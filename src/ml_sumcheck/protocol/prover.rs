//! Prover
use crate::ml_sumcheck::data_structures::ListOfProductsOfPolynomials;
use crate::ml_sumcheck::protocol::verifier::VerifierMsg;
use crate::ml_sumcheck::protocol::IPForMLSumcheck;
use ark_ff::Field;
use ark_poly::{DenseMultilinearExtension, MultilinearExtension, univariate::DensePolynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{cfg_iter_mut, vec::Vec};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Prover Message
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverMsg<F: Field> {
    /// evaluations on P(0), P(1), P(2), ...
    pub(crate) evaluations: Vec<F>,
}
/// Prover State
pub struct ProverState<F: Field> {
    /// sampled randomness given by the verifier
    pub randomness: Vec<F>,
    /// Stores the list of products that is meant to be added together. Each multiplicand is represented by
    /// the index in flattened_ml_extensions
    pub list_of_products: Vec<(F, Vec<usize>)>,
    /// Stores a list of multilinear extensions in which `self.list_of_products` points to
    pub flattened_ml_extensions: Vec<DenseMultilinearExtension<F>>,
    /// Number of variables
    pub num_vars: usize,
    /// Max number of multiplicands in a product
    pub max_multiplicands: usize,
    /// The current round number
    pub round: usize,
}
/// Prover State for ZK sumcheck
pub struct ZKProverState<F: Field>{
    /// Non-ZK Prover State
    pub prover_state: ProverState<F>,
    /// Masking polynomials from Libra (2019-317)
    pub mask_polynomials: Vec<DensePolynomial<F>>,
    /// ZK challenge
    pub challenge: F,
    /// Partial sum from front
    pub front_partial_sum: F,
    /// Partial sum from end
    pub tail_partial_sum: Vec<F>
}

impl<F: Field> IPForMLSumcheck<F> {
    /// initialize the prover to argue for the sum of polynomial over {0,1}^`num_vars`
    ///
    /// The polynomial is represented by a list of products of polynomials along with its coefficient that is meant to be added together.
    ///
    /// This data structure of the polynomial is a list of list of `(coefficient, DenseMultilinearExtension)`.
    /// * Number of products n = `polynomial.products.len()`,
    /// * Number of multiplicands of ith product m_i = `polynomial.products[i].1.len()`,
    /// * Coefficient of ith product c_i = `polynomial.products[i].0`
    ///
    /// The resulting polynomial is
    ///
    /// $$\sum_{i=0}^{n}C_i\cdot\prod_{j=0}^{m_i}P_{ij}$$
    ///
    pub fn prover_init(polynomial: &ListOfProductsOfPolynomials<F>) -> ProverState<F> {
        if polynomial.num_variables == 0 {
            panic!("Attempt to prove a constant.")
        }

        // create a deep copy of all unique MLExtensions
        let flattened_ml_extensions = polynomial
            .flattened_ml_extensions
            .iter()
            .map(|x| x.as_ref().clone())
            .collect();
        ProverState {
            randomness: Vec::with_capacity(polynomial.num_variables),
            list_of_products: polynomial.products.clone(),
            flattened_ml_extensions,
            num_vars: polynomial.num_variables,
            max_multiplicands: polynomial.max_multiplicands,
            round: 0,
        }
    }
    /// zero-knowledge of prover_init
    pub fn prover_init_zk(polynomial: &ListOfProductsOfPolynomials<F>, mask_polynomials: &Vec<DensePolynomial<F>>, challenge: F) -> ZKProverState<F> {
        
        
        let mut partial_sum: Vec<F> = Vec::new();
        let mut sum = F::zero();
        for (count, mask_poly) in mask_polynomials.iter().rev().enumerate(){
            sum += mask_poly[0] + mask_poly[0];
            for i in 1..polynomial.max_multiplicands + 1{
                sum += mask_poly[i];
            }
            partial_sum.push(sum * F::from(1u128 << count));
        }
        partial_sum.reverse();
        partial_sum.push(F::zero());
        ZKProverState {
            prover_state: Self::prover_init(polynomial),
            mask_polynomials: mask_polynomials.clone(),
            challenge,
            front_partial_sum: F::zero(),
            tail_partial_sum: partial_sum
        }
    }

    /// receive message from verifier, generate prover message, and proceed to next round
    ///
    /// Main algorithm used is from section 3.2 of [XZZPS19](https://eprint.iacr.org/2019/317.pdf#subsection.3.2).
    pub fn prove_round(
        prover_state: &mut ProverState<F>,
        v_msg: &Option<VerifierMsg<F>>,
    ) -> ProverMsg<F> {
        if let Some(msg) = v_msg {
            if prover_state.round == 0 {
                panic!("first round should be prover first.");
            }
            prover_state.randomness.push(msg.randomness);

            // fix argument
            let i = prover_state.round;
            let r = prover_state.randomness[i - 1];
            cfg_iter_mut!(prover_state.flattened_ml_extensions).for_each(|multiplicand| {
                *multiplicand = multiplicand.fix_variables(&[r]);
            });
        } else if prover_state.round > 0 {
            panic!("verifier message is empty");
        }

        prover_state.round += 1;

        if prover_state.round > prover_state.num_vars {
            panic!("Prover is not active");
        }

        let i = prover_state.round;
        let nv = prover_state.num_vars;
        let degree = prover_state.max_multiplicands; // the degree of univariate polynomial sent by prover at this round

        #[cfg(not(feature = "parallel"))]
        let zeros = (vec![F::zero(); degree + 1], vec![F::zero(); degree + 1]);
        #[cfg(feature = "parallel")]
        let zeros = || (vec![F::zero(); degree + 1], vec![F::zero(); degree + 1]);

        // generate sum
        let fold_result = ark_std::cfg_into_iter!(0..1 << (nv - i), 1 << 10).fold(
            zeros,
            |(mut products_sum, mut product), b| {
                // In effect, this fold is essentially doing simply:
                // for b in 0..1 << (nv - i) {
                for (coefficient, products) in &prover_state.list_of_products {
                    product.fill(*coefficient);
                    for &jth_product in products {
                        let table = &prover_state.flattened_ml_extensions[jth_product];
                        let mut start = table[b << 1];
                        let step = table[(b << 1) + 1] - start;
                        for p in product.iter_mut() {
                            *p *= start;
                            start += step;
                        }
                    }
                    for t in 0..degree + 1 {
                        products_sum[t] += product[t];
                    }
                }
                (products_sum, product)
            },
        );

        #[cfg(not(feature = "parallel"))]
        let products_sum = fold_result.0;

        // When rayon is used, the `fold` operation results in a iterator of `Vec<F>` rather than a single `Vec<F>`. In this case, we simply need to sum them.
        #[cfg(feature = "parallel")]
        let products_sum = fold_result.map(|scratch| scratch.0).reduce(
            || vec![F::zero(); degree + 1],
            |mut overall_products_sum, sublist_sum| {
                overall_products_sum
                    .iter_mut()
                    .zip(sublist_sum.iter())
                    .for_each(|(f, s)| *f += s);
                overall_products_sum
            },
        );

        ProverMsg {
            evaluations: products_sum,
        }
    }

    /// get evaluation of univariate polynomial on specific point 
    pub fn get_mask_evaluation(mask_polynomial: &DensePolynomial<F>, point: F) -> F{
        let mut evaluation = F::zero();
        for coef in mask_polynomial.iter().rev(){
            evaluation *= point;
            evaluation += coef;
        }    
        evaluation
    }

     /// get evaluation of multivariate polynomial formed by univariate polynomials on specific point 
    pub fn get_masks_evaluation(mask_polynomials: &Vec<DensePolynomial<F>>, points: &Vec<F>) -> F{
        let mut sum = F::zero();
        for (poly, point) in mask_polynomials.iter().zip(points){
            sum += Self::get_mask_evaluation(poly, *point);
        }
        sum
    }
    /// ZK prove round
    pub fn prove_round_zk( 
        prover_state_zk: &mut ZKProverState<F>,
        v_msg: &Option<VerifierMsg<F>>) -> ProverMsg<F>{
        let message = Self::prove_round(&mut prover_state_zk.prover_state, v_msg);// prover_state round += 1
        let i = prover_state_zk.prover_state.round;
        let nv = prover_state_zk.prover_state.num_vars;
        let deg = prover_state_zk.prover_state.max_multiplicands;
        let challenge = prover_state_zk.challenge;
        let mut sum = vec![F::zero(); deg + 1];
        if let Some(msg) = v_msg{
            prover_state_zk.front_partial_sum += Self::get_mask_evaluation(&prover_state_zk.mask_polynomials[i - 2], msg.randomness);
        }
        for j in 0..deg + 1{
            sum[j] = Self::get_mask_evaluation(&prover_state_zk.mask_polynomials[i - 1], F::from(j as u64)) + prover_state_zk.front_partial_sum;
            sum[j] *= F::from(1u128 << (nv - i));
            sum[j] += prover_state_zk.tail_partial_sum[i];
            sum[j] *= challenge;
        }
        
        ProverMsg{
            evaluations: message.evaluations.iter().zip(sum.iter()).map(|(msg, sum)| *msg + sum).collect()
        }
    }
}
