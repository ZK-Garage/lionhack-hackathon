#![allow(dead_code, unused_imports)]

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::*;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
    UVPolynomial,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use std::ops::{Mul, Neg, Div};

/// Conversion from integer to finite field element
pub fn scalar(n: u64) -> Fr {
    Fr::from(n)
}

/// Produces constants that are needed for polynomial
/// commitment protocol.  
/// Produces a "domain" which is used for polynomial
/// interpolation.
pub fn setup(
    vectors: &Vec<Fr>,
) -> (
    Vec<G1Affine>,
    G2Affine,
    G2Affine,
    GeneralEvaluationDomain<Fr>,
) {
    let domain: GeneralEvaluationDomain<Fr> =
        GeneralEvaluationDomain::new(vectors.len() + 2).unwrap();

    let mut rng = rand::thread_rng();
    let secret_scalar = Fr::rand(&mut rng);
    let secret_powers: Vec<Fr> = (0..domain.size() as u64)
        .map(|p| secret_scalar.pow(&[p, 0, 0, 0]))
        .collect();
    let generator = G1Projective::prime_subgroup_generator();
    let h = G2Projective::prime_subgroup_generator();
    let beta_h = h.mul(secret_scalar.into_repr());
    let kzg_setup: Vec<G1Affine> = secret_powers
        .iter()
        .map(|s| (generator.mul(s.into_repr())).into_affine())
        .collect();

    (kzg_setup, h.into_affine(), beta_h.into_affine(), domain)
}

/// Given a polynomial and the setup constants, computes
/// the KZG commitment to that polynomial.  This commitment
/// is encoded in a single elliptic curve point.
pub fn commit(p: &DensePolynomial<Fr>, setup: &Vec<G1Affine>) -> G1Affine {
    p.coeffs()
        .iter()
        .zip(setup)
        .map(|(c, p)| p.into_projective().mul(c.into_repr()))
        .sum::<G1Projective>()
        .into_affine()
}

/// Given a vector of finite field elements, computes the 
/// interpolation polynomial.  Recall this is the polynomial
/// whose first n values are precisely the elements in the 
/// values vector.
pub fn interpolate(
    values: &Vec<Fr>,
    domain: &GeneralEvaluationDomain<Fr>,
) -> DensePolynomial<Fr> {
    DensePolynomial::from_coefficients_vec(domain.ifft(values))
}

pub fn evaluate(poly: &DensePolynomial<Fr>, eval: &Fr) -> Fr {
    poly.evaluate(eval)
}

/// Produces evidence that `poly` evaluates to ?
pub fn open(poly: &DensePolynomial<Fr>, eval: &Fr, setup: &Vec<G1Affine>) -> G1Affine {
    // Compute witness poly
    let divisor = DensePolynomial::from_coefficients_vec(vec![eval.neg(), Fr::one()]);
    let witness_poly = poly / &divisor;

    // Compute opening
    commit(&witness_poly, setup)
}

/// Produces evidence of `poly` evaluation at `eval`
pub fn open_alternate(poly: &DensePolynomial<Fr>, eval: &Fr, setup: &Vec<G1Affine>) -> G1Affine {
    // Compute witness poly
    let divisor = DensePolynomial::from_coefficients_vec(vec![eval.neg(), Fr::one()]);
    let value = DensePolynomial::from_coefficients_vec(vec![evaluate(poly, eval)]);
    let witness_poly = (poly.clone() + value.neg()).div(&divisor);

    // Compute opening
    commit(&witness_poly, setup)
}

/// Verification part of polynomial commitment. 
/// Checks that `eval` is consistent with `commitment`,
/// which means that Prover was honest about evaluation.
pub fn verify(
    g1: &G1Affine,
    h: &G2Affine,
    beta_h: &G2Affine,
    commitment: &G1Affine,
    eval: &Fr,
    value: &Fr,
    opening: &G1Affine,
) -> bool {
    let inner = commitment.into_projective() - g1.mul(value.into_repr());
    let lhs = Bls12_381::pairing(inner, *h);

    let inner = beta_h.into_projective() - h.mul(eval.into_repr());
    let rhs = Bls12_381::pairing(*opening, inner);

    lhs == rhs
}

#[cfg(test)]
mod tests {
    use std::ops::Div;
    use super::*;
    use rand::Rng;

    #[test]
    fn commitment_success() {
        let mut rng = rand::thread_rng();
        let a = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8)];
        let (setup, h, beta_h, domain) = setup(&a);
        let poly = interpolate(&a, &domain);
        let commitment = commit(&poly, &setup);
        let eval = Fr::rand(&mut rng);
        let value = evaluate(&poly, &eval);
        let opening = open(&poly, &eval, &setup);
        let opening_alternate = open_alternate(&poly, &eval, &setup);

        assert!(verify(&setup[0], &h, &beta_h, &commitment, &eval, &value, &opening));
        assert!(verify(&setup[0], &h, &beta_h, &commitment, &eval, &value, &opening_alternate))
    }

    #[test]
    fn test_the_thing() {
        let mut rng = rand::thread_rng();
        let num_vecs = 4;
        let mut vecs: Vec<Vec<Fr>> = vec![];
        for _ in 0..num_vecs {
            let acct_bytes: Vec<u8> = (0..32).into_iter().map(|_u| rng.gen::<u8>()).collect();
            vecs.push(acct_bytes.iter().map(|u| Fr::from(*u)).collect());
        }

        let (setup, h, beta_h, domain) = setup(&vecs[0]);
        let poly = interpolate(&vecs[0], &domain);

        let commitment = commit(&poly, &setup);
        let eval = Fr::rand(&mut rng);
        let value = evaluate(&poly, &eval);
        let opening = open(&poly, &eval, &setup);

        assert!(verify(
            &setup[0],
            &h,
            &beta_h,
            &commitment,
            &eval,
            &value,
            &opening
        ));
    }

    // #[test]
    // fn sumcheck() {
    //     let mut rng = rand::thread_rng();
    //     let num_vecs = 2;
    //     let mut vecs: Vec<Vec<Fr>> = vec![];
    //     for _ in 0..num_vecs {
    //         let acct_bytes: Vec<u8> = (0..32).into_iter().map(|_u| rng.gen::<u8>()).collect();
    //         vecs.push(acct_bytes.iter().map(|u| Fr::from(*u)).collect());
    //     }

    //     let a = vecs[0];
    //     let b = vecs[1];
    //     let c = a
    //         .iter()
    //         .zip(b.iter())
    //         .map(|(one, two)| *one * two)
    //         .collect::<Vec<Fr>>();

    //     // let domain: GeneralEvaluationDomain<Fr> =
    //     //     GeneralEvaluationDomain::new(num_vecs + 3).unwrap();
    //     let (setup, h, beta_h, domain) = setup(vec![a, b, c]);
    //     let poly_1 = interpolate(&a, &domain);
    //     let poly_2 = interpolate(&b, &domain);
    //     let poly_3 = interpolate(&c, &domain);

    //     let q = (poly_1.mul(&poly_2) + poly_3.neg()).divide_by_vanishing_poly(domain);
    // }
}

/*
fn generate_challenge() -> (Vec<G1Affine>, Vec<Vec<Fr>>, Fr, Fr, G1Affine, Fr, Fr) {
    use rand::Rng;
    let mut rng = rand::thread_rng();

    let number_of_accts = 1000usize;
    let accts = generate_accts(number_of_accts);
    let target_acct_index = rng.gen_range(0..number_of_accts);
    let target_acct = &accts[target_acct_index];

    let domain: GeneralEvaluationDomain<Fr> =
        GeneralEvaluationDomain::new(number_of_accts + 2).unwrap();
    let (setup, h, beta_h) = setup(domain.size());

    let target_acct_poly = DensePolynomial::from_coefficients_vec(domain.ifft(&target_acct));
    let blinding_poly =
        DensePolynomial::from_coefficients_vec(vec![Fr::rand(&mut rng), Fr::rand(&mut rng)]);
    let blinded_acct_poly = target_acct_poly + blinding_poly.mul_by_vanishing_poly(domain);

    let commitment: G1Affine = commit(&blinded_acct_poly, &setup);

    let challenge_1 = Fr::rand(&mut rng);
    let challenge_2 = Fr::rand(&mut rng);

    let opening_1 = blinded_acct_poly.evaluate(&challenge_1);
    let opening_2 = blinded_acct_poly.evaluate(&challenge_2);

    (
        setup,
        accts,
        challenge_1,
        challenge_2,
        commitment,
        opening_1,
        opening_2,
    )
}
*/
