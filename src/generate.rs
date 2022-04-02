#![allow(dead_code, unused_imports)]

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::*;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
    UVPolynomial,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use std::ops::{Div, Mul, Neg};

/// Conversion from integer to finite field element
pub fn scalar(n: u64) -> Fr {
    Fr::from(n)
}

/// A struct that holds all the constants that
/// are needed for polynomial commitment and 
/// the domain used for polynomial interpolation.
pub struct Setup {
    g1_powers: Vec<G1Affine>,
    h: G2Affine,
    beta_h: G2Affine,
    domain: GeneralEvaluationDomain<Fr>,
}

/// Produces constants that are needed for polynomial
/// commitment protocol.  
/// Produces a "domain" which is used for polynomial
/// interpolation.
pub fn setup(vectors: &Vec<Fr>) -> Setup {
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

    Setup {
        g1_powers: kzg_setup,
        h: h.into_affine(),
        beta_h: beta_h.into_affine(),
        domain,
    }
}

/// Given a polynomial and the setup constants, computes
/// the KZG commitment to that polynomial.  This commitment
/// is encoded in a single elliptic curve point.
pub fn commit(p: &DensePolynomial<Fr>, setup: &Setup) -> G1Affine {
    let powers = &setup.g1_powers;
    p.coeffs()
        .iter()
        .zip(powers)
        .map(|(c, p)| p.into_projective().mul(c.into_repr()))
        .sum::<G1Projective>()
        .into_affine()
}

/// Given a vector of finite field elements, computes the
/// interpolation polynomial.  Recall this is the polynomial
/// whose first n values are precisely the elements in the
/// values vector.
pub fn interpolate(values: &Vec<Fr>, setup: &Setup) -> DensePolynomial<Fr> {
    let domain = setup.domain;
    DensePolynomial::from_coefficients_vec(domain.ifft(values))
}

/// Evaluate polynomial at given point
pub fn evaluate(poly: &DensePolynomial<Fr>, eval: &Fr) -> Fr {
    poly.evaluate(eval)
}

/// Produces evidence of `poly` evaluation at `eval`
pub fn open(poly: &DensePolynomial<Fr>, eval: &Fr, setup: &Setup) -> G1Affine {
    // Compute witness poly
    let divisor = DensePolynomial::from_coefficients_vec(vec![eval.neg(), Fr::one()]);
    let value = DensePolynomial::from_coefficients_vec(vec![evaluate(poly, eval)]);
    let witness_poly = (poly.clone() + value.neg()).div(&divisor);

    // Compute opening
    commit(&witness_poly, setup)
}

/// Verification of a polynomial commitment and evaluation
pub fn verify(
    setup: &Setup,
    commitment: &G1Affine,
    eval: &Fr,
    value: &Fr,
    opening: &G1Affine,
) -> bool {
    let Setup {
        g1_powers,
        h,
        beta_h,
        domain: _,
    } = setup;
    let g1 = g1_powers[0];
    let inner = commitment.into_projective() - g1.mul(value.into_repr());
    let lhs = Bls12_381::pairing(inner, *h);

    let inner = beta_h.into_projective() - h.mul(eval.into_repr());
    let rhs = Bls12_381::pairing(*opening, inner);

    lhs == rhs
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use std::ops::Div;

    #[test]
    fn commitment_success() {
        let mut rng = rand::thread_rng();
        let a = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8)];
        let setup = setup(&a);
        let poly = interpolate(&a, &setup);
        let commitment = commit(&poly, &setup);
        let eval = Fr::rand(&mut rng);
        let value = evaluate(&poly, &eval);
        let opening = open(&poly, &eval, &setup);

        assert!(verify(&setup, &commitment, &eval, &value, &opening));
    }

    pub struct Proof {
        comm_a: G1Affine,
        comm_b: G1Affine,
        comm_c: G1Affine,
        comm_q: G1Affine,
        eval_a: Fr,
        eval_b: Fr,
        eval_c: Fr,
        eval_q: Fr,
        open_a: G1Affine,
        open_b: G1Affine,
        open_c: G1Affine,
        open_q: G1Affine,
    }

    pub fn make_proof(a: Vec<Fr>, b: Vec<Fr>, c: Vec<Fr>, setup: &Setup) -> Proof {
        let poly_a = interpolate(&a, setup);
        let poly_b = interpolate(&b, setup);
        let poly_c = interpolate(&c, setup);
        let (poly_q, _) = (poly_a.naive_mul(&poly_b) + poly_c.clone().neg())
            .divide_by_vanishing_poly(setup.domain)
            .unwrap();

        let comm_a = commit(&poly_a, setup);
        let comm_b = commit(&poly_b, setup);
        let comm_c = commit(&poly_c, setup);
        let comm_q = commit(&poly_q, setup);

        // world's worst Fiat-Shamir lol
        let eval_point = Fr::from(1000u32);

        let eval_a = evaluate(&poly_a, &eval_point);
        let eval_b = evaluate(&poly_b, &eval_point);
        let eval_c = evaluate(&poly_c, &eval_point);
        let eval_q = evaluate(&poly_q, &eval_point);

        let open_a = open(&poly_a, &eval_point, setup);
        let open_b = open(&poly_b, &eval_point, setup);
        let open_c = open(&poly_c, &eval_point, setup);
        let open_q = open(&poly_q, &eval_point, setup);

        Proof {
            comm_a,
            comm_b,
            comm_c,
            comm_q,
            eval_a,
            eval_b,
            eval_c,
            eval_q,
            open_a,
            open_b,
            open_c,
            open_q,
        }
    }

    pub fn check_proof(proof: &Proof, setup: &Setup, eval_point: Fr) -> bool {
        let eval_z = setup.domain.evaluate_vanishing_polynomial(eval_point);
        verify(
            setup,
            &proof.comm_a,
            &eval_point,
            &proof.eval_a,
            &proof.open_a,
        ) && verify(
            setup,
            &proof.comm_b,
            &eval_point,
            &proof.eval_b,
            &proof.open_b,
        ) && verify(
            setup,
            &proof.comm_c,
            &eval_point,
            &proof.eval_c,
            &proof.open_c,
        ) && verify(
            setup,
            &proof.comm_q,
            &eval_point,
            &proof.eval_q,
            &proof.open_q,
        ) && (proof.eval_a * proof.eval_b - proof.eval_c == proof.eval_q * eval_z)
    }

    #[test]
    fn success_test() {
        let a = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8)];
        let b = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8)];
        let c = vec![Fr::from(1u8), Fr::from(4u8), Fr::from(9u8)];
        let setup = setup(&a);

        let proof = make_proof(a, b, c, &setup);
        // world's worst Fiat-Shamir lol
        let eval_point = Fr::from(1000u32);
        assert!(check_proof(&proof, &setup, eval_point))
    }

    #[test]
    fn failure_test() {
        let a = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8)];
        let b = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8)];
        let c = vec![Fr::from(1u8), Fr::from(4u8), Fr::from(10u8)];
        let setup = setup(&a);

        let proof = make_proof(a, b, c, &setup);
        // world's worst Fiat-Shamir lol
        let eval_point = Fr::from(1000u32);
        assert!(!check_proof(&proof, &setup, eval_point))
    }

    // #[test]
    // fn abc_test() {
    //     let mut rng = rand::thread_rng();
    //     let a = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8)];
    //     let b = vec![Fr::from(1u8), Fr::from(2u8), Fr::from(3u8)];
    //     let c = vec![Fr::from(1u8), Fr::from(4u8), Fr::from(9u8)];
    //     let setup = setup(&a);

    //     let poly_a = interpolate(&a, &setup);
    //     let poly_b = interpolate(&b, &setup);
    //     let poly_c = interpolate(&c, &setup);
    //     let (poly_q, _) = (poly_a.naive_mul(&poly_b) + poly_c.clone().neg())
    //         .divide_by_vanishing_poly(setup.domain)
    //         .unwrap();

    //     let comm_a = commit(&poly_a, &setup);
    //     let comm_b = commit(&poly_b, &setup);
    //     let comm_c = commit(&poly_c, &setup);
    //     let comm_q = commit(&poly_q, &setup);

    //     let eval_point = Fr::rand(&mut rng);

    //     let eval_a = evaluate(&poly_a, &eval_point);
    //     let eval_b = evaluate(&poly_b, &eval_point);
    //     let eval_c = evaluate(&poly_c, &eval_point);
    //     let eval_q = evaluate(&poly_q, &eval_point);

    //     let open_a = open(&poly_a, &eval_point, &setup);
    //     let open_b = open(&poly_b, &eval_point, &setup);
    //     let open_c = open(&poly_c, &eval_point, &setup);
    //     let open_q = open(&poly_q, &eval_point, &setup);

    //     let proof = Proof {
    //         comm_a,
    //         comm_b,
    //         comm_c,
    //         comm_q,
    //         eval_a,
    //         eval_b,
    //         eval_c,
    //         eval_q,
    //         open_a,
    //         open_b,
    //         open_c,
    //         open_q,
    //     };
    //     assert!(check_proof(&proof, &setup, eval_point))
    // }
}
