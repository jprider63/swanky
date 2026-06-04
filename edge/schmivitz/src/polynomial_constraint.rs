//! Polynomial constraint verification protocol.
//!
//! This module implements the batch verification protocol for polynomial commitments
//! in a VOLE-based zero-knowledge proof system.
//!
//! The protocol operates on commitment polynomials of varying degrees and verifies
//! them as a batch using random challenges and VOLE masking.

use swanky_error::{ErrorKind, Result, bail};
use swanky_field::FiniteRing;
use swanky_field_binary::F128b;
use crate::commitment_polynomial::CommitmentPolynomial;

/// Full-field VOLE correlation in F128b.
///
/// Constructed by composing `r` base F2 VOLEs into a single correlation over F_{p^r}.
/// The prover holds `(value, mask)` and the verifier holds `(delta, tag)`,
/// satisfying the relation: tag = value * delta + mask, all in F128b.
pub struct FullFieldVole {
    /// The prover's random value u ∈ F128b, composed from r base-field VOLE values.
    pub value: F128b,
    /// The prover's mask w ∈ F128b, composed from r base-field VOLE masks.
    pub mask: F128b,
}

/// Verifier's side of a full-field VOLE correlation.
///
/// Constructed by composing `r` base F2 VOLEs into a single correlation over F_{p^r}.
pub struct FullFieldVoleVerifier {
    /// The verifier's tag v = u * Δ + w ∈ F128b.
    pub tag: F128b,
}

/// Result of batch verification on the prover side.
///
/// Contains the combined polynomial π(t) whose coefficients (except the last)
/// are sent to the verifier.
pub struct BatchProverResult {
    /// Coefficients of π(t), excluding the degree-d coefficient (which is public).
    pub coefficients: Vec<F128b>,
    /// The degree-d coefficient (sum of ξ^i * x_i), computable by both parties.
    pub top_coefficient: F128b,
}

/// Perform batch verification from the prover's side.
///
/// Given `m` commitment polynomials of various degrees:
/// 1. Aligns each polynomial to the maximum degree d by multiplying by t^(d - d_i).
/// 2. Scales each by the challenge power ξ^i.
/// 3. Sums all aligned, scaled polynomials.
/// 4. Adds masking VOLEs: t^(j-1) * σ_j(t) for j ∈ [1, d-1].
/// 5. Returns the combined polynomial π(t).
///
/// The caller is responsible for:
/// - Generating the challenge ξ via Fiat-Shamir.
/// - Providing d-1 full-field VOLE correlations as masks.
/// - Sending the resulting coefficients to the verifier.
pub fn batch_prove(
    commitments: &[CommitmentPolynomial<F128b, F128b>],
    xi: F128b,
    mask_voles: &[FullFieldVole],
) -> Result<BatchProverResult> {
    if commitments.is_empty() {
        bail!(
            ErrorKind::OtherError,
            "batch_prove requires at least one commitment polynomial"
        );
    }

    let max_degree = commitments.iter().map(|c| c.degree()).max().unwrap();

    if max_degree == 0 {
        bail!(
            ErrorKind::OtherError,
            "batch_prove: all polynomials have degree 0, nothing to verify"
        );
    }

    let required_masks = max_degree - 1;
    if mask_voles.len() != required_masks {
        bail!(
            ErrorKind::OtherError,
            "batch_prove: expected {} mask VOLEs, got {}",
            required_masks,
            mask_voles.len()
        );
    }

    // Build π(t) of degree max_degree
    let pi_len = max_degree + 1;
    let mut pi_coeffs = vec![F128b::ZERO; pi_len];

    // Accumulate ξ^i * t^(d - d_i) * ρ_i(t) for each commitment
    let mut xi_power = F128b::ONE;
    for commitment in commitments {
        let d_i = commitment.degree();
        let shift = max_degree - d_i;
        for (k, coeff) in commitment.lower_coefficients().iter().enumerate() {
            pi_coeffs[k + shift] = pi_coeffs[k + shift] + xi_power * *coeff;
        }
        pi_coeffs[d_i + shift] =
            pi_coeffs[d_i + shift] + xi_power * commitment.highest_degree();
        xi_power *= xi;
    }

    // Add masks: t^(j-1) * σ_j(t) for j ∈ [1, d-1]
    // σ_j(t) = w_j + u_j * t, so t^(j-1) * σ_j(t) = w_j * t^(j-1) + u_j * t^j
    for (j_minus_1, vole) in mask_voles.iter().enumerate() {
        // j = j_minus_1 + 1, so t^(j-1) = t^j_minus_1
        pi_coeffs[j_minus_1] = pi_coeffs[j_minus_1] + vole.mask;
        pi_coeffs[j_minus_1 + 1] = pi_coeffs[j_minus_1 + 1] + vole.value;
    }

    let top_coefficient = pi_coeffs[max_degree];

    Ok(BatchProverResult {
        coefficients: pi_coeffs[..max_degree].to_vec(),
        top_coefficient,
    })
}

/// Perform batch verification from the verifier's side.
///
/// Given:
/// - `gamma_values`: the verifier's evaluations γ_i = ρ_i(Δ) for each commitment
/// - `degrees`: the degree d_i of each commitment polynomial
/// - `delta`: the verifier's global VOLE key Δ
/// - `xi`: the Fiat-Shamir challenge
/// - `mask_vole_tags`: the verifier's VOLE tags v_j for the mask VOLEs
/// - `prover_coefficients`: the coefficients [π_0, ..., π_{d-2}] sent by the prover
/// - `top_coefficient`: the publicly computable degree-d coefficient
///
/// Returns Ok(()) if the verification succeeds, or an error if it fails.
pub fn batch_verify(
    gamma_values: &[F128b],
    degrees: &[usize],
    delta: F128b,
    xi: F128b,
    mask_vole_tags: &[FullFieldVoleVerifier],
    prover_coefficients: &[F128b],
    top_coefficient: F128b,
) -> Result<()> {
    if gamma_values.len() != degrees.len() {
        bail!(
            ErrorKind::OtherError,
            "batch_verify: gamma_values and degrees must have the same length"
        );
    }

    if gamma_values.is_empty() {
        bail!(
            ErrorKind::OtherError,
            "batch_verify requires at least one commitment"
        );
    }

    let max_degree = *degrees.iter().max().unwrap();

    if max_degree == 0 {
        bail!(
            ErrorKind::OtherError,
            "batch_verify: all polynomials have degree 0"
        );
    }

    let required_masks = max_degree - 1;
    if mask_vole_tags.len() != required_masks {
        bail!(
            ErrorKind::OtherError,
            "batch_verify: expected {} mask VOLE tags, got {}",
            required_masks,
            mask_vole_tags.len()
        );
    }

    if prover_coefficients.len() != max_degree {
        bail!(
            ErrorKind::OtherError,
            "batch_verify: expected {} prover coefficients, got {}",
            max_degree,
            prover_coefficients.len()
        );
    }

    // Compute the verifier's expected evaluation of π(Δ)
    // = Σ_i ξ^i * Δ^(d - d_i) * γ_i + Σ_{j=1}^{d-1} Δ^{j-1} * v_j
    let mut expected = F128b::ZERO;

    let mut xi_power = F128b::ONE;
    for (gamma, &d_i) in gamma_values.iter().zip(degrees.iter()) {
        let shift = max_degree - d_i;
        let delta_shift = power(delta, shift);
        expected = expected + xi_power * delta_shift * *gamma;
        xi_power *= xi;
    }

    // Add mask VOLE tags: Δ^{j-1} * v_j
    let mut delta_power = F128b::ONE;
    for vole_tag in mask_vole_tags {
        expected = expected - delta_power * vole_tag.tag;
        delta_power *= delta;
    }

    // Evaluate π(Δ) from the received coefficients
    // π(Δ) = Σ_{k=0}^{d-2} π_k * Δ^k + top_coefficient * Δ^d
    let mut pi_at_delta = F128b::ZERO;
    let mut delta_power = F128b::ONE;
    for coeff in prover_coefficients {
        pi_at_delta = pi_at_delta - *coeff * delta_power;
        delta_power *= delta;
    }
    // delta_power is now Δ^(d-1) after the loop over d-1 coefficients... wait, we have
    // max_degree coefficients (indices 0..max_degree-1), so delta_power = Δ^max_degree
    // Actually, prover_coefficients has max_degree elements (indices 0..max_degree-1),
    // so after the loop delta_power = Δ^max_degree. That's correct for the top term.
    pi_at_delta = pi_at_delta + top_coefficient * delta_power;

    if expected != pi_at_delta {
        bail!(
            ErrorKind::OtherError,
            "Batch verification failed: π(Δ) does not match expected value"
        );
    }

    Ok(())
}

/// Compute base^exp in a finite field using repeated squaring.
fn power(base: F128b, exp: usize) -> F128b {
    if exp == 0 {
        return F128b::ONE;
    }
    let mut result = F128b::ONE;
    let mut b = base;
    let mut e = exp;
    while e > 0 {
        if e & 1 == 1 {
            result = result * b;
        }
        b = b * b;
        e >>= 1;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, thread_rng};
    use swanky_field::FiniteRing;

    fn random_f128b(rng: &mut impl Rng) -> F128b {
        F128b::random(rng)
    }

    /// Create a base VOLE triple: prover gets (u, w), verifier gets (delta, v = u*delta + w)
    fn make_vole(rng: &mut impl Rng, delta: F128b) -> (FullFieldVole, FullFieldVoleVerifier) {
        let u = random_f128b(rng);
        let w = random_f128b(rng);
        let v = u * delta + w;
        (
            FullFieldVole { value: u, mask: w },
            FullFieldVoleVerifier { tag: v },
        )
    }

    /// Create a commitment polynomial from a base VOLE for a value x.
    /// Prover: ρ(t) = w + x·t
    /// Verifier: γ = ρ(Δ) = w + x·Δ
    fn make_commitment(
        rng: &mut impl Rng,
        delta: F128b,
        value: F128b,
    ) -> (CommitmentPolynomial<F128b, F128b>, F128b) {
        let w = random_f128b(rng);
        let poly = CommitmentPolynomial::<F128b, F128b>::from_base_vole(value, w);
        let gamma = poly.evaluate_at_point(delta);
        (poly, gamma)
    }

    #[test]
    fn test_commitment_polynomial_basic() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);
        let x = random_f128b(rng);
        let w = random_f128b(rng);

        let poly = CommitmentPolynomial::<F128b, F128b>::from_base_vole(x, w);
        assert_eq!(poly.degree(), 1);
        assert_eq!(poly.lower_coefficients(), &[w]);
        assert_eq!(poly.highest_degree(), x);
        assert_eq!(poly.evaluate_at_point(delta), w + x * delta);
    }

    #[test]
    fn test_addc() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);
        let x = random_f128b(rng);
        let c = random_f128b(rng);
        let w = random_f128b(rng);

        let poly_x = CommitmentPolynomial::<F128b, F128b>::from_base_vole(x, w);
        let gamma_x = poly_x.evaluate_at_point(delta);

        let poly_sum = poly_x.addc(c);
        let gamma_sum = poly_sum.evaluate_at_point(delta);

        // Verifier: γ = γ_x + c·Δ^d
        let d = poly_x.degree();
        let expected_gamma = gamma_x + c * power(delta, d);
        assert_eq!(gamma_sum, expected_gamma);
    }

    #[test]
    fn test_add_same_degree() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);

        let val_x = random_f128b(rng);
        let val_y = random_f128b(rng);
        let (poly_x, gamma_x) = make_commitment(rng, delta, val_x);
        let (poly_y, gamma_y) = make_commitment(rng, delta, val_y);

        let poly_sum = poly_x.add(&poly_y);
        let gamma_sum = poly_sum.evaluate_at_point(delta);

        // Both degree 1, d = 1, shifts are 0
        assert_eq!(gamma_sum, gamma_x + gamma_y);
    }

    #[test]
    fn test_add_different_degree() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);

        // Create a degree-1 polynomial
        let val_x = random_f128b(rng);
        let (poly_x, gamma_x) = make_commitment(rng, delta, val_x);
        // Create a degree-2 polynomial by multiplying two degree-1 polynomials
        let val_a = random_f128b(rng);
        let val_b = random_f128b(rng);
        let (poly_a, gamma_a) = make_commitment(rng, delta, val_a);
        let (poly_b, gamma_b) = make_commitment(rng, delta, val_b);
        let poly_y = poly_a.mul(&poly_b);
        let gamma_y = gamma_a * gamma_b;

        assert_eq!(poly_x.degree(), 1);
        assert_eq!(poly_y.degree(), 2);

        let poly_sum = poly_x.add(&poly_y);
        let gamma_sum = poly_sum.evaluate_at_point(delta);

        // d = max(1, 2) = 2, shift1 = 1, shift2 = 0
        // Verifier: γ = Δ^1·γ_x + Δ^0·γ_y
        let expected = delta * gamma_x + gamma_y;
        assert_eq!(gamma_sum, expected);
    }

    #[test]
    fn test_mulc() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);
        let c = random_f128b(rng);

        let val_x = random_f128b(rng);
        let (poly_x, gamma_x) = make_commitment(rng, delta, val_x);

        let poly_prod = poly_x.mulc(c);
        let gamma_prod = poly_prod.evaluate_at_point(delta);

        // Verifier: γ = c·γ_x
        assert_eq!(gamma_prod, c * gamma_x);
    }

    #[test]
    fn test_mul() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);

        let val_x = random_f128b(rng);
        let val_y = random_f128b(rng);
        let (poly_x, gamma_x) = make_commitment(rng, delta, val_x);
        let (poly_y, gamma_y) = make_commitment(rng, delta, val_y);

        let poly_prod = poly_x.mul(&poly_y);
        let gamma_prod = poly_prod.evaluate_at_point(delta);

        // Verifier: γ = γ_x·γ_y
        assert_eq!(gamma_prod, gamma_x * gamma_y);
        assert_eq!(poly_prod.degree(), 2);
    }

    #[test]
    fn test_batch_verification_single_degree1() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);
        let xi = random_f128b(rng);

        let val = random_f128b(rng);
        let (poly, gamma) = make_commitment(rng, delta, val);

        // max_degree = 1, need 0 mask VOLEs
        let result = batch_prove(&[poly], xi, &[]).unwrap();

        // 1 coefficient below the top (the constant term)
        assert_eq!(result.coefficients.len(), 1);

        batch_verify(
            &[gamma],
            &[1],
            delta,
            xi,
            &[],
            &result.coefficients,
            result.top_coefficient,
        )
        .unwrap();
    }

    #[test]
    fn test_batch_verification_degree2() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);
        let xi = random_f128b(rng);

        // Create two degree-1 commitments and their product (degree 2)
        let val_a = random_f128b(rng);
        let val_b = random_f128b(rng);
        let (poly_a, gamma_a) = make_commitment(rng, delta, val_a);
        let (poly_b, gamma_b) = make_commitment(rng, delta, val_b);
        let poly_c = poly_a.mul(&poly_b);
        let gamma_c = gamma_a * gamma_b;

        // Verify a batch of [poly_a(deg 1), poly_b(deg 1), poly_c(deg 2)]
        let commitments = vec![poly_a, poly_b, poly_c];
        let gammas = vec![gamma_a, gamma_b, gamma_c];
        let degrees = vec![1, 1, 2];

        // max_degree = 2, need 1 mask VOLE
        let (mask_prover, mask_verifier) = make_vole(rng, delta);
        let result = batch_prove(&commitments, xi, &[mask_prover]).unwrap();

        batch_verify(
            &gammas,
            &degrees,
            delta,
            xi,
            &[mask_verifier],
            &result.coefficients,
            result.top_coefficient,
        )
        .unwrap();
    }

    #[test]
    fn test_batch_verification_mixed_degrees() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);
        let xi = random_f128b(rng);

        // Build commitments of varying degrees
        let val1 = random_f128b(rng);
        let val2 = random_f128b(rng);
        let (poly1, gamma1) = make_commitment(rng, delta, val1); // deg 1
        let (poly2, gamma2) = make_commitment(rng, delta, val2); // deg 1
        let poly3 = poly1.mul(&poly2); // deg 2
        let gamma3 = gamma1 * gamma2;
        let val4 = random_f128b(rng);
        let (poly4, gamma4) = make_commitment(rng, delta, val4); // deg 1
        let poly5 = poly3.mul(&poly4); // deg 3
        let gamma5 = gamma3 * gamma4;

        let commitments = vec![poly1, poly3, poly5];
        let gammas = vec![gamma1, gamma3, gamma5];
        let degrees = vec![1, 2, 3];

        // max_degree = 3, need 2 mask VOLEs
        let (mask_p1, mask_v1) = make_vole(rng, delta);
        let (mask_p2, mask_v2) = make_vole(rng, delta);
        let result = batch_prove(&commitments, xi, &[mask_p1, mask_p2]).unwrap();

        batch_verify(
            &gammas,
            &degrees,
            delta,
            xi,
            &[mask_v1, mask_v2],
            &result.coefficients,
            result.top_coefficient,
        )
        .unwrap();
    }

    #[test]
    fn test_batch_verification_fails_with_wrong_coefficients() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);
        let xi = random_f128b(rng);

        let val_a = random_f128b(rng);
        let val_b = random_f128b(rng);
        let (poly_a, gamma_a) = make_commitment(rng, delta, val_a);
        let (poly_b, gamma_b) = make_commitment(rng, delta, val_b);
        let poly_c = poly_a.mul(&poly_b);
        let gamma_c = gamma_a * gamma_b;

        let commitments = vec![poly_a, poly_b, poly_c];
        let gammas = vec![gamma_a, gamma_b, gamma_c];
        let degrees = vec![1, 1, 2];

        let (mask_prover, mask_verifier) = make_vole(rng, delta);
        let mut result = batch_prove(&commitments, xi, &[mask_prover]).unwrap();

        // Tamper with a coefficient
        if !result.coefficients.is_empty() {
            result.coefficients[0] = result.coefficients[0] + F128b::ONE;
        }

        assert!(
            batch_verify(
                &gammas,
                &degrees,
                delta,
                xi,
                &[mask_verifier],
                &result.coefficients,
                result.top_coefficient,
            )
            .is_err()
        );
    }

    #[test]
    fn test_batch_verification_fails_with_wrong_gamma() {
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);
        let xi = random_f128b(rng);

        let val_a = random_f128b(rng);
        let val_b = random_f128b(rng);
        let (poly_a, gamma_a) = make_commitment(rng, delta, val_a);
        let (poly_b, _gamma_b) = make_commitment(rng, delta, val_b);
        let poly_c = poly_a.mul(&poly_b);

        let commitments = vec![poly_a, poly_b, poly_c];
        // Use a wrong gamma for the second commitment
        let wrong_gamma = random_f128b(rng);
        let fake_gamma = random_f128b(rng);
        let gammas = vec![gamma_a, wrong_gamma, fake_gamma];
        let degrees = vec![1, 1, 2];

        let (mask_prover, mask_verifier) = make_vole(rng, delta);
        let result = batch_prove(&commitments, xi, &[mask_prover]).unwrap();

        assert!(
            batch_verify(
                &gammas,
                &degrees,
                delta,
                xi,
                &[mask_verifier],
                &result.coefficients,
                result.top_coefficient,
            )
            .is_err()
        );
    }

    #[test]
    fn test_circuit_like_polynomial_tracking() {
        // Simulate a simple circuit: x0, x1 private inputs, x2 = x0 * x1, x3 = x2 + x0
        let rng = &mut thread_rng();
        let delta = random_f128b(rng);

        let x0 = random_f128b(rng);
        let x1 = random_f128b(rng);

        // Input gates: degree-1 commitments from base VOLEs
        let (poly_x0, gamma_x0) = make_commitment(rng, delta, x0);
        let (poly_x1, gamma_x1) = make_commitment(rng, delta, x1);

        // Mul gate: x2 = x0 * x1
        let poly_x2 = poly_x0.mul(&poly_x1);
        let gamma_x2 = gamma_x0 * gamma_x1;

        // Add gate: x3 = x2 + x0 (degree alignment)
        let poly_x3 = poly_x2.add(&poly_x0);
        let gamma_x3 = gamma_x2 + delta * gamma_x0; // shift x0 by Δ^(2-1)

        // Verify the polynomial evaluation matches
        assert_eq!(poly_x3.evaluate_at_point(delta), gamma_x3);
    }
}
