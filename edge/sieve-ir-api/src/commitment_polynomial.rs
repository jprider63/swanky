//! Polynomial commitment type for VOLE-based zero-knowledge protocols.
//!
//! A [`CommitmentPolynomial`] represents the polynomial ρ_x(t) = ρ_0 + ρ_1·t + ··· + ρ_d·t^d
//! where ρ_d = x is the committed value (in the base field `F`) and
//! ρ_0, ..., ρ_{d-1} are random masking coefficients drawn from the extension field `FE`.
//!
//! Gate operations allow building commitment polynomials bottom-up through a circuit:
//! - [`CommitmentPolynomial::addc`]: add a constant
//! - [`CommitmentPolynomial::add`]: add two commitments (aligning degrees)
//! - [`CommitmentPolynomial::mulc`]: multiply by a constant
//! - [`CommitmentPolynomial::mul`]: multiply two commitments

use swanky_field::{FiniteField, IsSubFieldOf};

/// A polynomial commitment with leading coefficient in the base field `F`
/// and lower coefficients in the extension field `FE`.
///
/// Stores the polynomial ρ(t) = ρ_0 + ρ_1·t + ··· + ρ_d·t^d, where:
/// - `lower_coefficients` = [ρ_0, ρ_1, ..., ρ_{d-1}] (each in `FE`).
/// - `highest_degree` = ρ_d (the committed value, in `F`).
#[derive(Clone, Debug)]
pub struct CommitmentPolynomial<F: FiniteField, FE: FiniteField>
where
    F: IsSubFieldOf<FE>,
{
    lower_coefficients: Vec<FE>,
    highest_degree: F,
}

impl<F: FiniteField, FE: FiniteField> CommitmentPolynomial<F, FE>
where
    F: IsSubFieldOf<FE>,
{
    /// Create a commitment polynomial from a base VOLE.
    ///
    /// Given a value `x` in the base field and a VOLE mask `w` in the extension field,
    /// constructs ρ(t) = w + x·t (degree 1).
    pub fn from_base_vole(value: F, mask: FE) -> Self {
        Self {
            lower_coefficients: vec![mask],
            highest_degree: value,
        }
    }

    /// Create a commitment polynomial directly from its lower coefficients
    /// and the highest-degree coefficient.
    pub fn from_parts(lower_coefficients: Vec<FE>, highest_degree: F) -> Self {
        Self {
            lower_coefficients,
            highest_degree,
        }
    }

    /// Return the degree of the polynomial.
    pub fn degree(&self) -> usize {
        self.lower_coefficients.len()
    }

    /// Return the lower coefficients [ρ_0, ρ_1, ..., ρ_{d-1}].
    pub fn lower_coefficients(&self) -> &[FE] {
        &self.lower_coefficients
    }

    /// Return the highest-degree coefficient ρ_d (the committed value).
    pub fn highest_degree(&self) -> F {
        self.highest_degree
    }

    /// Evaluate the polynomial at a given point using Horner's method.
    ///
    /// This is useful for the verifier to evaluate at Δ (the global VOLE key).
    pub fn evaluate_at_point(&self, point: FE) -> FE {
        let mut result: FE = self.highest_degree.into();
        for c in self.lower_coefficients.iter().rev() {
            result = result * point + *c;
        }
        result
    }

    /// Add a constant: ρ(t) = ρ_x(t) + c·t^d.
    ///
    /// The constant is added to the highest-degree coefficient.
    pub fn addc(&self, c: F) -> Self {
        Self {
            lower_coefficients: self.lower_coefficients.clone(),
            highest_degree: self.highest_degree + c,
        }
    }

    /// Add two commitment polynomials, aligning to the maximum degree.
    ///
    /// Given ρ_x of degree d_1 and ρ_y of degree d_2, with d = max(d_1, d_2):
    /// ρ(t) = t^(d - d_1)·ρ_x(t) + t^(d - d_2)·ρ_y(t).
    pub fn add(&self, other: &Self) -> Self {
        let d1 = self.degree();
        let d2 = other.degree();
        let d = d1.max(d2);

        let mut lower = vec![FE::ZERO; d];

        let shift1 = d - d1;
        for (i, c) in self.lower_coefficients.iter().enumerate() {
            lower[i + shift1] = lower[i + shift1] + *c;
        }
        let shift2 = d - d2;
        for (i, c) in other.lower_coefficients.iter().enumerate() {
            lower[i + shift2] = lower[i + shift2] + *c;
        }

        Self {
            lower_coefficients: lower,
            highest_degree: self.highest_degree + other.highest_degree,
        }
    }

    /// Multiply by a constant: ρ(t) = c·ρ_x(t).
    pub fn mulc(&self, c: F) -> Self {
        let lower = self.lower_coefficients.iter().map(|x| c * *x).collect();
        Self {
            lower_coefficients: lower,
            highest_degree: self.highest_degree * c,
        }
    }

    /// Multiply two commitment polynomials: ρ(t) = ρ_x(t)·ρ_y(t).
    pub fn mul(&self, other: &Self) -> Self {
        let d1 = self.degree();
        let d2 = other.degree();
        let new_degree = d1 + d2;
        let mut lower = vec![FE::ZERO; new_degree];

        // lower × lower (FE × FE)
        for (i, a) in self.lower_coefficients.iter().enumerate() {
            for (j, b) in other.lower_coefficients.iter().enumerate() {
                lower[i + j] = lower[i + j] + *a * *b;
            }
        }
        // self.highest × other.lower (F × FE)
        for (j, b) in other.lower_coefficients.iter().enumerate() {
            lower[d1 + j] = lower[d1 + j] + self.highest_degree * *b;
        }
        // self.lower × other.highest (F × FE)
        for (i, a) in self.lower_coefficients.iter().enumerate() {
            lower[i + d2] = lower[i + d2] + other.highest_degree * *a;
        }

        Self {
            lower_coefficients: lower,
            highest_degree: self.highest_degree * other.highest_degree,
        }
    }

    /// Multiply the polynomial by t^shift (shift all coefficients up).
    pub fn shift(&self, shift: usize) -> Self {
        if shift == 0 {
            return self.clone();
        }
        let mut lower = vec![FE::ZERO; self.degree() + shift];
        for (i, c) in self.lower_coefficients.iter().enumerate() {
            lower[i + shift] = *c;
        }
        Self {
            lower_coefficients: lower,
            highest_degree: self.highest_degree,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;
    use swanky_field::FiniteRing;
    use swanky_field_binary::{F2, F128b};

    fn pow_fe<FE: FiniteField>(base: FE, exp: usize) -> FE {
        let mut result = FE::ONE;
        for _ in 0..exp {
            result = result * base;
        }
        result
    }

    #[test]
    fn from_base_vole_creates_degree_one() {
        let mut rng = thread_rng();
        let value = F2::random(&mut rng);
        let mask = F128b::random(&mut rng);
        let poly = CommitmentPolynomial::<F2, F128b>::from_base_vole(value, mask);
        assert_eq!(poly.degree(), 1);
        assert_eq!(poly.lower_coefficients(), &[mask]);
        assert_eq!(poly.highest_degree(), value);
    }

    #[test]
    fn from_parts_round_trip() {
        let mut rng = thread_rng();
        let lower = vec![F128b::random(&mut rng), F128b::random(&mut rng)];
        let highest = F2::random(&mut rng);
        let poly = CommitmentPolynomial::<F2, F128b>::from_parts(lower.clone(), highest);
        assert_eq!(poly.lower_coefficients(), &lower[..]);
        assert_eq!(poly.highest_degree(), highest);
        assert_eq!(poly.degree(), 2);
    }

    #[test]
    fn evaluate_at_point_horner() {
        let mut rng = thread_rng();
        let value = F128b::random(&mut rng);
        let mask = F128b::random(&mut rng);
        let point = F128b::random(&mut rng);
        let poly = CommitmentPolynomial::<F128b, F128b>::from_base_vole(value, mask);
        // ρ(t) = mask + value·t
        assert_eq!(poly.evaluate_at_point(point), mask + value * point);
    }

    #[test]
    fn evaluate_at_point_subfield() {
        let mut rng = thread_rng();
        let value = F2::random(&mut rng);
        let mask = F128b::random(&mut rng);
        let point = F128b::random(&mut rng);
        let poly = CommitmentPolynomial::<F2, F128b>::from_base_vole(value, mask);
        let value_lifted: F128b = value.into();
        assert_eq!(poly.evaluate_at_point(point), mask + value_lifted * point);
    }

    #[test]
    fn addc_increments_highest_degree() {
        let mut rng = thread_rng();
        let value = F128b::random(&mut rng);
        let mask = F128b::random(&mut rng);
        let c = F128b::random(&mut rng);
        let poly = CommitmentPolynomial::<F128b, F128b>::from_base_vole(value, mask);
        let result = poly.addc(c);
        assert_eq!(result.highest_degree(), value + c);
        assert_eq!(result.lower_coefficients(), poly.lower_coefficients());
    }

    #[test]
    fn addc_evaluation_consistency() {
        let mut rng = thread_rng();
        let value = F128b::random(&mut rng);
        let mask = F128b::random(&mut rng);
        let c = F128b::random(&mut rng);
        let point = F128b::random(&mut rng);
        let poly = CommitmentPolynomial::<F128b, F128b>::from_base_vole(value, mask);
        let result = poly.addc(c);
        let d = poly.degree();
        // Verifier: γ' = γ_x + c · Δ^d.
        assert_eq!(
            result.evaluate_at_point(point),
            poly.evaluate_at_point(point) + c * pow_fe(point, d),
        );
    }

    #[test]
    fn add_same_degree() {
        let mut rng = thread_rng();
        let val_x = F128b::random(&mut rng);
        let val_y = F128b::random(&mut rng);
        let w_x = F128b::random(&mut rng);
        let w_y = F128b::random(&mut rng);
        let point = F128b::random(&mut rng);

        let poly_x = CommitmentPolynomial::<F128b, F128b>::from_base_vole(val_x, w_x);
        let poly_y = CommitmentPolynomial::<F128b, F128b>::from_base_vole(val_y, w_y);

        let sum = poly_x.add(&poly_y);
        assert_eq!(sum.degree(), 1);
        assert_eq!(sum.highest_degree(), val_x + val_y);
        assert_eq!(
            sum.evaluate_at_point(point),
            poly_x.evaluate_at_point(point) + poly_y.evaluate_at_point(point),
        );
    }

    #[test]
    fn add_different_degrees() {
        let mut rng = thread_rng();
        let point = F128b::random(&mut rng);

        let val_a = F128b::random(&mut rng);
        let val_b = F128b::random(&mut rng);
        let val_c = F128b::random(&mut rng);
        let poly_a = CommitmentPolynomial::<F128b, F128b>::from_base_vole(
            val_a,
            F128b::random(&mut rng),
        );
        let poly_b = CommitmentPolynomial::<F128b, F128b>::from_base_vole(
            val_b,
            F128b::random(&mut rng),
        );
        let poly_c = CommitmentPolynomial::<F128b, F128b>::from_base_vole(
            val_c,
            F128b::random(&mut rng),
        );
        let poly_ab = poly_a.mul(&poly_b);
        assert_eq!(poly_ab.degree(), 2);
        assert_eq!(poly_c.degree(), 1);

        let sum = poly_c.add(&poly_ab);
        assert_eq!(sum.degree(), 2);
        assert_eq!(sum.highest_degree(), val_c + val_a * val_b);

        // Verifier: γ = Δ^(d-d_1) γ_c + Δ^(d-d_2) γ_ab.
        let gamma_c = poly_c.evaluate_at_point(point);
        let gamma_ab = poly_ab.evaluate_at_point(point);
        assert_eq!(sum.evaluate_at_point(point), point * gamma_c + gamma_ab);
    }

    #[test]
    fn mulc_scales_correctly() {
        let mut rng = thread_rng();
        let val = F128b::random(&mut rng);
        let mask = F128b::random(&mut rng);
        let c = F128b::random(&mut rng);
        let point = F128b::random(&mut rng);
        let poly = CommitmentPolynomial::<F128b, F128b>::from_base_vole(val, mask);
        let result = poly.mulc(c);
        assert_eq!(result.highest_degree(), val * c);
        assert_eq!(
            result.evaluate_at_point(point),
            c * poly.evaluate_at_point(point),
        );
    }

    #[test]
    fn mul_polynomials() {
        let mut rng = thread_rng();
        let val_x = F128b::random(&mut rng);
        let val_y = F128b::random(&mut rng);
        let w_x = F128b::random(&mut rng);
        let w_y = F128b::random(&mut rng);
        let point = F128b::random(&mut rng);
        let poly_x = CommitmentPolynomial::<F128b, F128b>::from_base_vole(val_x, w_x);
        let poly_y = CommitmentPolynomial::<F128b, F128b>::from_base_vole(val_y, w_y);
        let prod = poly_x.mul(&poly_y);
        assert_eq!(prod.degree(), 2);
        assert_eq!(prod.highest_degree(), val_x * val_y);
        assert_eq!(
            prod.evaluate_at_point(point),
            poly_x.evaluate_at_point(point) * poly_y.evaluate_at_point(point),
        );
    }

    #[test]
    fn mul_subfield_polynomials() {
        let mut rng = thread_rng();
        let val_x = F2::random(&mut rng);
        let val_y = F2::random(&mut rng);
        let w_x = F128b::random(&mut rng);
        let w_y = F128b::random(&mut rng);
        let point = F128b::random(&mut rng);
        let poly_x = CommitmentPolynomial::<F2, F128b>::from_base_vole(val_x, w_x);
        let poly_y = CommitmentPolynomial::<F2, F128b>::from_base_vole(val_y, w_y);
        let prod = poly_x.mul(&poly_y);
        assert_eq!(prod.degree(), 2);
        assert_eq!(prod.highest_degree(), val_x * val_y);
        assert_eq!(
            prod.evaluate_at_point(point),
            poly_x.evaluate_at_point(point) * poly_y.evaluate_at_point(point),
        );
    }

    #[test]
    fn shift_increases_degree() {
        let mut rng = thread_rng();
        let val = F128b::random(&mut rng);
        let mask = F128b::random(&mut rng);
        let point = F128b::random(&mut rng);
        let poly = CommitmentPolynomial::<F128b, F128b>::from_base_vole(val, mask);
        let shifted = poly.shift(2);
        assert_eq!(shifted.degree(), 3);
        assert_eq!(shifted.highest_degree(), val);
        assert_eq!(
            shifted.evaluate_at_point(point),
            poly.evaluate_at_point(point) * pow_fe(point, 2),
        );
    }

    #[test]
    fn shift_zero_is_identity() {
        let mut rng = thread_rng();
        let val = F128b::random(&mut rng);
        let mask = F128b::random(&mut rng);
        let poly = CommitmentPolynomial::<F128b, F128b>::from_base_vole(val, mask);
        let shifted = poly.shift(0);
        assert_eq!(shifted.degree(), poly.degree());
        assert_eq!(shifted.highest_degree(), poly.highest_degree());
        assert_eq!(shifted.lower_coefficients(), poly.lower_coefficients());
    }
}
