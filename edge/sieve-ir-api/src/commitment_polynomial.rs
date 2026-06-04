//! Polynomial commitment type for VOLE-based zero-knowledge protocols.
//!
//! A [`CommitmentPolynomial`] represents the polynomial ρ_x(t) = ρ_0 + ρ_1·t + ··· + ρ_d·t^d
//! where ρ_d = x is the committed value and ρ_0, ..., ρ_{d-1} are random masking coefficients
//! drawn from the extension field.
//!
//! The committed value lives in the *clear* field `F` (e.g. the small field a circuit operates
//! over), whereas the masking coefficients live in the larger extension field `FE` (where the
//! VOLE correlation and the global key Δ live). `F` is a subfield of `FE`, captured by the
//! [`IsSubFieldOf`] bound. To reflect this, the highest-degree coefficient is stored separately
//! from the lower coefficients:
//! - [`CommitmentPolynomial::highest_degree`] is the committed value `x ∈ F`.
//! - [`CommitmentPolynomial::lower_coefficients`] are the masks `ρ_0, ..., ρ_{d-1} ∈ FE`.
//!
//! Gate operations allow building commitment polynomials bottom-up through a circuit:
//! - [`CommitmentPolynomial::addc`]: add a constant
//! - [`CommitmentPolynomial::add`]: add two commitments (aligning degrees)
//! - [`CommitmentPolynomial::mulc`]: multiply by a constant
//! - [`CommitmentPolynomial::mul`]: multiply two commitments
//!
//! Each of these preserves the invariant that the highest-degree coefficient (the committed
//! value) stays in the clear field `F`.

use swanky_field::{FiniteField, IsSubFieldOf};

/// A polynomial commitment over an extension field `FE` whose committed value lives in the
/// subfield `F`.
///
/// Represents the polynomial ρ(t) = ρ_0 + ρ_1·t + ··· + ρ_d·t^d, where:
/// - `lower_coefficients` holds `[ρ_0, ρ_1, ..., ρ_{d-1}]`, the masking coefficients in `FE`.
/// - `highest_degree` holds `ρ_d = x`, the committed value, in the clear field `F`.
///
/// `F` defaults to `FE`, recovering the homogeneous case where the committed value is also an
/// element of the full extension field.
#[derive(Clone, Debug)]
pub struct CommitmentPolynomial<FE: FiniteField, F: IsSubFieldOf<FE> = FE> {
    lower_coefficients: Vec<FE>,
    highest_degree: F,
}

impl<FE: FiniteField, F: IsSubFieldOf<FE>> CommitmentPolynomial<FE, F> {
    /// Create a commitment polynomial from a base VOLE.
    ///
    /// Given a value `x ∈ F` and a VOLE mask `w ∈ FE`, constructs ρ(t) = w + x·t (degree 1).
    pub fn from_base_vole(value: F, mask: FE) -> Self {
        Self {
            lower_coefficients: vec![mask],
            highest_degree: value,
        }
    }

    /// Create a commitment polynomial directly from its coefficients.
    ///
    /// `lower_coefficients` are the masking coefficients `[ρ_0, ..., ρ_{d-1}] ∈ FE` and
    /// `highest_degree` is the committed value `ρ_d = x ∈ F` (the former last element of the
    /// combined coefficient vector). An empty `lower_coefficients` yields a degree-0 (constant)
    /// polynomial equal to `x`.
    pub fn from_coefficients(lower_coefficients: Vec<FE>, highest_degree: F) -> Self {
        Self {
            lower_coefficients,
            highest_degree,
        }
    }

    /// Return the degree of the polynomial.
    pub fn degree(&self) -> usize {
        self.lower_coefficients.len()
    }

    /// Return a reference to the lower coefficients `[ρ_0, ..., ρ_{d-1}]` (excluding the
    /// committed value).
    pub fn lower_coefficients(&self) -> &[FE] {
        &self.lower_coefficients
    }

    /// Return the committed value `ρ_d = x` (the highest-degree coefficient), in the clear
    /// field `F`.
    pub fn highest_degree(&self) -> F {
        self.highest_degree
    }

    /// Return the full coefficient list `[ρ_0, ..., ρ_d]` as elements of `FE`.
    ///
    /// This reconstructs the combined vector by lifting the committed value from `F` into `FE`.
    pub fn coefficients(&self) -> Vec<FE> {
        let mut coeffs = self.lower_coefficients.clone();
        coeffs.push(self.highest_degree.into());
        coeffs
    }

    /// Evaluate the polynomial at a given point using Horner's method.
    ///
    /// This is useful for the verifier to evaluate at Δ (the global VOLE key).
    pub fn evaluate_at_point(&self, point: FE) -> FE {
        // Start from the highest-degree coefficient (lifted into `FE`) and fold downward.
        let mut result: FE = self.highest_degree.into();
        for c in self.lower_coefficients.iter().rev() {
            result = result * point + *c;
        }
        result
    }

    /// Add a constant: ρ(t) = ρ_x(t) + c·t^d
    ///
    /// The constant is added to the highest-degree coefficient (the committed value), so it is
    /// itself a clear-field value and the result remains a valid commitment.
    pub fn addc(&self, c: F) -> Self {
        Self {
            lower_coefficients: self.lower_coefficients.clone(),
            highest_degree: self.highest_degree + c,
        }
    }

    /// Add two commitment polynomials, aligning to the maximum degree.
    ///
    /// Given ρ_x of degree d_1 and ρ_y of degree d_2, with d = max(d_1, d_2):
    /// ρ(t) = t^(d - d_1)·ρ_x(t) + t^(d - d_2)·ρ_y(t)
    ///
    /// Both committed values are shifted to the top degree `d`, so the resulting committed value
    /// is their sum in `F`, and the lower coefficients combine in `FE`.
    pub fn add(&self, other: &Self) -> Self {
        let d1 = self.degree();
        let d2 = other.degree();
        let d = d1.max(d2);

        let shift1 = d - d1;
        let shift2 = d - d2;

        // Lower coefficients occupy positions 0..d; position d is the (clear) committed value.
        let mut lower = vec![FE::ZERO; d];

        for (i, c) in self.lower_coefficients.iter().enumerate() {
            lower[i + shift1] = lower[i + shift1] + *c;
        }
        for (i, c) in other.lower_coefficients.iter().enumerate() {
            lower[i + shift2] = lower[i + shift2] + *c;
        }

        Self {
            lower_coefficients: lower,
            highest_degree: self.highest_degree + other.highest_degree,
        }
    }

    /// Multiply by a constant: ρ(t) = c·ρ_x(t)
    ///
    /// The constant is a clear-field value, so the committed value `c·x` stays in `F`.
    pub fn mulc(&self, c: F) -> Self {
        // `c * *x` uses `F: Mul<FE, Output = FE>`, keeping the masks in `FE`.
        let lower = self.lower_coefficients.iter().map(|x| c * *x).collect();
        Self {
            lower_coefficients: lower,
            highest_degree: self.highest_degree * c,
        }
    }

    /// Multiply two commitment polynomials: ρ(t) = ρ_x(t)·ρ_y(t)
    ///
    /// The top coefficient of the product is `x·y` (the product of the two committed values),
    /// which stays in `F`; every lower coefficient involves at least one mask and so lives
    /// in `FE`.
    pub fn mul(&self, other: &Self) -> Self {
        let d1 = self.degree();
        let d2 = other.degree();
        let new_degree = d1 + d2;

        // Positions 0..new_degree are lower coefficients; position new_degree is the committed
        // value `x·y`.
        let mut lower = vec![FE::ZERO; new_degree];

        // mask_x · mask_y  (FE · FE)
        for (i, a) in self.lower_coefficients.iter().enumerate() {
            for (j, b) in other.lower_coefficients.iter().enumerate() {
                lower[i + j] = lower[i + j] + *a * *b;
            }
        }
        // mask_x · y  (FE · F), landing at degree i + d2
        for (i, a) in self.lower_coefficients.iter().enumerate() {
            lower[i + d2] = lower[i + d2] + other.highest_degree * *a;
        }
        // x · mask_y  (F · FE), landing at degree d1 + j
        for (j, b) in other.lower_coefficients.iter().enumerate() {
            lower[d1 + j] = lower[d1 + j] + self.highest_degree * *b;
        }

        Self {
            lower_coefficients: lower,
            highest_degree: self.highest_degree * other.highest_degree,
        }
    }

    /// Multiply the polynomial by t^shift (shift all coefficients up).
    ///
    /// This raises every degree by `shift`, so the committed value stays put (now at degree
    /// `d + shift`) and `shift` zero masks are prepended to the lower coefficients.
    pub fn shift(&self, shift: usize) -> Self {
        if shift == 0 {
            return self.clone();
        }
        let mut lower = vec![FE::ZERO; self.lower_coefficients.len() + shift];
        for (i, c) in self.lower_coefficients.iter().enumerate() {
            lower[i + shift] = *c;
        }
        Self {
            lower_coefficients: lower,
            highest_degree: self.highest_degree,
        }
    }

    /// Multiply `other` by a clear scalar and accumulate into `self`, aligning at degree 0.
    ///
    /// Computes `self += scalar·other` coefficient-wise from the constant term up, growing
    /// `self` if `other` has the larger degree. The scalar is a clear-field value so the top
    /// coefficient remains in `F`; when `self` grows, its previous committed value becomes an
    /// interior coefficient and is lifted into `FE`.
    pub fn add_scaled(&mut self, other: &Self, scalar: F) {
        let self_len = self.degree() + 1;
        let other_len = other.degree() + 1;
        let new_degree = self_len.max(other_len) - 1;

        let mut lower = vec![FE::ZERO; new_degree];

        // `self`'s masks carry over unchanged.
        for (i, c) in self.lower_coefficients.iter().enumerate() {
            lower[i] = lower[i] + *c;
        }
        // If `self` grew, its old committed value is now interior; lift it into `FE`.
        if self_len - 1 < new_degree {
            lower[self_len - 1] = lower[self_len - 1] + Into::<FE>::into(self.highest_degree);
        }

        // `other`'s masks, scaled.
        for (i, c) in other.lower_coefficients.iter().enumerate() {
            lower[i] = lower[i] + scalar * *c;
        }
        // If `other` does not reach the new top degree, its committed value is interior too.
        if other_len - 1 < new_degree {
            lower[other_len - 1] =
                lower[other_len - 1] + Into::<FE>::into(scalar * other.highest_degree);
        }

        let highest = if self_len > other_len {
            self.highest_degree
        } else if other_len > self_len {
            scalar * other.highest_degree
        } else {
            self.highest_degree + scalar * other.highest_degree
        };

        self.lower_coefficients = lower;
        self.highest_degree = highest;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;
    use swanky_field::FiniteRing;
    use swanky_field_binary::{F2, F8b, F128b};

    fn power(base: F128b, exp: usize) -> F128b {
        let mut result = F128b::ONE;
        for _ in 0..exp {
            result *= base;
        }
        result
    }

    /// Reference polynomial evaluation from the full coefficient list, independent of
    /// `evaluate_at_point`'s Horner implementation.
    fn eval_reference(poly: &CommitmentPolynomial<F128b>, point: F128b) -> F128b {
        let mut acc = F128b::ZERO;
        let mut p = F128b::ONE;
        for c in poly.coefficients() {
            acc = acc + c * p;
            p *= point;
        }
        acc
    }

    #[test]
    fn from_base_vole_layout() {
        let rng = &mut thread_rng();
        let x = F128b::random(rng);
        let w = F128b::random(rng);

        let poly = CommitmentPolynomial::from_base_vole(x, w);

        assert_eq!(poly.degree(), 1);
        assert_eq!(poly.lower_coefficients(), &[w]);
        assert_eq!(poly.highest_degree(), x);
        assert_eq!(poly.coefficients(), &[w, x]);
    }

    #[test]
    fn from_coefficients_layout() {
        let rng = &mut thread_rng();
        let r0 = F128b::random(rng);
        let r1 = F128b::random(rng);
        let x = F128b::random(rng);

        let poly = CommitmentPolynomial::from_coefficients(vec![r0, r1], x);
        assert_eq!(poly.degree(), 2);
        assert_eq!(poly.lower_coefficients(), &[r0, r1]);
        assert_eq!(poly.highest_degree(), x);
        assert_eq!(poly.coefficients(), &[r0, r1, x]);
    }

    #[test]
    fn from_coefficients_degree_zero() {
        let rng = &mut thread_rng();
        let x = F128b::random(rng);
        let delta = F128b::random(rng);

        let poly: CommitmentPolynomial<F128b> = CommitmentPolynomial::from_coefficients(vec![], x);
        assert_eq!(poly.degree(), 0);
        assert!(poly.lower_coefficients().is_empty());
        assert_eq!(poly.coefficients(), &[x]);
        // A degree-0 polynomial evaluates to its (constant) committed value everywhere.
        assert_eq!(poly.evaluate_at_point(delta), x);
    }

    #[test]
    fn evaluate_matches_reference() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);
        let poly = CommitmentPolynomial::from_coefficients(
            vec![F128b::random(rng), F128b::random(rng), F128b::random(rng)],
            F128b::random(rng),
        );
        assert_eq!(poly.evaluate_at_point(delta), eval_reference(&poly, delta));
    }

    #[test]
    fn evaluate_degree_one_explicit() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);
        let x = F128b::random(rng);
        let w = F128b::random(rng);

        let poly = CommitmentPolynomial::from_base_vole(x, w);
        assert_eq!(poly.evaluate_at_point(delta), w + x * delta);
    }

    #[test]
    fn addc_evaluation() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);
        let x = F128b::random(rng);
        let w = F128b::random(rng);
        let c = F128b::random(rng);

        let poly = CommitmentPolynomial::from_base_vole(x, w);
        let summed = poly.addc(c);

        let d = poly.degree();
        // γ_sum = γ_x + c·Δ^d
        assert_eq!(
            summed.evaluate_at_point(delta),
            poly.evaluate_at_point(delta) + c * power(delta, d)
        );
        // The committed value absorbs the constant; masks are untouched.
        assert_eq!(summed.highest_degree(), x + c);
        assert_eq!(summed.lower_coefficients(), poly.lower_coefficients());
    }

    #[test]
    fn add_same_degree() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);

        let p = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let q = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));

        let sum = p.add(&q);
        assert_eq!(sum.degree(), 1);
        // Equal degree, no shifting: evaluations add directly.
        assert_eq!(
            sum.evaluate_at_point(delta),
            p.evaluate_at_point(delta) + q.evaluate_at_point(delta)
        );
        assert_eq!(sum.highest_degree(), p.highest_degree() + q.highest_degree());
    }

    #[test]
    fn add_different_degree() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);

        // p has degree 1, q has degree 2 (a product of two degree-1 polynomials).
        let p = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let a = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let b = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let q = a.mul(&b);

        assert_eq!(p.degree(), 1);
        assert_eq!(q.degree(), 2);

        let sum = p.add(&q);
        assert_eq!(sum.degree(), 2);

        // d = 2, shift_p = 1, shift_q = 0: γ = Δ^1·γ_p + Δ^0·γ_q
        let expected = delta * p.evaluate_at_point(delta) + q.evaluate_at_point(delta);
        assert_eq!(sum.evaluate_at_point(delta), expected);
    }

    #[test]
    fn mulc_evaluation() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);
        let c = F128b::random(rng);

        let p = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let scaled = p.mulc(c);

        assert_eq!(scaled.degree(), p.degree());
        assert_eq!(
            scaled.evaluate_at_point(delta),
            c * p.evaluate_at_point(delta)
        );
        assert_eq!(scaled.highest_degree(), p.highest_degree() * c);
    }

    #[test]
    fn mul_evaluation() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);

        let p = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let q = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));

        let prod = p.mul(&q);
        assert_eq!(prod.degree(), 2);
        assert_eq!(
            prod.evaluate_at_point(delta),
            p.evaluate_at_point(delta) * q.evaluate_at_point(delta)
        );
        assert_eq!(prod.highest_degree(), p.highest_degree() * q.highest_degree());
    }

    #[test]
    fn mul_with_constant_polynomial() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);

        let p = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let constant: CommitmentPolynomial<F128b> =
            CommitmentPolynomial::from_coefficients(vec![], F128b::random(rng));

        let prod = p.mul(&constant);
        assert_eq!(prod.degree(), p.degree());
        assert_eq!(
            prod.evaluate_at_point(delta),
            p.evaluate_at_point(delta) * constant.evaluate_at_point(delta)
        );
    }

    #[test]
    fn shift_evaluation() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);

        let p = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let shifted = p.shift(3);

        assert_eq!(shifted.degree(), p.degree() + 3);
        // Committed value is preserved by the shift.
        assert_eq!(shifted.highest_degree(), p.highest_degree());
        // Evaluating: ρ(Δ)·Δ^3.
        assert_eq!(
            shifted.evaluate_at_point(delta),
            p.evaluate_at_point(delta) * power(delta, 3)
        );
    }

    #[test]
    fn shift_zero_is_identity() {
        let rng = &mut thread_rng();
        let p = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let shifted = p.shift(0);
        assert_eq!(shifted.coefficients(), p.coefficients());
        assert_eq!(shifted.highest_degree(), p.highest_degree());
    }

    #[test]
    fn add_scaled_equal_degree() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);
        let scalar = F128b::random(rng);

        let mut acc = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let other = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));

        let before = acc.evaluate_at_point(delta);
        acc.add_scaled(&other, scalar);

        // Equal degree (low-aligned == high-aligned here): π(Δ) = acc(Δ) + scalar·other(Δ).
        assert_eq!(acc.degree(), 1);
        assert_eq!(
            acc.evaluate_at_point(delta),
            before + scalar * other.evaluate_at_point(delta)
        );
    }

    #[test]
    fn add_scaled_other_longer() {
        let rng = &mut thread_rng();
        let scalar = F128b::random(rng);

        // acc: degree 1, other: degree 2.
        let mut acc = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let a = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let b = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let other = a.mul(&b);

        // Low-aligned reference: combine the two full coefficient lists index-by-index.
        let acc_coeffs = acc.coefficients();
        let other_coeffs = other.coefficients();
        let new_len = acc_coeffs.len().max(other_coeffs.len());
        let mut expected = vec![F128b::ZERO; new_len];
        for (i, c) in acc_coeffs.iter().enumerate() {
            expected[i] = expected[i] + *c;
        }
        for (i, c) in other_coeffs.iter().enumerate() {
            expected[i] = expected[i] + scalar * *c;
        }

        acc.add_scaled(&other, scalar);
        assert_eq!(acc.degree(), 2);
        assert_eq!(acc.coefficients(), expected);
    }

    #[test]
    fn add_scaled_self_longer() {
        let rng = &mut thread_rng();
        let scalar = F128b::random(rng);

        // acc: degree 2, other: degree 1.
        let a = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let b = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));
        let mut acc = a.mul(&b);
        let other = CommitmentPolynomial::from_base_vole(F128b::random(rng), F128b::random(rng));

        let acc_coeffs = acc.coefficients();
        let other_coeffs = other.coefficients();
        let new_len = acc_coeffs.len().max(other_coeffs.len());
        let mut expected = vec![F128b::ZERO; new_len];
        for (i, c) in acc_coeffs.iter().enumerate() {
            expected[i] = expected[i] + *c;
        }
        for (i, c) in other_coeffs.iter().enumerate() {
            expected[i] = expected[i] + scalar * *c;
        }

        acc.add_scaled(&other, scalar);
        assert_eq!(acc.degree(), 2);
        assert_eq!(acc.coefficients(), expected);
    }

    // --- Subfield (`F != FE`) tests: committed value in `F2`, masks in `F128b`. ---

    #[test]
    fn subfield_base_vole_keeps_value_in_clear_field() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);
        let x = F2::random(rng);
        let w = F128b::random(rng);

        let poly: CommitmentPolynomial<F128b, F2> = CommitmentPolynomial::from_base_vole(x, w);

        // `highest_degree()` returns an `F2` value (the clear committed bit).
        let value: F2 = poly.highest_degree();
        assert_eq!(value, x);
        assert_eq!(poly.lower_coefficients(), &[w]);
        // Evaluation lifts the clear value into `F128b`.
        assert_eq!(poly.evaluate_at_point(delta), w + Into::<F128b>::into(x) * delta);
    }

    #[test]
    fn subfield_mul_keeps_product_in_clear_field() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);

        let x = F2::random(rng);
        let y = F2::random(rng);
        let p: CommitmentPolynomial<F128b, F2> =
            CommitmentPolynomial::from_base_vole(x, F128b::random(rng));
        let q: CommitmentPolynomial<F128b, F2> =
            CommitmentPolynomial::from_base_vole(y, F128b::random(rng));

        let prod = p.mul(&q);
        // The product of two clear bits is still a clear bit.
        assert_eq!(prod.highest_degree(), x * y);
        assert_eq!(
            prod.evaluate_at_point(delta),
            p.evaluate_at_point(delta) * q.evaluate_at_point(delta)
        );
    }

    #[test]
    fn subfield_addc_and_mulc_in_clear_field() {
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);

        let x = F2::random(rng);
        let c = F2::random(rng);
        let poly: CommitmentPolynomial<F128b, F2> =
            CommitmentPolynomial::from_base_vole(x, F128b::random(rng));

        let added = poly.addc(c);
        assert_eq!(added.highest_degree(), x + c);
        assert_eq!(
            added.evaluate_at_point(delta),
            poly.evaluate_at_point(delta) + Into::<F128b>::into(c) * power(delta, poly.degree())
        );

        let scaled = poly.mulc(c);
        assert_eq!(scaled.highest_degree(), x * c);
        assert_eq!(
            scaled.evaluate_at_point(delta),
            Into::<F128b>::into(c) * poly.evaluate_at_point(delta)
        );
    }

    #[test]
    fn subfield_f8b_in_f128b() {
        // Exercise a non-trivial, non-prime subfield: F8b ⊂ F128b.
        let rng = &mut thread_rng();
        let delta = F128b::random(rng);

        let x = F8b::random(rng);
        let y = F8b::random(rng);
        let p: CommitmentPolynomial<F128b, F8b> =
            CommitmentPolynomial::from_base_vole(x, F128b::random(rng));
        let q: CommitmentPolynomial<F128b, F8b> =
            CommitmentPolynomial::from_base_vole(y, F128b::random(rng));

        let prod = p.mul(&q);
        assert_eq!(prod.highest_degree(), x * y);
        assert_eq!(
            prod.evaluate_at_point(delta),
            p.evaluate_at_point(delta) * q.evaluate_at_point(delta)
        );
    }
}
