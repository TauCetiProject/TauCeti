/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The real period in the one-real-root case

For a real Weierstrass curve with
`Ψ₂Sq(x) = 4 (x - e) ((x - a)² + b²)` and `b ≠ 0`, the discriminant is negative
and the positive locus of `Ψ₂Sq` is exactly `(e, ∞)`. Consequently its real period
is twice the integral of the inverse square root of this cubic over
that half-line. This reduces evaluation of the period to a single cubic integral,
without a separate ellipticity hypothesis or a choice of roots.

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, second edition, §3.7.
* J. Silverman, *The Arithmetic of Elliptic Curves*, Appendix C, §16.
-/

public section

open MeasureTheory Polynomial Set

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ) {e a b : ℝ}

/-- The discriminant of a real Weierstrass curve in real linear-times-quadratic form. -/
theorem Δ_eq_of_linear_mul_quadratic
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e) * ((x - a) ^ 2 + b ^ 2)) :
    W.Δ = -64 * b ^ 2 * ((e - a) ^ 2 + b ^ 2) ^ 2 := by
  have hc : W.twoTorsionPolynomial =
      ⟨4, -4 * (e + 2 * a), 4 * (2 * a * e + a ^ 2 + b ^ 2),
        -4 * e * (a ^ 2 + b ^ 2)⟩ := by
    apply (Cubic.toPoly_injective _ _).mp
    apply Polynomial.funext
    intro x
    rw [← W.Ψ₂Sq_eq, hW]
    simp only [Cubic.toPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    ring
  have hd := W.twoTorsionPolynomial_discr
  rw [hc] at hd
  simp only [Cubic.discr] at hd
  linear_combination -hd / 16

/-- A factorization with one real root and a nonreal conjugate pair has negative discriminant. -/
theorem Δ_neg_of_one_real_root (hb : b ≠ 0)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e) * ((x - a) ^ 2 + b ^ 2)) :
    W.Δ < 0 := by
  rw [W.Δ_eq_of_linear_mul_quadratic hW]
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hq : 0 < (e - a) ^ 2 + b ^ 2 := by positivity
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hb2) (sq_pos_of_pos hq)

/-- The one-real-root factorization with a nonreal conjugate pair implies ellipticity. -/
theorem isElliptic_of_one_real_root (hb : b ≠ 0)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e) * ((x - a) ^ 2 + b ^ 2)) :
    W.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (W.Δ_neg_of_one_real_root hb hW).ne⟩

/-- The positive locus of the cubic in the one-real-root case is the half-line `(e, ∞)`. -/
theorem eval_Ψ₂Sq_pos_iff_of_one_real_root (hb : b ≠ 0)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e) * ((x - a) ^ 2 + b ^ 2)) (x : ℝ) :
    0 < W.Ψ₂Sq.eval x ↔ e < x := by
  have hq : 0 < (x - a) ^ 2 + b ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)
  rw [hW, mul_pos_iff_of_pos_right hq, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)]
  exact sub_pos

/-- The defining nonnegative integral of the period is the half-line cubic integral. -/
theorem realPeriodLIntegral_eq_of_one_real_root (hb : b ≠ 0)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e) * ((x - a) ^ 2 + b ^ 2)) :
    W.realPeriodLIntegral =
      ∫⁻ x in Ioi e, ENNReal.ofReal (√(4 * (x - e) * ((x - a) ^ 2 + b ^ 2)))⁻¹ := by
  have hs : {x | 0 < W.Ψ₂Sq.eval x} = Ioi e := by
    ext x
    exact W.eval_Ψ₂Sq_pos_iff_of_one_real_root hb hW x
  simp_rw [W.realPeriodLIntegral_def, hs, hW]

/-- The one-real-root period formula as an equality of nonnegative integrals.
Ellipticity, hence finiteness, follows from the factorization. -/
theorem ofReal_realPeriod_eq_of_one_real_root (hb : b ≠ 0)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e) * ((x - a) ^ 2 + b ^ 2)) :
    ENNReal.ofReal W.realPeriod =
      2 * ∫⁻ x in Ioi e, ENNReal.ofReal (√(4 * (x - e) * ((x - a) ^ 2 + b ^ 2)))⁻¹ := by
  let := W.isElliptic_of_one_real_root hb hW
  rw [W.ofReal_realPeriod, W.realPeriodLIntegral_eq_of_one_real_root hb hW]

/-- The real period is twice the real cubic integral on `(e, ∞)`. -/
theorem realPeriod_eq_integral_of_one_real_root (hb : b ≠ 0)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e) * ((x - a) ^ 2 + b ^ 2)) :
    W.realPeriod =
      2 * ∫ x in Ioi e, (√(4 * (x - e) * ((x - a) ^ 2 + b ^ 2)))⁻¹ := by
  rw [W.realPeriod_def, W.realPeriodLIntegral_eq_of_one_real_root hb hW]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x ↦ by positivity)
    (by fun_prop)]

end WeierstrassCurve
