/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.PowTrace
public import TauCeti.RingTheory.PowerSeries.Log
-- Proof-only: the Hasse bound `a_q² ≤ 4q`.
import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound

/-!
# The zeta function of an elliptic curve over a finite field

Let `W` be an elliptic curve over a finite field `F` with `q` elements, `π` its `q`-power
Frobenius endomorphism and `a_q = q + 1 - #W(F)` its Frobenius trace. The zeta function of `W` is
the formal power series

`Z(W/F, T) = exp (∑_{n ≥ 1} Nₙ Tⁿ / n) ∈ ℚ⟦T⟧`,

where `Nₙ = #W(𝔽_{qⁿ})` counts the points over an extension of degree `n`, the point at infinity
included. Here `Nₙ` is taken to be `deg (1 - π ^ n)`, which is the number of points of `W` fixed
by `π ^ n` over a separable closure, and the number of points over any extension of `F` of degree
`n` (`coeff_finrank_logOf_zetaFunction`). The definition therefore depends on no chosen field with
`q ^ n` elements.

The zeta function is rational (Silverman V.2.4):

`Z(W/F, T) = (1 - a_q T + q T²) / ((1 - T) (1 - q T))`.

The traces `tₙ = q ^ n + 1 - Nₙ` of the powers of Frobenius satisfy `t₀ = 2`, `t₁ = a_q` and
`tₙ₊₂ = a_q tₙ₊₁ - q tₙ` (`WeierstrassCurve.frobeniusPowTrace_add_two`), and an exponential of
power sums `∑ (1 + qⁿ - tₙ) Tⁿ / n` with such a sequence `t` is this rational function
(`PowerSeries.subst_exp_mul_one_sub_X_mul_one_sub_C_mul_X`). No roots of `T² - a_q T + q` are
introduced.

The Hasse bound `a_q² ≤ 4q` then gives the Riemann hypothesis for `W`: every complex zero of the
numerator `1 - a_q T + q T²` has absolute value `q^{-1/2}`.

## Main definitions

* `WeierstrassCurve.zetaFunction`: the zeta function `Z(W/F, T) ∈ ℚ⟦T⟧`.

## Main results

* `WeierstrassCurve.logOf_zetaFunction`: the logarithm of `Z(W/F, T)` is
  `∑ deg (1 - π ^ n) Tⁿ / n`.
* `WeierstrassCurve.coeff_finrank_logOf_zetaFunction`: for a finite extension `E/F` of degree `n`,
  the `n`th coefficient of the logarithm is `#W(E) / n`.
* `WeierstrassCurve.zetaFunction_mul_one_sub_X_mul_one_sub_C_mul_X` and
  `WeierstrassCurve.zetaFunction_eq_mul_inv`: rationality,
  `Z(W/F, T) = (1 - a_q T + q T²) / ((1 - T) (1 - q T))`.
* `WeierstrassCurve.norm_eq_inv_sqrt_card_of_one_sub_frobeniusTrace_mul_add_card_mul_sq_eq_zero`:
  the Riemann hypothesis, the zeros of `1 - a_q T + q T²` have absolute value `q^{-1/2}`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.
-/

public section

open TauCeti TauCeti.Isogeny PowerSeries

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- **The zeta function** of an elliptic curve `W` over a finite field `F` with `q` elements:
`Z(W/F, T) = exp (∑_{n ≥ 1} Nₙ Tⁿ / n)`, where `Nₙ = deg (1 - π ^ n)` for the `q`-power Frobenius
endomorphism `π`.

`Nₙ` is the number of points of `W`, the point at infinity included, over an extension of `F` of
degree `n` (`coeff_finrank_logOf_zetaFunction`). The zeta function is the rational function
`(1 - a_q T + q T²) / ((1 - T) (1 - q T))` (`zetaFunction_eq_mul_inv`). -/
noncomputable def zetaFunction : ℚ⟦X⟧ :=
  (exp ℚ).subst (PowerSeries.mk fun n ↦
    ((1 - Hom.ofIsogeny (frobeniusIsogeny W) ^ n).degree : ℚ) / n : ℚ⟦X⟧)

/-- The defining equation of `zetaFunction`. -/
theorem zetaFunction_def :
    W.zetaFunction = (exp ℚ).subst (PowerSeries.mk fun n ↦
      ((1 - Hom.ofIsogeny (frobeniusIsogeny W) ^ n).degree : ℚ) / n : ℚ⟦X⟧) :=
  (rfl)

/-- The power sum in the definition of the zeta function has no constant term. -/
private theorem constantCoeff_mk_degree_div :
    constantCoeff (PowerSeries.mk fun n ↦
      ((1 - Hom.ofIsogeny (frobeniusIsogeny W) ^ n).degree : ℚ) / n : ℚ⟦X⟧) = 0 := by
  simp

/-- The zeta function has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_zetaFunction : constantCoeff W.zetaFunction = 1 := by
  rw [zetaFunction_def, constantCoeff_subst_exp (constantCoeff_mk_degree_div W)]

/-- **The logarithm of the zeta function** is `∑_{n ≥ 1} deg (1 - π ^ n) Tⁿ / n`. -/
@[simp]
theorem logOf_zetaFunction :
    logOf W.zetaFunction =
      PowerSeries.mk fun n ↦ ((1 - Hom.ofIsogeny (frobeniusIsogeny W) ^ n).degree : ℚ) / n := by
  rw [zetaFunction_def, logOf_subst_exp (constantCoeff_mk_degree_div W)]

/-- **The zeta function counts points over finite extensions**: for a finite extension `E/F` of
degree `n`, the `n`th coefficient of the logarithm of `Z(W/F, T)` is `#W(E) / n`, where the count
includes the point at infinity. -/
theorem coeff_finrank_logOf_zetaFunction (E : Type*) [Field E] [Finite E] [Algebra F E] :
    coeff (Module.finrank F E) (logOf W.zetaFunction) =
      ((W⁄E).pointCount : ℚ) / Module.finrank F E := by
  -- `t n = q ^ n + 1 - deg (1 - π ^ n)` is also `#E + 1 - #W(E)`, and `#E = q ^ n`
  have h := W.frobeniusPowTrace_finrank E
  rw [frobeniusPowTrace_def, frobeniusTrace_def, Module.natCard_eq_pow_finrank (K := F) (V := E),
    Nat.cast_pow] at h
  rw [logOf_zetaFunction, coeff_mk]
  congr 1
  have hdeg : ((1 - Hom.ofIsogeny (frobeniusIsogeny W) ^ Module.finrank F E).degree : ℤ) =
      (W⁄E).pointCount := by
    linarith
  exact_mod_cast hdeg

/-- **Rationality of the zeta function** (Silverman V.2.4), without inverses:
`Z(W/F, T) (1 - T) (1 - q T) = 1 - a_q T + q T²`, where `q` is the number of elements of `F` and
`a_q` the Frobenius trace of `W`. -/
theorem zetaFunction_mul_one_sub_X_mul_one_sub_C_mul_X :
    W.zetaFunction * ((1 - X) * (1 - C (Nat.card F : ℚ) * X)) =
      1 - C (W.frobeniusTrace : ℚ) * X + C (Nat.card F : ℚ) * X ^ 2 := by
  have h := subst_exp_mul_one_sub_X_mul_one_sub_C_mul_X (W.frobeniusTrace : ℚ) (Nat.card F : ℚ)
    (t := fun n ↦ (W.frobeniusPowTrace n : ℚ)) (by simp) (by simp)
    (fun n ↦ by exact_mod_cast W.frobeniusPowTrace_add_two n)
  -- the power sums `(1 + q ^ n - t n) / n` are the coefficients `deg (1 - π ^ n) / n`
  have hL : (PowerSeries.mk fun n ↦
      (n : ℚ)⁻¹ • (1 + (Nat.card F : ℚ) ^ n - W.frobeniusPowTrace n) : ℚ⟦X⟧) =
      PowerSeries.mk fun n ↦ ((1 - Hom.ofIsogeny (frobeniusIsogeny W) ^ n).degree : ℚ) / n := by
    ext n
    simp only [coeff_mk, frobeniusPowTrace_def, smul_eq_mul]
    push_cast
    ring
  rwa [hL, ← zetaFunction_def] at h

/-- **Rationality of the zeta function** (Silverman V.2.4):
`Z(W/F, T) = (1 - a_q T + q T²) / ((1 - T) (1 - q T))`, where `q` is the number of elements of `F`
and `a_q` the Frobenius trace of `W`. -/
theorem zetaFunction_eq_mul_inv :
    W.zetaFunction = (1 - C (W.frobeniusTrace : ℚ) * X + C (Nat.card F : ℚ) * X ^ 2) *
      ((1 - X) * (1 - C (Nat.card F : ℚ) * X))⁻¹ := by
  have hP : constantCoeff ((1 - X) * (1 - C (Nat.card F : ℚ) * X) : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← W.zetaFunction_mul_one_sub_X_mul_one_sub_C_mul_X, mul_assoc,
    PowerSeries.mul_inv_cancel _ hP, mul_one]

/-- **The Riemann hypothesis for an elliptic curve over a finite field** (Silverman V.2.4): every
complex zero `z` of the numerator `1 - a_q T + q T²` of the zeta function has `|z| = q^{-1/2}`,
where `q` is the number of elements of `F` and `a_q` the Frobenius trace of `W`. -/
theorem norm_eq_inv_sqrt_card_of_one_sub_frobeniusTrace_mul_add_card_mul_sq_eq_zero {z : ℂ}
    (hz : 1 - W.frobeniusTrace * z + Nat.card F * z ^ 2 = 0) :
    ‖z‖ = (√(Nat.card F : ℝ))⁻¹ := by
  have hHasse : (W.frobeniusTrace : ℝ) ^ 2 ≤ 4 * (Nat.card F : ℝ) := by
    exact_mod_cast W.frobeniusTrace_sq_le_four_mul_card
  have hq : 0 < (Nat.card F : ℝ) := by exact_mod_cast Nat.card_pos
  set a : ℝ := (W.frobeniusTrace : ℝ)
  set q : ℝ := (Nat.card F : ℝ)
  -- the real and imaginary parts of the equation `1 - a z + q z² = 0`
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.intCast_re,
    Complex.intCast_im, Complex.natCast_re, Complex.natCast_im, sq, Complex.zero_re, Complex.sub_im,
    Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im] at hre him
  -- either `z` is real, and then a double root as `a² ≤ 4q`, or `2 q re z = a`
  have hnorm : q * Complex.normSq z = 1 := by
    rw [Complex.normSq_apply]
    have him' : z.im * (2 * q * z.re - a) = 0 := by linear_combination him
    rcases mul_eq_zero.mp him' with hy | hx
    · rw [hy] at hre ⊢
      nlinarith [sq_nonneg (2 * q * z.re - a)]
    · linear_combination -hre + z.re * hx
  rw [Complex.norm_def, ← Real.sqrt_inv, eq_inv_of_mul_eq_one_right hnorm]

end WeierstrassCurve

end
