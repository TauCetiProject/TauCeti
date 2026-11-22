/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf.Complex
public import TauCeti.Analysis.Complex.GrowthOrder
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Factorization

/-!
# Zeros of the complex error function

This file locates the zeros of the entire function `TauCeti.Complex.erf` (DLMF §7.13(i)).

* Every zero of `erf` and of `erfc` is simple, because `erf′ = (2/√π) e^{−z²}` never vanishes.
* On the real axis `erf` vanishes only at `0`, because the real error function is strictly
  increasing; on the imaginary axis `erf (iy) = (2i/√π) ∫₀^y e^{t²} dt` vanishes only at `y = 0`.
* `erf` has infinitely many zeros, and so, by its oddness and its conjugation symmetry,
  infinitely many in the open first quadrant.

## Main results

* `TauCeti.Complex.analyticOrderAt_erf_eq_one`, `TauCeti.Complex.analyticOrderAt_erfc_eq_one`:
  all zeros of `erf` and `erfc` are simple.
* `TauCeti.Complex.erf_ofReal_eq_zero_iff`, `TauCeti.Complex.erf_I_mul_ofReal_eq_zero_iff`:
  the only zero of `erf` on the real or the imaginary axis is `0`.
* `TauCeti.Complex.orderLE_erf`: `erf` has order at most `2`.
* `TauCeti.Complex.infinite_setOf_erf_eq_zero`: `erf` has infinitely many zeros.
* `TauCeti.Complex.infinite_erf_zeros_firstQuadrant`: `erf` has infinitely many zeros in the open
  first quadrant.

## Implementation notes

The infinitude of the zeros uses the finite-zero case of Hadamard factorization,
`TauCeti.OrderLE.exists_eq_polynomial_eval_mul_cexp_of_finite_zeros`, since `erf` has order at most
`2`: `|erf z| ≤ (2/√π) |z| e^{|z|²}`. If its zero set were finite, `erf` would be `P(z) e^{Q(z)}`
for polynomials `P` and `Q`. Comparing with `erf′ = (2/√π) e^{−z²}`, the polynomial `P′ + P Q′`
would have no root, hence be a nonzero constant `r`. Then `e^{Q(z) + z²}` would be constant, so
`Q′ = −2z` and `P′ − 2zP = r`. This is impossible: `P ≠ 0`, and the coefficient of
`z^{deg P + 1}` on the left is `−2` times the leading coefficient of `P`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §7.13(i),
  <https://dlmf.nist.gov/7.13>.
* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., Oxford, 1939, Chapter VIII, for
  Hadamard factorization.
-/

public section

noncomputable section

open Complex Filter Asymptotics Bornology Polynomial

open scoped Real ComplexConjugate

namespace TauCeti

namespace Complex

/-! ### Simplicity of the zeros -/

private theorem two_div_sqrt_pi_ne_zero : 2 / (Real.sqrt π : ℂ) ≠ 0 :=
  div_ne_zero two_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')

/-- The derivative `erf′ z = (2/√π) e^{−z²}` never vanishes. -/
theorem deriv_erf_ne_zero (z : ℂ) : deriv erf z ≠ 0 := by
  rw [deriv_erf]
  exact mul_ne_zero two_div_sqrt_pi_ne_zero (Complex.exp_ne_zero _)

/-- Every zero of `erf` is simple. -/
theorem analyticOrderAt_erf_eq_one {z : ℂ} (hz : erf z = 0) : analyticOrderAt erf z = 1 :=
  (differentiable_erf.analyticAt z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
    (deriv_erf_ne_zero z)

/-- Every zero of `erfc` is simple. -/
theorem analyticOrderAt_erfc_eq_one {z : ℂ} (hz : erfc z = 0) : analyticOrderAt erfc z = 1 :=
  (differentiable_erfc.analyticAt z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
    (by rw [(hasDerivAt_erfc z).deriv, neg_ne_zero, ← (hasDerivAt_erf z).deriv]
        exact deriv_erf_ne_zero z)

/-! ### Zeros on the axes -/

/-- On the real axis, `erf` vanishes only at `0`. -/
@[simp]
theorem erf_ofReal_eq_zero_iff {x : ℝ} : erf x = 0 ↔ x = 0 := by
  rw [erf_ofReal, ofReal_eq_zero]
  refine ⟨fun h ↦ TauCeti.Real.strictMono_erf.injective (h.trans TauCeti.Real.erf_zero.symm), ?_⟩
  rintro rfl
  exact TauCeti.Real.erf_zero

/-- On the imaginary axis, `erf (iy) = (2i/√π) y ∫₀¹ e^{(sy)²} ds`. -/
theorem erf_I_mul_ofReal (y : ℝ) :
    erf (I * y) =
      2 / (Real.sqrt π : ℂ) * I * ((y * ∫ s in (0 : ℝ)..1, Real.exp ((s * y) ^ 2) : ℝ) : ℂ) := by
  have hint (s : ℝ) : (I * y) * cexp (-((s : ℂ) * (I * y)) ^ 2) =
      I * ((y * Real.exp ((s * y) ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [show -((s : ℂ) * (I * y)) ^ 2 = ((s : ℂ) * y) ^ 2 by ring_nf; rw [I_sq]; ring]
    ring
  rw [erf_def, intervalIntegral.integral_congr fun s _ ↦ hint s,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_const_mul, mul_assoc]

/-- On the imaginary axis, `erf` vanishes only at `0`. -/
@[simp]
theorem erf_I_mul_ofReal_eq_zero_iff {y : ℝ} : erf (I * y) = 0 ↔ y = 0 := by
  have hpos : 0 < ∫ s in (0 : ℝ)..1, Real.exp ((s * y) ^ 2) :=
    intervalIntegral.intervalIntegral_pos_of_pos
      ((by fun_prop : Continuous fun s : ℝ ↦ Real.exp ((s * y) ^ 2)).intervalIntegrable _ _)
      (fun _ ↦ Real.exp_pos _) one_pos
  rw [erf_I_mul_ofReal, mul_eq_zero, or_iff_right (mul_ne_zero two_div_sqrt_pi_ne_zero I_ne_zero),
    ofReal_eq_zero, mul_eq_zero, or_iff_left hpos.ne']

/-! ### Order of growth -/

/-- The growth bound `|erf z| ≤ (2/√π) |z| e^{|z|²}`. -/
theorem norm_erf_le (z : ℂ) :
    ‖erf z‖ ≤ 2 / Real.sqrt π * (‖z‖ * Real.exp (‖z‖ ^ 2)) := by
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ‖z * cexp (-((s : ℂ) * z) ^ 2)‖ ≤ ‖z‖ * Real.exp (‖z‖ ^ 2) := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr ?_)) (norm_nonneg z)
    rw [norm_neg, norm_pow, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs.1, mul_pow]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hs.1.le hs.2)
  rw [erf_def, norm_mul]
  refine mul_le_mul (le_of_eq ?_) ((intervalIntegral.norm_integral_le_of_norm_le_const hb).trans
    (by simp)) (norm_nonneg _) (by positivity)
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
  norm_num

/-- `erf` has order at most `2`. -/
theorem orderLE_erf : OrderLE erf 2 := by
  refine orderLE_def.mpr fun A' hA' ↦ ?_
  refine (IsBigO.of_bound (2 / Real.sqrt π) (Eventually.of_forall fun z ↦ ?_)).trans
    (isBigO_exp_mul_norm_rpow (E := ℂ) 2 hA')
  have hz : ‖z‖ ≤ Real.exp (‖z‖ ^ 2) :=
    (by nlinarith [sq_nonneg (‖z‖ - 1)] : ‖z‖ ≤ ‖z‖ ^ 2 + 1).trans (Real.add_one_le_exp _)
  rw [Real.norm_eq_abs, Real.abs_exp, Real.rpow_two, two_mul, Real.exp_add]
  exact (norm_erf_le z).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le) (by positivity))

/-! ### Infinitely many zeros -/

/-- `erf` is not a polynomial times the exponential of a polynomial. -/
private theorem not_forall_erf_eq_polynomial_eval_mul_cexp (P Q : ℂ[X]) :
    ¬ ∀ z, erf z = P.eval z * cexp (Q.eval z) := by
  intro hPQ
  set c : ℂ := 2 / (Real.sqrt π : ℂ)
  set R := derivative P + P * derivative Q
  have hR (z : ℂ) : R.eval z * cexp (Q.eval z) = c * cexp (-z ^ 2) := by
    have h : HasDerivAt erf (R.eval z * cexp (Q.eval z)) z := by
      rw [show erf = fun z ↦ P.eval z * cexp (Q.eval z) from funext hPQ]
      convert (P.hasDerivAt z).mul (Q.hasDerivAt z).cexp using 1
      simp only [R, eval_add, eval_mul]
      ring
    exact h.unique (hasDerivAt_erf z)
  have hR0 (z : ℂ) : R.eval z ≠ 0 := fun h0 ↦
    mul_ne_zero two_div_sqrt_pi_ne_zero (Complex.exp_ne_zero _) (by rw [← hR z, h0, zero_mul])
  have hRC : R = C (R.coeff 0) := eq_C_of_degree_le_zero (not_lt.mp fun hdeg ↦
    (Complex.exists_root hdeg).elim fun z hz ↦ hR0 z hz)
  set r := R.coeff 0
  have hr : r ≠ 0 := by simpa [hRC] using hR0 0
  have hexp (z : ℂ) : cexp (Q.eval z) = c / r * cexp (-z ^ 2) := by
    have h := hR z
    rw [hRC, eval_C] at h
    rw [div_mul_eq_mul_div, eq_div_iff hr]
    linear_combination h
  have hQ' (z : ℂ) : (derivative Q).eval z = -2 * z := by
    have h1 := (Q.hasDerivAt z).cexp
    rw [funext hexp] at h1
    have h2 := h1.unique (((hasDerivAt_pow 2 z).neg.cexp).const_mul (c / r))
    rw [hexp z] at h2
    refine mul_left_cancel₀ (mul_ne_zero (div_ne_zero two_div_sqrt_pi_ne_zero hr)
      (Complex.exp_ne_zero (-z ^ 2))) ?_
    linear_combination h2
  have hPpoly : derivative P - C 2 * (X * P) = C r := by
    refine Polynomial.funext fun z ↦ ?_
    have h := congrArg (eval z) hRC
    simp only [R, eval_add, eval_mul, hQ', eval_C] at h
    simp only [eval_sub, eval_mul, eval_C, eval_X, ← h]
    ring
  have hP : P ≠ 0 := by
    rintro rfl
    exact hr (by simpa using congrArg (fun p : ℂ[X] ↦ p.coeff 0) hPpoly.symm)
  -- The coefficient of `X ^ (deg P + 1)` in `P′ − 2XP` is `−2` times the leading coefficient.
  have hcoeff := congrArg (fun p : ℂ[X] ↦ p.coeff (P.natDegree + 1)) hPpoly
  simp only [coeff_sub, coeff_derivative, coeff_C_mul, coeff_X_mul, coeff_C, Nat.succ_ne_zero,
    ite_false, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self _)), zero_mul,
    zero_sub, neg_eq_zero, mul_eq_zero, two_ne_zero, false_or] at hcoeff
  exact hP (leadingCoeff_eq_zero.mp hcoeff)

/-- `erf` has infinitely many zeros. -/
theorem infinite_setOf_erf_eq_zero : {z : ℂ | erf z = 0}.Infinite := fun hfin ↦ by
  obtain ⟨P, Q, -, hPQ⟩ :=
    orderLE_erf.exists_eq_polynomial_eval_mul_cexp_of_finite_zeros differentiable_erf hfin
  exact not_forall_erf_eq_polynomial_eval_mul_cexp P Q hPQ

/-- `erf` has infinitely many zeros in the open first quadrant. -/
theorem infinite_erf_zeros_firstQuadrant :
    {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ erf z = 0}.Infinite := by
  set S := {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ erf z = 0}
  intro hS
  refine infinite_setOf_erf_eq_zero ((((((Set.finite_singleton 0).union hS).union
    (hS.image Neg.neg)).union (hS.image conj)).union (hS.image fun z ↦ -conj z)).subset ?_)
  intro z (hz : erf z = 0)
  by_cases h0 : z = 0
  · simp [h0]
  have hre : z.re ≠ 0 := fun h ↦ h0 <| by
    have hz' : z = I * z.im := by apply Complex.ext <;> simp [h]
    rw [hz', erf_I_mul_ofReal_eq_zero_iff] at hz
    rw [hz', hz, ofReal_zero, mul_zero]
  have him : z.im ≠ 0 := fun h ↦ h0 <| by
    have hz' : z = z.re := by apply Complex.ext <;> simp [h]
    rw [hz', erf_ofReal_eq_zero_iff] at hz
    rw [hz', hz, ofReal_zero]
  rcases hre.lt_or_gt with hre | hre <;> rcases him.lt_or_gt with him | him
  · exact Or.inl <| Or.inl <| Or.inr ⟨-z, ⟨by simpa using hre, by simpa using him,
      by rw [erf_neg, hz, neg_zero]⟩, neg_neg z⟩
  · exact Or.inr ⟨-conj z, ⟨by simpa using hre, by simpa using him,
      by rw [erf_neg, erf_conj, hz, map_zero, neg_zero]⟩, by simp⟩
  · exact Or.inl <| Or.inr ⟨conj z, ⟨by simpa using hre, by simpa using him,
      by rw [erf_conj, hz, map_zero]⟩, by simp⟩
  · exact Or.inl <| Or.inl <| Or.inl <| Or.inr ⟨hre, him, hz⟩

end Complex

end TauCeti
