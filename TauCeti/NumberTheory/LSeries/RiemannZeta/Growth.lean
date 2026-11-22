/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Reciprocal.Order
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth

/-!
# Growth of the pole-removed Riemann zeta function

Mathlib's entire function `DirichletCharacter.LFunctionTrivChar₁ 1` extends `(s - 1) ζ(s)`
through the pole at one. It is the product of the entire completion of zeta and a shifted
reciprocal Gamma factor, divided by `2π`. Both factors have order at most one, so the
pole-removed uncompleted function does too. The identity holds at the cancelled poles,
including zero and one.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open Complex DirichletCharacter Filter Real Topology

namespace TauCeti.LFunctions

/-- The entire pole-removed zeta function is the entire completion times the shifted reciprocal
Gamma factor. The equality includes the removed pole and the trivial zeros. -/
theorem LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ (s : ℂ) :
    LFunctionTrivChar₁ 1 s =
      zetaEntireCompletion s * (Gammaℝ (s + 2))⁻¹ / (2 * π : ℂ) := by
  have hg : Differentiable ℂ (fun z : ℂ ↦
      zetaEntireCompletion z * (Gammaℝ (z + 2))⁻¹ / (2 * π : ℂ)) :=
    (differentiable_zetaEntireCompletion.mul
      (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 2))).div_const _
  suffices heq : LFunctionTrivChar₁ 1 = (fun z : ℂ ↦
      zetaEntireCompletion z * (Gammaℝ (z + 2))⁻¹ / (2 * π : ℂ)) by
    exact congrFun heq s
  apply AnalyticOnNhd.eq_of_eventuallyEq
    (fun z _ ↦ (differentiable_LFunctionTrivChar₁ 1).analyticAt z)
    (fun z _ ↦ hg.analyticAt z) (z₀ := (2 : ℂ))
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (by norm_num : 1 < (2 : ℂ).re)] with z hz
  have hz0 : z ≠ 0 := by intro h; subst z; norm_num at hz
  have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hz
  have hΓ : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hz)
  rw [LFunctionTrivChar₁, Function.update_of_ne hz1,
    LFunctionTrivChar_eq_mul_riemannZeta hz1]
  simp only [Nat.primeFactors_one, Finset.prod_empty, one_mul]
  rw [zetaEntireCompletion_eq_mul hz0 hz1, riemannZeta_def_of_ne_zero hz0, Gammaℝ_add_two hz0]
  field_simp [hz0, hΓ, ofReal_ne_zero.mpr pi_ne_zero]

end TauCeti.LFunctions

namespace TauCeti

/-- The entire extension of `(s - 1) ζ(s)` has order at most one on the whole complex plane. -/
theorem orderLE_LFunctionTrivChar₁_one : OrderLE (LFunctionTrivChar₁ 1) 1 := by
  rw [funext LFunctions.LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ]
  simpa only [one_mul, div_eq_mul_inv] using
    (LFunctions.orderLE_zetaEntireCompletion.mul (orderLE_inv_Gammaℝ.comp_mul_add 1 2)).mul
      (orderLE_const ((2 * π : ℂ)⁻¹) 1)

end TauCeti
