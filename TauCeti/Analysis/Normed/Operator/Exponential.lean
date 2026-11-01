/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Exponentials in normed algebras

This file records basic facts about the exponential in normed algebras, including the
specialization to continuous linear endomorphisms of a normed space.

## Main results

* `TauCeti.norm_exp_le_mul_exp_of_norm_pow_le`: if `‖x ^ n‖ ≤ M * r ^ n` for every `n`, then
  `‖exp x‖ ≤ M * Real.exp r`; in particular `‖exp x‖ ≤ Real.exp ‖x‖` when `‖1‖ ≤ 1`
  (`TauCeti.norm_exp_le_exp_norm`), and power-bounded elements satisfy
  `‖exp (s • b)‖ ≤ M * Real.exp ‖s‖` (`TauCeti.norm_exp_smul_le_mul_exp_of_norm_pow_le`).
* `TauCeti.exp_smul_one`: the exponential of a real scalar multiple of the unit.
* `ContinuousLinearMap.exp_add_smul`: exponentials of scalar multiples of a bounded operator
  compose additively.
* `ContinuousLinearMap.exp_smul_apply_of_apply_eq_smul`: the exponential acts on an eigenvector
  by the scalar exponential of the eigenvalue.
* `ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral`: the Duhamel identity
  `exp (t • B) x - x = ∫₀ᵗ exp (u • B) (B x) du` for the orbits of a real bounded operator.
-/

public section

open NormedSpace

namespace TauCeti

section NormedAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- In a normed `ℚ`-algebra, if the powers of `x` satisfy `‖x ^ n‖ ≤ M * r ^ n`, then
`‖exp x‖ ≤ M * Real.exp r`. -/
theorem norm_exp_le_mul_exp_of_norm_pow_le [NormedAlgebra ℚ 𝔸] {x : 𝔸} {M r : ℝ}
    (h : ∀ n : ℕ, ‖x ^ n‖ ≤ M * r ^ n) : ‖exp x‖ ≤ M * Real.exp r := by
  have hr := (exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) r).mul_left M
  rw [exp_eq_tsum ℚ, Real.exp_eq_exp_ℝ, ← hr.tsum_eq]
  refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂 := ℚ) x)).trans <|
    Summable.tsum_le_tsum (fun n => ?_) (norm_expSeries_summable' (𝕂 := ℚ) x) hr.summable
  rw [norm_smul, ← Rat.norm_cast_real, Rat.cast_inv, Rat.cast_natCast, norm_inv,
    RCLike.norm_natCast, smul_eq_mul, mul_left_comm]
  gcongr
  exact h n

/-- In a normed `ℚ`-algebra whose unit has norm at most one, the exponential is norm-bounded by
the scalar exponential of the norm: `‖exp x‖ ≤ Real.exp ‖x‖`. -/
theorem norm_exp_le_exp_norm [NormedAlgebra ℚ 𝔸] (h_one : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) :
    ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hpow (n : ℕ) : ‖x ^ n‖ ≤ 1 * ‖x‖ ^ n := by
    rw [one_mul]
    cases n with
    | zero => simpa only [pow_zero] using h_one
    | succ m => exact norm_pow_le' x m.succ_pos
  simpa only [one_mul] using norm_exp_le_mul_exp_of_norm_pow_le hpow

/-- If every power of `b` has norm at most `M`, then `‖exp (s • b)‖ ≤ M * Real.exp ‖s‖`. -/
theorem norm_exp_smul_le_mul_exp_of_norm_pow_le {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 𝔸]
    {b : 𝔸} {M : ℝ} (s : 𝕜) (hpow : ∀ n : ℕ, ‖b ^ n‖ ≤ M) :
    ‖exp (s • b)‖ ≤ M * Real.exp ‖s‖ := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕜 𝔸
  refine norm_exp_le_mul_exp_of_norm_pow_le fun n => ?_
  rw [smul_pow, norm_smul, norm_pow, mul_comm]
  gcongr
  exact hpow n

variable [NormedAlgebra ℝ 𝔸]

/-- The exponential of a real scalar multiple of the unit is the corresponding scalar exponential
times the unit. -/
@[simp]
theorem exp_smul_one (c : ℝ) : exp (c • (1 : 𝔸)) = Real.exp c • 1 := by
  rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, ← algebraMap_exp_comm,
    Real.exp_eq_exp_ℝ]

/-- If the unit has norm at most one, then the norm of the exponential of a real scalar multiple
of the unit is at most the corresponding scalar exponential. -/
theorem norm_exp_smul_one_le (h_one : ‖(1 : 𝔸)‖ ≤ 1) (c : ℝ) :
    ‖exp (c • (1 : 𝔸))‖ ≤ Real.exp c := by
  rw [exp_smul_one, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg c)]
  exact mul_le_of_le_one_right (Real.exp_nonneg c) h_one

end NormedAlgebra

section Operator

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The exponential of a scalar multiple of a bounded operator satisfies
`‖exp (t A)‖ ≤ exp (‖A‖ ‖t‖)`. -/
theorem _root_.ContinuousLinearMap.norm_exp_smul_le (A : X →L[𝕜] X) (t : 𝕜) :
    ‖exp (t • A)‖ ≤ Real.exp (‖A‖ * ‖t‖) := by
  let +nondep : NormedAlgebra ℚ (X →L[𝕜] X) := .restrictScalars ℚ 𝕜 _
  rw [mul_comm, ← norm_smul]
  exact norm_exp_le_exp_norm ContinuousLinearMap.norm_id_le _

/-- Exponentials of scalar multiples of the same bounded operator split over addition. -/
theorem _root_.ContinuousLinearMap.exp_add_smul [CompleteSpace X] (A : X →L[𝕜] X) (s t : 𝕜) :
    exp ((s + t) • A) = (exp (s • A)).comp (exp (t • A)) := by
  let +nondep : NormedAlgebra ℚ (X →L[𝕜] X) := .restrictScalars ℚ 𝕜 _
  exact (NormedSpace.exp_add_smul A s t).trans (ContinuousLinearMap.mul_def _ _)

/-- **The exponential of an operator acts exponentially on an eigenvector.** If `B x = μ • x`,
then `exp (t B) x = exp (t μ) • x`. The statement also covers `x = 0`, without requiring a
bundled `Module.End.HasEigenvector` witness. -/
theorem _root_.ContinuousLinearMap.exp_smul_apply_of_apply_eq_smul [CompleteSpace X]
    (B : X →L[𝕜] X) {x : X} {μ : 𝕜} (hx : B x = μ • x) (t : 𝕜) :
    exp (t • B) x = exp (t * μ) • x := by
  have hpow (n : ℕ) : ((t • B) ^ n) x = (t * μ) ^ n • x := by
    induction n with
    | zero => simp
    | succ n hn =>
      simp only [pow_succ, mul_apply_eq_comp, smul_apply, hx, map_smul, hn, smul_smul]
      ring_nf
  have hop := (exp_series_hasSum_exp' (𝕂 := 𝕜) (t • B)).mapL (ContinuousLinearMap.apply 𝕜 X x)
  simp only [ContinuousLinearMap.apply_apply, smul_apply, hpow, smul_smul] at hop
  exact hop.unique ((exp_series_hasSum_exp' (𝕂 := 𝕜) (t * μ)).smul_const x)

end Operator

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **The Duhamel identity for the exponential of a bounded operator.** For `B : X →L[ℝ] X`,
`exp (t B) x - x = ∫₀ᵗ exp (u B) (B x) du`.

This is the fundamental theorem of calculus applied to the differentiable orbit
`u ↦ exp (u B) x`, whose derivative is the continuous function `u ↦ exp (u B) (B x)`. -/
theorem _root_.ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral
    (B : X →L[ℝ] X) (t : ℝ) (x : X) :
    exp (t • B) x - x = ∫ u in (0 : ℝ)..t, exp (u • B) (B x) := by
  have hderiv : ∀ u : ℝ, HasDerivAt (fun v : ℝ => exp (v • B) x) (exp (u • B) (B x)) u := by
    intro u
    simpa [mul_apply_eq_comp] using
      (hasDerivAt_exp_smul_const B u).clm_apply (hasDerivAt_const u x)
  have hcont : Continuous fun u : ℝ => exp (u • B) (B x) :=
    (differentiable_exp_smul_const ℝ B).continuous.clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 t)]
  simp

end Real

end TauCeti

end
