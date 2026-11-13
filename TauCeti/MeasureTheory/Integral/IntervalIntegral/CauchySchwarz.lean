/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Cauchy–Schwarz inequality for interval integrals

For a function `g` on `[a, b]` whose square is integrable,
`∫ₐᵇ g ≤ √(b - a) √(∫ₐᵇ g²)` (`TauCeti.integral_le_sqrt_mul_sqrt_integral_sq`). This is the
estimate that turns an `L²` bound on a derivative into a uniform Hölder modulus of continuity
`|f(t₂) - f(t₁)| ≤ √(t₂ - t₁) ‖f'‖_{L²}`, as in the Sobolev embedding `W^{1,2} ⊆ C^{1/2}` in one
dimension.

It is the case `f = 1`, `p = q = 2` of Hölder's inequality
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`, restated for interval integrals with square
roots in place of the powers `1 / 2`.
-/

public section

open Set MeasureTheory

namespace TauCeti

/-- **The Cauchy–Schwarz inequality on an interval.** For a function `g` on `[a, b]` with `g²`
integrable, `∫ₐᵇ g ≤ √(b - a) √(∫ₐᵇ g²)`. -/
theorem integral_le_sqrt_mul_sqrt_integral_sq {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg2 : IntervalIntegrable (fun t ↦ g t ^ 2) volume a b) :
    ∫ t in a..b, g t ≤ √(b - a) * √(∫ t in a..b, g t ^ 2) := by
  have hle : ∫ t in a..b, g t ≤ ∫ t in a..b, |g t| :=
    (le_abs_self _).trans (intervalIntegral.abs_integral_le_integral_abs hab)
  refine hle.trans ?_
  have hg2' : IntervalIntegrable (fun t ↦ |g t| ^ 2) volume a b := by simpa only [sq_abs] using hg2
  simp only [← sq_abs (g _)]
  -- On `(a, b]` the nonnegative `|g|` is `√(|g|²)`, hence measurable.
  have hgm : AEStronglyMeasurable (fun t ↦ |g t|) (volume.restrict (Ioc a b)) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hg2'.1.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun t ↦ Real.sqrt_sq (abs_nonneg _))
  have hmem : MemLp (fun t ↦ |g t|) (ENNReal.ofReal 2) (volume.restrict (Ioc a b)) := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hgm).2 hg2'.1
  have hone : MemLp (fun _ ↦ (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Ioc a b)) :=
    memLp_const 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (Filter.Eventually.of_forall fun t ↦ abs_nonneg (g t)) hone hmem
  simp only [one_mul, one_pow, Real.rpow_two, integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hab] at h
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

end TauCeti
