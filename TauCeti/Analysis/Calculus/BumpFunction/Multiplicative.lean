/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Smooth bumps for the measure `dx/x`

For every `R > 1` there is a `C^∞` function `ν : ℝ → ℝ` with `ν ≥ 0`, support in `[R⁻¹, R]`,
`∫_{(0,∞)} ν(x) dx/x = 1` and `ν(x⁻¹) = ν(x)` for `x > 0`
(`TauCeti.exists_smooth_symmetric_bump`). Such a function is a bump for the multiplicative Haar
measure `dx/x` on `(0, ∞)`, invariant under the inversion `x ↦ x⁻¹`, so its smoothed cutoffs at
every scale `ε > 0` take the value `1/2` at `1` (`TauCeti.smoothCutoff_one_eq_half_of_symm`).

## References

* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd*,
  <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>, file
  `PrimeNumberTheoremAnd/SmoothExistence.lean` at revision
  `a4fb6989b07e9c76b511807ae93e33e25b820e9b`: `SmoothExistence` is the statement without the
  inversion symmetry, for `R = 2`. The function here is instead Mathlib's normalized bump
  `ContDiffBump.normed` on `ℝ`, pulled back along `Real.log`.
-/

public section

open Set MeasureTheory
open scoped ContDiff Topology

namespace TauCeti

/-- For every `R > 1` there is a `C^∞` function `ν ≥ 0` supported in `[R⁻¹, R]`, of `dx/x`-mass
`1` on `(0, ∞)`, with `ν x⁻¹ = ν x` for every `x > 0`. -/
theorem exists_smooth_symmetric_bump {R : ℝ} (hR : 1 < R) :
    ∃ ν : ℝ → ℝ, ContDiff ℝ ∞ ν ∧ (∀ x, 0 ≤ ν x) ∧ Function.support ν ⊆ Icc R⁻¹ R ∧
      ∫ x in Ioi 0, ν x / x = 1 ∧ ∀ x > 0, ν x⁻¹ = ν x := by
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hlogR : 0 < Real.log R := Real.log_pos hR
  let b : ContDiffBump (0 : ℝ) := ⟨Real.log R / 4, Real.log R / 2, by positivity, by linarith⟩
  let ν : ℝ → ℝ := fun x ↦ if 0 < x then b.normed volume (Real.log x) else 0
  have hsupp : Function.support ν ⊆ Icc R⁻¹ R := by
    intro x hx
    have hx0 : 0 < x := by
      by_contra h
      exact hx (by simp [ν, h])
    have hbx : Real.log x ∈ Function.support (b.normed volume) := by simpa [ν, hx0] using hx
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hbx
    have habs : |Real.log x| ≤ Real.log R := (hbx.trans (by dsimp [b]; linarith)).le
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    rw [← Real.exp_log hx0, ← Real.exp_log hR0, ← Real.exp_neg]
    exact ⟨Real.exp_le_exp.mpr hlo, Real.exp_le_exp.mpr hhi⟩
  have hcd : ContDiff ℝ ∞ ν := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge 0 x with hx | hx
    · have hpos : ContDiffOn ℝ ∞ (fun t ↦ b.normed volume (Real.log t)) (Ioi 0) :=
        b.contDiff_normed.comp_contDiffOn (Real.contDiffOn_log.mono fun _ ht ↦ ne_of_gt ht)
      refine (hpos.contDiffAt (Ioi_mem_nhds hx)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with t (ht : 0 < t)
      simp [ν, ht]
    · have heq : ν =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (hx.trans_lt (inv_pos.mpr hR0))] with t ht
        exact Function.notMem_support.mp fun h ↦ ht.not_ge (hsupp h).1
      exact contDiffAt_const.congr_of_eventuallyEq heq
  refine ⟨ν, hcd, fun x ↦ ?_, hsupp, ?_, fun x hx ↦ ?_⟩
  · dsimp only [ν]
    split_ifs
    exacts [b.nonneg_normed _, le_rfl]
  · rw [← integral_comp_exp]
    have hEq : (fun t ↦ Real.exp t • (ν (Real.exp t) / Real.exp t)) = b.normed volume := by
      ext t
      simp only [ν, Real.exp_pos, ↓reduceIte, Real.log_exp, smul_eq_mul,
        mul_div_cancel₀ _ (Real.exp_ne_zero t)]
    rw [hEq, b.integral_normed]
  · simp only [ν, inv_pos.mpr hx, hx, ↓reduceIte, Real.log_inv, b.normed_neg]

end TauCeti
