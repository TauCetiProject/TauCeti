/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Sobolev.Comparison
public import Mathlib.Tactic.NormNum

/-!
# A nonzero square-root cone in the Sobolev Cauchy graph

The compactly supported datum `‖z‖^(1/2) χ(z)` is continuous and Hölder of order one half.
Its Cauchy integral gains one derivative: it is `C¹`, and its derivative is one-half Hölder.
The graph operator constructed from `Lᵖ` data has this same derivative almost everywhere.
This tests the rough order-zero Hölder gain on a nonzero datum without a `C¹` input assumption.
-/

public noncomputable section

open MeasureTheory Complex ComplexConjugate Metric Set TopologicalSpace Function
open scoped ENNReal NNReal

namespace TauCeti.CauchyTransform.Rough

open TauCeti.CauchyTransform

/-- A smooth cutoff equal to one on the unit closed disc. -/
def cutoff : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The compactly supported square-root cone datum. -/
def cone (z : ℂ) : ℂ := ((‖z‖ ^ ((1 / 2 : ℝ≥0) : ℝ) * cutoff z : ℝ) : ℂ)

/-- The cone is continuous. -/
theorem cone_continuous : Continuous cone :=
  Complex.continuous_ofReal.comp
    ((continuous_norm.rpow_const fun _ ↦ Or.inr (by norm_num)).mul cutoff.continuous)

/-- The cutoff fixes the input support disc. -/
theorem cone_support : support cone ⊆ closedBall (0 : ℂ) 2 := by
  intro z hz
  by_contra hn
  have hout : 2 < ‖z‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hn
  have hχ := cutoff.zero_of_le_dist (by simpa [cutoff, dist_zero_right] using hout.le)
  exact hz (by simp [cone, hχ])

/-- The cone has compact support. -/
theorem cone_compact : HasCompactSupport cone :=
  .of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 2) cone_support

/-- The cone is nonzero at a point where the cutoff is one. -/
theorem cone_nonzero : cone (1 / 4) ≠ 0 := by
  have hχ : cutoff (1 / 4) = 1 := cutoff.one_of_mem_closedBall (by
    simp [cutoff, mem_closedBall, dist_eq_norm]
    norm_num)
  simp only [cone, hχ, mul_one, Complex.ofReal_ne_zero]
  exact (Real.rpow_pos_of_pos (by norm_num : 0 < ‖(1 / 4 : ℂ)‖) _).ne'

/-- The same cone belongs to the input at every finite exponent. -/
theorem cone_memLp (p : ℝ≥0∞) : MemLp cone p (volume : Measure ℂ) :=
  cone_continuous.memLp_of_hasCompactSupport cone_compact

/-- Its Cauchy integral is globally `C¹`. -/
theorem cone_cauchy_contDiff : ContDiff ℝ 1 (cauchyTransform cone) := by
  apply contDiff_iff_contDiffAt.2
  intro z
  have h := contDiffOn_holderOnWith_fderiv_cauchyTransform_norm_rpow_mul
    (α := (1 / 2 : ℝ≥0)) (by norm_num) (by norm_num)
    cutoff.contDiff cutoff.hasCompactSupport (R := ‖z‖) (norm_nonneg z)
  exact h.1.contDiffAt (isOpen_ball.mem_nhds (by
    simp only [mem_ball, dist_zero_right]
    linarith))

/-- The constructed graph carries the Hölder derivative of the rough cone. -/
theorem cone_graph_gain {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    ContDiff ℝ 1 (cauchyTransform cone) ∧
      ∃ C : ℝ≥0, HolderOnWith C (1 / 2 : ℝ≥0)
        (fderiv ℝ (cauchyTransform cone)) (closedBall (0 : ℂ) 2) ∧
      WeakDerivStep.weakFDeriv _
        (graphL hp hp_top 0 2 2 (((cone_memLp p).restrict (closedBall (0 : ℂ) 2)).toLp cone))
        =ᵐ[volume.restrict (disc 0 2 : Set ℂ)] fderiv ℝ (cauchyTransform cone) := by
  have hHolder := contDiffOn_holderOnWith_fderiv_cauchyTransform_norm_rpow_mul
    (α := (1 / 2 : ℝ≥0)) (by norm_num) (by norm_num)
    cutoff.contDiff cutoff.hasCompactSupport (R := 2) (by norm_num)
  obtain ⟨C, hC⟩ := hHolder.2
  refine ⟨cone_cauchy_contDiff, C, hC, ?_⟩
  have hj := (hasWeakFDerivOn_cauchy (c := 0) (r := 2) hp hp_top
    (cone_memLp p) cone_support ⊤).ae_eq_fderiv
      ((cone_cauchy_contDiff.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      (fun x _ ↦ cone_cauchy_contDiff.differentiable one_ne_zero x)
  rw [Opens.coe_top, Measure.restrict_univ] at hj
  rw [graphL_toLp_weakFDeriv hp hp_top (cone_memLp p) cone_support 2]
  exact (LpToLpRestrictCLM_coeFn ℂ _ _).trans
    (hj.filter_mono (ae_mono Measure.restrict_le_self))

end TauCeti.CauchyTransform.Rough
