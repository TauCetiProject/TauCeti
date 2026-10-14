/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth approximation in `Lᵖ` with control of the support

Mathlib's `MeasureTheory.MemLp.exist_eLpNorm_sub_le` approximates a function in `Lᵖ`, `p < ∞`, by
smooth compactly supported functions, with no control on where the approximants live. If the
function vanishes off a closed set `s`, the approximants can be taken to be supported in any
closed thickening `cthickening δ s`: multiply an approximant by a smooth cutoff with values in
`[0, 1]` that equals `1` on `s` and is supported in `thickening δ s`. Multiplying by the cutoff
does not increase the distance to the function, which is unchanged by it.

Such support control is what is needed to pass a statement about an operator off the support of
its argument from smooth functions to all of `Lᵖ`.
-/

public section

open MeasureTheory Metric Set
open scoped ContDiff

namespace MeasureTheory.MemLp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- A function in `Lᵖ`, `1 ≤ p < ∞`, vanishing almost everywhere off a closed set `s` is the
`Lᵖ` limit of smooth compactly supported functions supported in `cthickening δ s`, for any
`δ > 0`. -/
theorem exist_contDiff_tsupport_subset_cthickening_eLpNorm_sub_le {p : ENNReal} (hp : p ≠ ⊤)
    (hp₁ : 1 ≤ p) {f : E → F} (hf : MemLp f p μ) {s : Set E} (hs : IsClosed s)
    (hfs : ∀ᵐ y ∂μ, y ∉ s → f y = 0) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ g : E → F, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ cthickening δ s ∧
      eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  obtain ⟨θ, hθ, hθr, hθs, hθ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    isOpen_thickening hs (self_subset_thickening hδ s)
  obtain ⟨g, hgc, hg, hfg⟩ := hf.exist_eLpNorm_sub_le hp hp₁ hε
  have htθ : tsupport θ ⊆ cthickening δ s := by
    rw [tsupport, hθs]
    exact closure_thickening_subset_cthickening δ s
  refine ⟨fun y => θ y • g y, hgc.smul_left, hθ.smul hg,
    (tsupport_smul_subset_left _ _).trans htθ, (eLpNorm_mono_ae
      (hf.aestronglyMeasurable.sub (hθ.continuous.smul hg.continuous).aestronglyMeasurable)
      ?_).trans hfg⟩
  filter_upwards [hfs] with y hy
  simp only [Pi.sub_apply, Pi.smul_apply']
  by_cases hys : y ∈ s
  · rw [(hθ1 y).1 hys, one_smul]
  · have h01 := hθr (mem_range_self y)
    rw [hy hys, zero_sub, norm_neg, zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg h01.1]
    exact mul_le_of_le_one_left (norm_nonneg _) h01.2

end MeasureTheory.MemLp
