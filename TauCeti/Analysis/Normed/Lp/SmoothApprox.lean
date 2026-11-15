/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth approximation in `Lᵖ` with control of the support

Mathlib's `MeasureTheory.MemLp.exist_eLpNorm_sub_le` approximates a function in `Lᵖ`, `p < ∞`, by
smooth compactly supported functions, with no control on where the approximants live. If the
function vanishes off a closed set `s`, the approximants can be taken to be supported in any
neighbourhood `t` of `s`, for example a closed thickening `Metric.cthickening δ s` with `δ > 0`:
multiply an approximant by a smooth cutoff with values in `[0, 1]` that equals `1` on `s` and has
topological support in `t`. Multiplying by the cutoff does not increase the distance to the
function, which is unchanged by it.

Such support control is what is needed to pass a statement about an operator off the support of
its argument from smooth functions to all of `Lᵖ`.
-/

public section

open MeasureTheory Set Topology
open scoped ContDiff

namespace MeasureTheory.MemLp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- A function in `Lᵖ`, `1 ≤ p < ∞`, vanishing almost everywhere off a closed set `s` is the
`Lᵖ` limit of smooth compactly supported functions supported in `t`, for any neighbourhood `t`
of `s`. -/
theorem exist_contDiff_tsupport_subset_eLpNorm_sub_le {p : ENNReal} (hp : p ≠ ⊤) (hp₁ : 1 ≤ p)
    {f : E → F} (hf : MemLp f p μ) {s t : Set E} (hs : IsClosed s) (ht : t ∈ 𝓝ˢ s)
    (hfs : ∀ᵐ y ∂μ, y ∉ s → f y = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ t ∧
      eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  obtain ⟨u, hu, hsu, hut⟩ := normal_exists_closure_subset hs isOpen_interior
    (subset_interior_iff_mem_nhdsSet.2 ht)
  obtain ⟨θ, hθ, hθr, hθs, hθ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hu hs hsu
  obtain ⟨g, hgc, hg, hfg⟩ := hf.exist_eLpNorm_sub_le hp hp₁ hε
  refine ⟨fun y => θ y • g y, hgc.smul_left, hθ.smul hg, (tsupport_smul_subset_left _ _).trans
    (by rw [tsupport, hθs]; exact hut.trans interior_subset), (eLpNorm_mono_ae
      (hf.aestronglyMeasurable.sub (hθ.continuous.smul hg.continuous).aestronglyMeasurable)
      ?_).trans hfg⟩
  filter_upwards [hfs] with y hy
  have h01 := hθr (mem_range_self y)
  by_cases hys : y ∈ s
  · simp [(hθ1 y).1 hys]
  · simpa [hy hys, norm_smul, abs_of_nonneg h01.1] using
      mul_le_of_le_one_left (norm_nonneg (g y)) h01.2

end MeasureTheory.MemLp
