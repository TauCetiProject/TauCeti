/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Geometry.Manifold.SmoothApprox.Lp

/-!
# Smooth approximation in `Lᵖ` with control of the support

Mathlib's `MeasureTheory.MemLp.exist_eLpNorm_sub_le` approximates a function in `Lᵖ`, `p < ∞`, by
smooth compactly supported functions, with no control on where the approximants live. If the
function vanishes off a closed set `s`, the approximants can be taken to be supported in any
neighbourhood `t` of `s`, for example a closed thickening `Metric.cthickening δ s` with `δ > 0`.
This is the case of the model space `𝓘(ℝ, E)` of the manifold statement
`MeasureTheory.MemLp.exists_contMDiff_tsupport_subset_eLpNorm_sub_le`.

Such support control is what is needed to pass a statement about an operator off the support of
its argument from smooth functions to all of `Lᵖ`.
-/

public section

open MeasureTheory Set Topology
open scoped ContDiff Manifold

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
  obtain ⟨g, hgc, hgt, hfg⟩ := hf.exists_contMDiff_tsupport_subset_eLpNorm_sub_le 𝓘(ℝ, E) hp hp₁
    hs ht hfs (ENNReal.ofReal_pos.2 hε).ne'
  exact ⟨g, hgc, contMDiff_iff_contDiff.1 g.contMDiff, hgt, hfg⟩

end MeasureTheory.MemLp
