/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Mean-zero smooth functions on a compact manifold

Given a finite measure `μ` on a compact manifold `M`, the smooth real-valued functions on `M`
whose integral against `μ` vanishes form the `ℝ`-submodule
`TauCeti.Manifold.meanZeroSmoothFunctions I M μ`, defined as the kernel of integration against `μ`
via `ContinuousMap.integralPositiveLinearMap` and `ContMDiffMap.toContinuousMapLinearMap`.

## Main definitions

* `TauCeti.Manifold.meanZeroSmoothFunctions`: the submodule of smooth functions on `M` with
  vanishing integral against `μ`.

## Main results

* `TauCeti.Manifold.mem_meanZeroSmoothFunctions_iff`: membership characterization in
  `meanZeroSmoothFunctions I M μ`.
-/

public section

open MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] (μ : Measure M) [IsFiniteMeasure μ]

/-- The submodule of smooth functions on `M` with vanishing integral against `μ`. -/
def meanZeroSmoothFunctions : Submodule ℝ C^∞⟮I, M; ℝ⟯ :=
  LinearMap.ker
    ((ContinuousMap.integralPositiveLinearMap μ).toLinearMap.comp
      ContMDiffMap.toContinuousMapLinearMap)

variable {I M μ}

/-- A smooth function belongs to `meanZeroSmoothFunctions I M μ` exactly when its integral
against `μ` vanishes. -/
@[simp]
theorem mem_meanZeroSmoothFunctions_iff {u : C^∞⟮I, M; ℝ⟯} :
    u ∈ meanZeroSmoothFunctions I M μ ↔ ∫ x, u x ∂μ = 0 := by
  simp [meanZeroSmoothFunctions, ContinuousMap.integralPositiveLinearMap_apply]

end TauCeti.Manifold
