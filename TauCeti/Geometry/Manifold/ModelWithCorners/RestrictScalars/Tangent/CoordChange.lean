/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart

/-!
# Tangent coordinate changes after restriction of scalars

Let `E` be a normed space over two fields `𝕜` and `𝕜'`, compatibly: every `𝕜'`-linear endomorphism
of `E` is `𝕜`-linear (`LinearMap.CompatibleSMul E E 𝕜 𝕜'`), as scalar towers provide. A boundaryless
model `I` over `𝕜'` and its scalar restriction `I.restrictScalars 𝕜` have the same extended charts
(`ModelWithCorners.extChartAt_restrictScalars`), so on the overlap of two charts their tangent
coordinate changes are the derivatives of the same chart transition over the two fields. For a
manifold with `C¹` structures `IsManifold I 1 M` and `IsManifold (I.restrictScalars 𝕜) 1 M`, the
tangent coordinate change for `I.restrictScalars 𝕜` is therefore the one for `I` with scalars
restricted to `𝕜`, and in particular it is `𝕜'`-linear.

The main example is a complex manifold modelled on a boundaryless model `I`, regarded as a real
manifold modelled on `I.restrictScalars ℝ`: its real tangent coordinate changes are complex linear.
For the self models, `modelWithCornersSelf_restrictScalars` identifies `𝓘(𝕜', E).restrictScalars 𝕜`
with `𝓘(𝕜, E)`.

## Main results

* `ModelWithCorners.tangentCoordChange_restrictScalars`: on the overlap of two charts, the tangent
  coordinate change for `I.restrictScalars 𝕜` is that for `I` with scalars restricted to `𝕜`.
* `ModelWithCorners.tangentCoordChange_smul`: on the overlap of two charts, the tangent coordinate
  change for `I.restrictScalars 𝕜` is `𝕜'`-linear.
* `TauCeti.tangentCoordChange_modelWithCornersSelf_restrictScalars_apply`: for the self models,
  the tangent coordinate changes for `𝓘(𝕜, E)` and `𝓘(𝕜', E)` agree on chart overlaps.
-/

public section

open scoped Manifold

namespace ModelWithCorners

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [LinearMap.CompatibleSMul E E 𝕜 𝕜']
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜' E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [IsManifold (I.restrictScalars 𝕜) 1 M]

variable (𝕜)

/-- On the overlap of the charts at `x` and `y`, the tangent coordinate change for the scalar
restriction `I.restrictScalars 𝕜` of a boundaryless model `I` over `𝕜'` is the tangent coordinate
change for `I`, with scalars restricted to `𝕜`: both are the derivative of the same chart
transition. For instance, the tangent coordinate changes of a complex manifold, regarded as a real
manifold, are complex linear. -/
theorem tangentCoordChange_restrictScalars {x y z : M}
    (h : z ∈ (chartAt H x).source ∩ (chartAt H y).source) :
    tangentCoordChange (I.restrictScalars 𝕜) x y z =
      (tangentCoordChange I x y z).restrictScalars 𝕜 := by
  have h' : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source := by
    simpa only [extChartAt_source] using h
  have h₁ := hasFDerivWithinAt_tangentCoordChange h'
  have h₂ := hasFDerivWithinAt_tangentCoordChange (I := I.restrictScalars 𝕜)
    (by simpa only [extChartAt_restrictScalars] using h')
  simp only [extChartAt_restrictScalars, coe_restrictScalars, I.range_eq_univ,
    hasFDerivWithinAt_univ] at h₁ h₂
  exact h₂.unique ((TauCeti.hasFDerivAtFilter_restrictScalars_iff 𝕜).2 h₁)

/-- On the overlap of the charts at `x` and `y`, the tangent coordinate change for the scalar
restriction `I.restrictScalars 𝕜` of a boundaryless model `I` over `𝕜'` is `𝕜'`-linear. -/
theorem tangentCoordChange_smul {x y z : M}
    (h : z ∈ (chartAt H x).source ∩ (chartAt H y).source) (c : 𝕜') (w : E) :
    tangentCoordChange (I.restrictScalars 𝕜) x y z (c • w) =
      c • tangentCoordChange (I.restrictScalars 𝕜) x y z w := by
  rw [I.tangentCoordChange_restrictScalars 𝕜 h, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

end ModelWithCorners

namespace TauCeti

variable (𝕜 : Type*) {𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [LinearMap.CompatibleSMul E E 𝕜 𝕜'] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜', E) 1 M] [IsManifold 𝓘(𝕜, E) 1 M]

/-- For the self models, on the overlap of the charts at `x` and `y`, the tangent coordinate
change for `𝓘(𝕜, E)` is the one for `𝓘(𝕜', E)`. For instance, the real tangent coordinate changes
of a complex manifold are the complex ones. -/
theorem tangentCoordChange_modelWithCornersSelf_restrictScalars_apply {x y z : M}
    (h : z ∈ (chartAt E x).source ∩ (chartAt E y).source) (v : E) :
    tangentCoordChange 𝓘(𝕜, E) x y z v = tangentCoordChange 𝓘(𝕜', E) x y z v := by
  have : IsManifold (𝓘(𝕜', E).restrictScalars 𝕜) 1 M := by
    rwa [modelWithCornersSelf_restrictScalars]
  simpa only [modelWithCornersSelf_restrictScalars, ContinuousLinearMap.coe_restrictScalars'] using
    congrArg (fun L : E →L[𝕜] E ↦ L v) (𝓘(𝕜', E).tangentCoordChange_restrictScalars 𝕜 h)

end TauCeti
