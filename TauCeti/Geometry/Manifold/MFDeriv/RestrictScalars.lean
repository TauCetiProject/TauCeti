/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Tangent.Space
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Restricting the scalars of manifold derivatives

Let `E` and `E'` be normed spaces over two fields `𝕜` and `𝕜'`, compatibly: for instance `𝕜'` is a
normed algebra over `𝕜` and the actions form scalar towers. A boundaryless model `I` over `𝕜'` and
its scalar restriction `I.restrictScalars 𝕜` have the same coordinate maps and use the same charted
space. This file shows that a map which is
differentiable for boundaryless models over `𝕜'` is differentiable for their scalar restrictions
over `𝕜`, and that its derivative for the scalar restrictions is its derivative for the models over
`𝕜'` with scalars restricted to `𝕜`. The proofs follow `ContMDiffWithinAt.restrictScalars` and its
companions in `TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars`: rewrite the extended charts
with `ModelWithCorners.extChartAt_restrictScalars` and restrict the scalars of the derivative in
charts. The derivative comparisons and the differentiability criteria are the manifold versions of
those in `Mathlib.Analysis.Calculus.FDeriv.RestrictScalars`: `HasFDerivWithinAt.restrictScalars`,
`HasFDerivAt.restrictScalars`, `HasFDerivWithinAt.of_restrictScalars`,
`hasFDerivAt_of_restrictScalars`, `DifferentiableWithinAt.restrictScalars_fderivWithin`,
`DifferentiableAt.fderiv_restrictScalars`, `differentiableWithinAt_iff_restrictScalars` and
`differentiableAt_iff_restrictScalars`.

The tangent spaces `TangentSpace I x` and `TangentSpace (I.restrictScalars 𝕜) x` are both
definitionally the model space `E`, but their module instances are over different fields: the
second is only a `𝕜`-module. The derivative comparisons are stated with
`ContinuousLinearMap.restrictScalarsTangent` from
`TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Tangent.Space`, which turns a
`𝕜'`-linear map between tangent spaces for `I` and `I'` into the same map, `𝕜`-linear between the
tangent spaces for their scalar restrictions. Like `ContinuousLinearMap.restrictScalars`, the
derivative comparisons need only the scalar compatibility condition `LinearMap.CompatibleSMul`,
which scalar towers provide; in charts they use
`TauCeti.hasFDerivAtFilter_restrictScalars_iff`. The comparison of the derivatives of inverse
charts needs this scalar compatibility condition as well, and of the manifold structures only the
`C¹` structure `IsManifold I 1 M` for the model over `𝕜'`. The tangent coordinate changes of the
two models are compared in
`TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Tangent.CoordChange`.

The main example is a holomorphic map between complex manifolds modelled on `𝓘(ℂ, E)` and
`𝓘(ℂ, E')`: its real derivative is its complex derivative regarded as an `ℝ`-linear map.

For the self models, at a point where a map is differentiable over the larger field, the fibrewise
linear equivalence `TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv` intertwines its manifold and
vector-valued derivatives over the two fields.

## Main results

* `TauCeti.hasMFDerivWithinAt_restrictScalars_iff`, `TauCeti.hasMFDerivAt_restrictScalars_iff`:
  the scalar restriction of a `𝕜'`-linear map is a derivative for the scalar restrictions of
  boundaryless models over `𝕜'` exactly when the map is a derivative for the models over `𝕜'`.
* `HasMFDerivWithinAt.restrictScalars`, `HasMFDerivAt.restrictScalars`: the scalar restriction of a
  derivative for boundaryless models over `𝕜'` is a derivative for their scalar restrictions.
* `MDifferentiableWithinAt.restrictScalars`, `MDifferentiableAt.restrictScalars`,
  `MDifferentiableOn.restrictScalars`, `MDifferentiable.restrictScalars`: differentiability for
  boundaryless models over `𝕜'` implies differentiability for their scalar restrictions to `𝕜`.
* `HasMFDerivWithinAt.of_restrictScalars`, `HasMFDerivAt.of_restrictScalars`: conversely, a
  `𝕜'`-linear map whose scalar restriction is a derivative for the scalar restrictions is a
  derivative for the models over `𝕜'`.
* `MDifferentiableWithinAt.restrictScalars_mfderivWithin` and
  `MDifferentiableAt.mfderiv_restrictScalars`: at a point where the map is differentiable for the
  models over `𝕜'` (within the set, for the first, which also needs a set with unique derivatives
  for the scalar restriction of the source model, `UniqueMDiffWithinAt (I.restrictScalars 𝕜) s x`),
  the derivative for the scalar restrictions is the scalar restriction of the derivative for the
  models over `𝕜'`.
* `TauCeti.mdifferentiableWithinAt_iff_restrictScalars` (for a set with
  `UniqueMDiffWithinAt (I.restrictScalars 𝕜) s x`) and
  `TauCeti.mdifferentiableAt_iff_restrictScalars`: a map differentiable for the scalar
  restrictions is differentiable for the models over `𝕜'` exactly when its derivative for the
  scalar restrictions is the scalar restriction of a `𝕜'`-linear map.
* `TauCeti.injective_mfderiv_restrictScalars`, `TauCeti.injective_mvfderiv_restrictScalars`,
  `MDifferentiableAt.injective_mfderiv_restrictScalars_iff`,
  `MDifferentiableAt.injective_mvfderiv_restrictScalars_iff`: if the derivative for boundaryless
  models over `𝕜'` is injective, so is the derivative for their scalar restrictions, and at a point
  where the map is differentiable for the models over `𝕜'`, injectivity of the derivatives over `𝕜`
  and over `𝕜'` are equivalent.
* `ModelWithCorners.mfderivWithin_extChartAt_symm_smul`: for a boundaryless model `I` over `𝕜'`,
  the scalar compatibility condition `LinearMap.CompatibleSMul E E 𝕜 𝕜'` and a manifold with
  `IsManifold I 1 M`, the derivative for `I.restrictScalars 𝕜` of the inverse of a chart at points
  of the chart target, read in the model spaces, is `𝕜'`-linear.
  `TauCeti.mfderivWithin_extChartAt_symm_smul` states this for a manifold charted by `E` with the
  self models `𝓘(𝕜', E)` and `𝓘(𝕜, E)`, whose tangent spaces are `E`, without the model casts,
  as the commutation of the derivative with `c • ContinuousLinearMap.id 𝕜 E`.
* `MDifferentiableAt.mfderiv_modelWithCornersSelf_restrictScalars_apply`: for the self models, at a
  point where the map is differentiable over the larger field, its derivatives over the two fields
  agree on every vector.
* `MDifferentiableAt.mfderiv_restrictScalarsSelf_apply` and
  `MDifferentiableAt.mvfderiv_restrictScalarsSelf_apply`: for the self models, at a point where the
  map is differentiable over the larger field, its derivatives over the two fields agree through
  `TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv`.
-/

public section

open Set
open scoped Manifold

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace 𝕜' E']

section Boundaryless

variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜' E H} {I' : ModelWithCorners 𝕜' E' H'} [I.Boundaryless] [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N] {f : M → N} {s : Set M} {x : M}

variable (𝕜)

/- As for `ContinuousLinearMap.restrictScalars`, the derivative comparisons only need `𝕜`-scalars to
commute with `𝕜'`-linear maps; scalar towers provide this. The derivative of a map is the same
`o`-condition over either field. -/
variable [LinearMap.CompatibleSMul E E' 𝕜 𝕜']

/-- For boundaryless models over `𝕜'`, the scalar restriction `f'.restrictScalarsTangent 𝕜` of a
`𝕜'`-linear map `f'` is a derivative of `f` within a set at a point for the scalar restrictions to
`𝕜` if and only if `f'` is a derivative of `f` within that set at that point for the models over
`𝕜'`: in charts, both say that `f'` satisfies the same `o`-condition. -/
theorem TauCeti.hasMFDerivWithinAt_restrictScalars_iff
    {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)} :
    HasMFDerivWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x
        (f'.restrictScalarsTangent 𝕜) ↔ HasMFDerivWithinAt I I' f s x f' := by
  rw [HasMFDerivWithinAt,
    ContinuousLinearMap.tangentSpaceCastModel_comp_restrictScalarsTangent_comp]
  simp only [writtenInExtChartAt, ModelWithCorners.extChartAt_restrictScalars,
    ModelWithCorners.coe_restrictScalars]
  exact and_congr_right' (TauCeti.hasFDerivAtFilter_restrictScalars_iff 𝕜)

/-- For boundaryless models over `𝕜'`, the scalar restriction `f'.restrictScalarsTangent 𝕜` of a
`𝕜'`-linear map `f'` is a derivative of `f` at a point for the scalar restrictions to `𝕜` if and
only if `f'` is a derivative of `f` at that point for the models over `𝕜'`. -/
theorem TauCeti.hasMFDerivAt_restrictScalars_iff
    {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)} :
    HasMFDerivAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x (f'.restrictScalarsTangent 𝕜) ↔
      HasMFDerivAt I I' f x f' := by
  simpa only [hasMFDerivWithinAt_univ] using
    TauCeti.hasMFDerivWithinAt_restrictScalars_iff 𝕜 (s := univ)

/-- If `f'` is a derivative of `f` within a set at a point for boundaryless models over `𝕜'`, then
its scalar restriction `f'.restrictScalarsTangent 𝕜` is a derivative of `f` within that set at that
point for their scalar restrictions to `𝕜`. -/
theorem HasMFDerivWithinAt.restrictScalars {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    (h : HasMFDerivWithinAt I I' f s x f') :
    HasMFDerivWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x
      (f'.restrictScalarsTangent 𝕜) :=
  (TauCeti.hasMFDerivWithinAt_restrictScalars_iff 𝕜).2 h

/-- If `f'` is a derivative of `f` at a point for boundaryless models over `𝕜'`, then its scalar
restriction `f'.restrictScalarsTangent 𝕜` is a derivative of `f` at that point for their scalar
restrictions to `𝕜`. -/
theorem HasMFDerivAt.restrictScalars {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    (h : HasMFDerivAt I I' f x f') :
    HasMFDerivAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x (f'.restrictScalarsTangent 𝕜) :=
  (TauCeti.hasMFDerivAt_restrictScalars_iff 𝕜).2 h

/-- A map which is differentiable within a set at a point for boundaryless models over `𝕜'` is
differentiable within that set at that point for their scalar restrictions to `𝕜`. -/
theorem MDifferentiableWithinAt.restrictScalars (h : MDifferentiableWithinAt I I' f s x) :
    MDifferentiableWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x :=
  (h.hasMFDerivWithinAt.restrictScalars 𝕜).mdifferentiableWithinAt

/-- A map which is differentiable at a point for boundaryless models over `𝕜'` is differentiable at
that point for their scalar restrictions to `𝕜`. -/
theorem MDifferentiableAt.restrictScalars (h : MDifferentiableAt I I' f x) :
    MDifferentiableAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x :=
  (h.hasMFDerivAt.restrictScalars 𝕜).mdifferentiableAt

/-- A map which is differentiable on a set for boundaryless models over `𝕜'` is differentiable on
that set for their scalar restrictions to `𝕜`. -/
theorem MDifferentiableOn.restrictScalars (h : MDifferentiableOn I I' f s) :
    MDifferentiableOn (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s :=
  fun x hx ↦ (h x hx).restrictScalars 𝕜

/-- A map which is differentiable for boundaryless models over `𝕜'` is differentiable for their
scalar restrictions to `𝕜`. For instance, a holomorphic map between complex manifolds is real
differentiable. -/
theorem MDifferentiable.restrictScalars (h : MDifferentiable I I' f) :
    MDifferentiable (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f :=
  fun x ↦ (h x).restrictScalars 𝕜

/-- If the scalar restriction `f'.restrictScalarsTangent 𝕜` of a `𝕜'`-linear map `f'` is a
derivative of `f` within a set at a point for the scalar restrictions to `𝕜` of boundaryless models
over `𝕜'`, then `f'` is a derivative of `f` within that set at that point for the models over `𝕜'`.
This is the converse of `HasMFDerivWithinAt.restrictScalars`. -/
theorem HasMFDerivWithinAt.of_restrictScalars
    {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    (h : HasMFDerivWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x
      (f'.restrictScalarsTangent 𝕜)) :
    HasMFDerivWithinAt I I' f s x f' :=
  (TauCeti.hasMFDerivWithinAt_restrictScalars_iff 𝕜).1 h

/-- If the scalar restriction `f'.restrictScalarsTangent 𝕜` of a `𝕜'`-linear map `f'` is a
derivative of `f` at a point for the scalar restrictions to `𝕜` of boundaryless models over `𝕜'`,
then `f'` is a derivative of `f` at that point for the models over `𝕜'`. This is the converse of
`HasMFDerivAt.restrictScalars`. -/
theorem HasMFDerivAt.of_restrictScalars {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    (h : HasMFDerivAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x
      (f'.restrictScalarsTangent 𝕜)) :
    HasMFDerivAt I I' f x f' :=
  (TauCeti.hasMFDerivAt_restrictScalars_iff 𝕜).1 h

/-- At a point where `f` is differentiable within a set for boundaryless models over `𝕜'`, and
where the set has unique derivatives for their scalar restrictions to `𝕜`, the derivative of `f`
within the set for the scalar restrictions is the scalar restriction of its derivative for the
models over `𝕜'`. -/
theorem MDifferentiableWithinAt.restrictScalars_mfderivWithin
    (h : MDifferentiableWithinAt I I' f s x)
    (hs : UniqueMDiffWithinAt (I.restrictScalars 𝕜) s x) :
    (mfderivWithin I I' f s x).restrictScalarsTangent 𝕜 =
      mfderivWithin (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x :=
  ((h.hasMFDerivWithinAt.restrictScalars 𝕜).mfderivWithin hs).symm

/-- At a point where `f` is differentiable for boundaryless models over `𝕜'`, the derivative of `f`
for their scalar restrictions to `𝕜` is the scalar restriction of its derivative for the models
over `𝕜'`. For instance, the real derivative of a holomorphic map is its complex derivative. -/
theorem MDifferentiableAt.mfderiv_restrictScalars (h : MDifferentiableAt I I' f x) :
    mfderiv (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x =
      (mfderiv I I' f x).restrictScalarsTangent 𝕜 :=
  (h.hasMFDerivAt.restrictScalars 𝕜).mfderiv

/-- Let `f` be differentiable within a set at a point for the scalar restrictions to `𝕜` of
boundaryless models over `𝕜'`, where the set has unique derivatives for the scalar restrictions.
Then `f` is differentiable within the set at the point for the models over `𝕜'` if and only if
its derivative for the scalar restrictions is the scalar restriction of a `𝕜'`-linear map. -/
theorem TauCeti.mdifferentiableWithinAt_iff_restrictScalars
    (hf : MDifferentiableWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x)
    (hs : UniqueMDiffWithinAt (I.restrictScalars 𝕜) s x) :
    MDifferentiableWithinAt I I' f s x ↔
      ∃ g' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x),
        g'.restrictScalarsTangent 𝕜 =
          mfderivWithin (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x := by
  refine ⟨fun h ↦ ⟨_, h.restrictScalars_mfderivWithin 𝕜 hs⟩, fun ⟨g', hg'⟩ ↦ ?_⟩
  have hf' := hf.hasMFDerivWithinAt
  rw [← hg'] at hf'
  exact (hf'.of_restrictScalars 𝕜).mdifferentiableWithinAt

/-- Let `f` be differentiable at a point for the scalar restrictions to `𝕜` of boundaryless models
over `𝕜'`. Then `f` is differentiable at the point for the models over `𝕜'` if and only if its
derivative for the scalar restrictions is the scalar restriction of a `𝕜'`-linear map. -/
theorem TauCeti.mdifferentiableAt_iff_restrictScalars
    (hf : MDifferentiableAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x) :
    MDifferentiableAt I I' f x ↔
      ∃ g' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x),
        g'.restrictScalarsTangent 𝕜 = mfderiv (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x := by
  simpa only [← mdifferentiableWithinAt_univ, ← mfderivWithin_univ] using
    TauCeti.mdifferentiableWithinAt_iff_restrictScalars 𝕜 hf.mdifferentiableWithinAt
      (uniqueMDiffWithinAt_univ _)

/-- At a point where `f` is differentiable for boundaryless models over `𝕜'`, its derivative for
their scalar restrictions to `𝕜` is injective if and only if its derivative for the models over
`𝕜'` is injective. -/
theorem MDifferentiableAt.injective_mfderiv_restrictScalars_iff (h : MDifferentiableAt I I' f x) :
    Function.Injective (mfderiv (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x) ↔
      Function.Injective (mfderiv I I' f x) := by
  rw [h.mfderiv_restrictScalars 𝕜, ContinuousLinearMap.injective_restrictScalarsTangent_iff]

/-- If the derivative of `f` at `x` for boundaryless models over `𝕜'` is injective, then so is its
derivative for their scalar restrictions to `𝕜`. For instance, if the complex derivative of a map
between complex manifolds is injective at a point, so is its real derivative there. Where `f` is
not differentiable over `𝕜'` its derivative over `𝕜'` is `0`, and injectivity of that derivative
forces the tangent space to be trivial. -/
theorem TauCeti.injective_mfderiv_restrictScalars
    (hinj : Function.Injective (mfderiv I I' f x)) :
    Function.Injective (mfderiv (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x) := by
  by_cases h : MDifferentiableAt I I' f x
  · exact (h.injective_mfderiv_restrictScalars_iff 𝕜).2 hinj
  · rw [mfderiv_zero_of_not_mdifferentiableAt h,
      ← ContinuousLinearMap.injective_restrictScalarsTangent_iff (𝕜 := 𝕜),
      ContinuousLinearMap.restrictScalarsTangent_zero] at hinj
    -- The zero map on the tangent space for the scalar restrictions is injective, so that tangent
    -- space is trivial.
    intro v w _
    exact hinj (by rw [zero_apply, zero_apply])

/-- At a point where a vector-valued map `g : M → E'` is differentiable for a boundaryless model
`I` over `𝕜'`, its vector-valued derivative for the scalar restriction of `I` to `𝕜` is injective if
and only if its vector-valued derivative for `I` is injective. For instance, for a holomorphic map
into a complex normed space, the real derivative at `x` is injective exactly when the complex
derivative at `x` is. -/
theorem MDifferentiableAt.injective_mvfderiv_restrictScalars_iff {g : M → E'}
    (h : MDifferentiableAt I 𝓘(𝕜', E') g x) :
    Function.Injective (mvfderiv (I.restrictScalars 𝕜) g x) ↔
      Function.Injective (mvfderiv I g x) := by
  have H := h.injective_mfderiv_restrictScalars_iff 𝕜
  rw [modelWithCornersSelf_restrictScalars] at H
  simpa only [TauCeti.injective_mvfderiv_iff] using H

/-- If the vector-valued derivative of `g : M → E'` at `x` for a boundaryless model `I` over `𝕜'` is
injective, then so is its vector-valued derivative for the scalar restriction of `I` to `𝕜`. No
differentiability is needed: this is `TauCeti.injective_mfderiv_restrictScalars` for the target
model `𝓘(𝕜', E')`. For instance, if the complex derivative of a map into a complex normed space is
injective at a point, so is its real derivative there. -/
theorem TauCeti.injective_mvfderiv_restrictScalars {g : M → E'}
    (hinj : Function.Injective (mvfderiv I g x)) :
    Function.Injective (mvfderiv (I.restrictScalars 𝕜) g x) := by
  rw [TauCeti.injective_mvfderiv_iff] at hinj ⊢
  have H := TauCeti.injective_mfderiv_restrictScalars 𝕜 hinj
  rwa [modelWithCornersSelf_restrictScalars] at H

end Boundaryless

namespace ModelWithCorners

variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜' E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [LinearMap.CompatibleSMul E E 𝕜 𝕜']

variable (𝕜)

/-- On the target of the chart at `x`, the derivative over `𝕜` of the inverse of the chart for the
scalar restriction `I.restrictScalars 𝕜` of a boundaryless model `I` over `𝕜'`, read in the model
spaces through `tangentSpaceCastModel`, is `𝕜'`-linear: it is the derivative over `𝕜'` of the
inverse of the chart for `I`, with scalars restricted to `𝕜`. -/
theorem mfderivWithin_extChartAt_symm_smul {x : M} {z : E}
    (hz : z ∈ (extChartAt (I.restrictScalars 𝕜) x).target) (c : 𝕜') (w : E) :
    tangentSpaceCastModel (I.restrictScalars 𝕜) _
        (mfderivWithin 𝓘(𝕜, E) (I.restrictScalars 𝕜) (extChartAt (I.restrictScalars 𝕜) x).symm
          (range (I.restrictScalars 𝕜)) z ((tangentSpaceCastModel 𝓘(𝕜, E) z).symm (c • w))) =
      c • tangentSpaceCastModel (I.restrictScalars 𝕜) _
        (mfderivWithin 𝓘(𝕜, E) (I.restrictScalars 𝕜) (extChartAt (I.restrictScalars 𝕜) x).symm
          (range (I.restrictScalars 𝕜)) z ((tangentSpaceCastModel 𝓘(𝕜, E) z).symm w)) := by
  rw [extChartAt_restrictScalars] at hz ⊢
  have hs : UniqueMDiffWithinAt (𝓘(𝕜', E).restrictScalars 𝕜) (range I) z := by
    rw [I.range_eq_univ]
    exact uniqueMDiffWithinAt_univ _
  rw [coe_restrictScalars, ← modelWithCornersSelf_restrictScalars (𝕜 := 𝕜) (𝕜' := 𝕜'),
    ← (mdifferentiableWithinAt_extChartAt_symm hz).restrictScalars_mfderivWithin 𝕜 hs]
  -- Read in the model spaces, the scalar restriction of the derivative over `𝕜'` is
  -- `ContinuousLinearMap.restrictScalars` of a `𝕜'`-linear map.
  have key (v : E) := DFunLike.congr_fun
    (ContinuousLinearMap.tangentSpaceCastModel_comp_restrictScalarsTangent_comp 𝕜
      (mfderivWithin 𝓘(𝕜', E) I (extChartAt I x).symm (range I) z)) v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_restrictScalars'] at key
  simp only [key, map_smul]

end ModelWithCorners

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {x : M}

variable (𝕜)

variable [LinearMap.CompatibleSMul E E 𝕜 𝕜'] [IsManifold 𝓘(𝕜', E) 1 M]

/-- On the target of the chart at `x`, the derivative over `𝕜` of the inverse of the chart is
`𝕜'`-linear: it is the derivative over `𝕜'` with scalars restricted to `𝕜`. For instance, on a
complex manifold, regarded as a real manifold, the real derivative of the inverse of a chart
commutes with multiplication by `i`. This is `ModelWithCorners.mfderivWithin_extChartAt_symm_smul`
for the self models, whose tangent spaces are `E`. -/
theorem mfderivWithin_extChartAt_symm_smul {z : E}
    (hz : z ∈ (extChartAt 𝓘(𝕜, E) x).target) (c : 𝕜') (w : E) :
    -- `𝕜'` acts on `E →L[𝕜] E`: by `LinearMap.CompatibleSMul`, each `v ↦ d • v` is `𝕜`-linear.
    haveI : SMulCommClass 𝕜 𝕜' E := ⟨fun a d v ↦ by
      simpa only [LinearMap.smul_apply, LinearMap.id_apply] using
        (LinearMap.CompatibleSMul.map_smul (d • LinearMap.id (R := 𝕜') (M := E)) a v).symm⟩
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) (extChartAt 𝓘(𝕜, E) x).symm (range 𝓘(𝕜, E)) z
        ((c • ContinuousLinearMap.id 𝕜 E) w) =
      (c • ContinuousLinearMap.id 𝕜 E)
        (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) (extChartAt 𝓘(𝕜, E) x).symm (range 𝓘(𝕜, E)) z w) := by
  have h := 𝓘(𝕜', E).mfderivWithin_extChartAt_symm_smul 𝕜
    (by rwa [modelWithCornersSelf_restrictScalars]) c w
  rw [modelWithCornersSelf_restrictScalars] at h
  -- The statement feeds vectors of `E` to the self-model tangent spaces, which are `E` by
  -- definition, and applies `c • ContinuousLinearMap.id 𝕜 E` to tangent vectors. On these spaces
  -- `tangentSpaceCastModel 𝓘(𝕜, E)` and its inverse are the identity of `E`, so `h`, which reads
  -- the derivative through these casts, is the claim.
  exact h

end TauCeti

namespace MDifferentiableAt

variable (R : Type*) {A : Type*}
  [NontriviallyNormedField R] [NontriviallyNormedField A] [Algebra R A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace A E] [NormedSpace R E]
  [IsScalarTower R A E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace A F] [NormedSpace R F]
  [IsScalarTower R A F] {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- At a point where `f` is differentiable over the larger field `A`, its derivatives for the self
models over `R` and over `A` agree on every vector of `E`. For instance, the real derivative of a
holomorphic map between complex manifolds charted by complex vector spaces is its complex
derivative. -/
theorem mfderiv_modelWithCornersSelf_restrictScalars_apply {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(A, E) 𝓘(A, F) f x) (v : E) :
    mfderiv 𝓘(R, E) 𝓘(R, F) f x v = mfderiv 𝓘(A, E) 𝓘(A, F) f x v := by
  have h := DFunLike.congr_fun (hf.mfderiv_restrictScalars R) v
  rw [modelWithCornersSelf_restrictScalars, modelWithCornersSelf_restrictScalars] at h
  exact h.trans (ContinuousLinearMap.restrictScalarsTangent_apply _ _)

/-- At a point where `f` is differentiable over the larger field `A`, the native self-model fibre
comparison intertwines its derivatives over the two fields. -/
theorem mfderiv_restrictScalarsSelf_apply {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(A, E) 𝓘(A, F) f x)
    (v : RestrictScalars R A (TangentSpace 𝓘(A, E) x)) :
    TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (f x)
        ((RestrictScalars.addEquiv R A _).symm
          (mfderiv 𝓘(A, E) 𝓘(A, F) f x (RestrictScalars.addEquiv R A _ v))) =
      mfderiv 𝓘(R, E) 𝓘(R, F) f x
        (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R x v) := by
  rw [← ContinuousLinearMap.restrictScalarsTangent_tangentSpaceRestrictScalarsSelfLinearEquiv,
    ← hf.mfderiv_restrictScalars R, modelWithCornersSelf_restrictScalars,
    modelWithCornersSelf_restrictScalars]

/-- At a point where `f` is differentiable over the larger field `A`, its vector-valued
derivatives over the two fields agree through the native self-model fibre comparison. -/
theorem mvfderiv_restrictScalarsSelf_apply {f : M → F} {x : M}
    (hf : MDifferentiableAt 𝓘(A, E) 𝓘(A, F) f x)
    (v : RestrictScalars R A (TangentSpace 𝓘(A, E) x)) :
    mvfderiv 𝓘(R, E) f x (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R x v) =
      mvfderiv 𝓘(A, E) f x (RestrictScalars.addEquiv R A _ v) := by
  -- For a vector-space target, the model cast is the standard tangent-space identification.
  have h := congrArg (tangentSpaceCastModel 𝓘(R, F) (f x))
    (hf.mfderiv_restrictScalarsSelf_apply R v)
  simp only [TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv_apply,
    AddEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [mvfderiv, NormedSpace.fromTangentSpace,
    TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv_apply]
  rw [ContinuousLinearMap.comp_apply]
  exact h.symm

end MDifferentiableAt
