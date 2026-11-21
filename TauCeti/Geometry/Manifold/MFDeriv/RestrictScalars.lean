/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.TangentSpace
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
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

The tangent spaces `TangentSpace I x` and `TangentSpace (I.restrictScalars 𝕜) x` are both the model
space `E`, but they are distinct types carrying module structures over different fields. The
derivative comparisons are stated with `ContinuousLinearMap.restrictScalarsTangent` from
`TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.TangentSpace`, which turns a
`𝕜'`-linear map between tangent spaces for `I` and `I'` into the same map, `𝕜`-linear between the
tangent spaces for their scalar restrictions. Like `ContinuousLinearMap.restrictScalars`, the
derivative comparisons assume only `LinearMap.CompatibleSMul`, which scalar towers provide. The
tangent coordinate changes later in the file are for a manifold charted by `E` with the self models
`𝓘(𝕜', E)` and `𝓘(𝕜, E)`, and assume a normed algebra and scalar towers.

The main example is a holomorphic map between complex manifolds modelled on `𝓘(ℂ, E)` and
`𝓘(ℂ, E')`: its real derivative is its complex derivative regarded as an `ℝ`-linear map.
Likewise, on the overlap of two charts, the tangent coordinate changes of a complex manifold
modelled on `𝓘(ℂ, E)`, regarded as a real manifold modelled on `𝓘(ℝ, E)`, are its complex tangent
coordinate changes regarded as `ℝ`-linear maps.

For the self models, the fibrewise linear equivalence
`TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv` intertwines the manifold and vector-valued
derivatives over the two fields.

## Main results

* `HasMFDerivWithinAt.restrictScalars`, `HasMFDerivAt.restrictScalars`: the scalar restriction of a
  derivative for boundaryless models over `𝕜'` is a derivative for their scalar restrictions.
* `MDifferentiableWithinAt.restrictScalars`, `MDifferentiableAt.restrictScalars`,
  `MDifferentiableOn.restrictScalars`, `MDifferentiable.restrictScalars`: differentiability for
  boundaryless models over `𝕜'` implies differentiability for their scalar restrictions to `𝕜`.
* `HasMFDerivWithinAt.of_restrictScalars`, `HasMFDerivAt.of_restrictScalars`: conversely, a
  `𝕜'`-linear map whose scalar restriction is a derivative for the scalar restrictions is a
  derivative for the models over `𝕜'`.
* `MDifferentiableWithinAt.restrictScalars_mfderivWithin` (for a set with unique derivatives for
  the scalar restriction of the source model, `UniqueMDiffWithinAt (I.restrictScalars 𝕜) s x`) and
  `MDifferentiableAt.mfderiv_restrictScalars`: the derivative for the scalar restrictions is the
  scalar restriction of the derivative for the models over `𝕜'`.
* `TauCeti.mdifferentiableWithinAt_iff_restrictScalars` (for a set with
  `UniqueMDiffWithinAt (I.restrictScalars 𝕜) s x`) and
  `TauCeti.mdifferentiableAt_iff_restrictScalars`: a map differentiable for the scalar
  restrictions is differentiable for the models over `𝕜'` exactly when its derivative for the
  scalar restrictions is the scalar restriction of a `𝕜'`-linear map.
* `TauCeti.injective_mfderiv_restrictScalars`,
  `MDifferentiableAt.injective_mfderiv_restrictScalars_iff`,
  `MDifferentiableAt.injective_mvfderiv_restrictScalars_iff`: if the derivative for boundaryless
  models over `𝕜'` is injective, so is the derivative for their scalar restrictions, and at a point
  of differentiability injectivity of the derivatives over `𝕜` and over `𝕜'` are equivalent.
* `TauCeti.tangentCoordChange_restrictScalars`: for a manifold charted by `E` with the self models,
  on the overlap of two charts the tangent coordinate change for `𝓘(𝕜, E)` is that for `𝓘(𝕜', E)`
  with scalars restricted to `𝕜`; in particular it is `𝕜'`-linear there
  (`TauCeti.tangentCoordChange_smul`), and so is the derivative for `𝓘(𝕜, E)` of the inverse of a
  chart at points of the chart target (`TauCeti.mfderivWithin_extChartAt_symm_smul`).
* `MDifferentiableAt.mfderiv_restrictScalarsSelf_apply` and
  `MDifferentiableAt.mvfderiv_restrictScalarsSelf_apply`: for the self models, the derivatives
  over the two fields agree through `TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv`.
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

/-- If `f'` is a derivative of `f` within a set at a point for boundaryless models over `𝕜'`, then
its scalar restriction `f'.restrictScalarsTangent 𝕜` is a derivative of `f` within that set at that
point for their scalar restrictions to `𝕜`. -/
theorem HasMFDerivWithinAt.restrictScalars {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    (h : HasMFDerivWithinAt I I' f s x f') :
    HasMFDerivWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x
      (f'.restrictScalarsTangent 𝕜) := by
  rw [HasMFDerivWithinAt,
    ContinuousLinearMap.tangentSpaceCastModel_comp_restrictScalarsTangent_comp]
  simp only [writtenInExtChartAt, ModelWithCorners.extChartAt_restrictScalars,
    ModelWithCorners.coe_restrictScalars]
  refine ⟨h.1, .of_isLittleO ?_⟩
  simpa only [writtenInExtChartAt, ContinuousLinearMap.coe_restrictScalars'] using h.2.isLittleO

/-- If `f'` is a derivative of `f` at a point for boundaryless models over `𝕜'`, then its scalar
restriction `f'.restrictScalarsTangent 𝕜` is a derivative of `f` at that point for their scalar
restrictions to `𝕜`. -/
theorem HasMFDerivAt.restrictScalars {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    (h : HasMFDerivAt I I' f x f') :
    HasMFDerivAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x (f'.restrictScalarsTangent 𝕜) :=
  hasMFDerivWithinAt_univ.mp (h.hasMFDerivWithinAt.restrictScalars 𝕜)

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
    HasMFDerivWithinAt I I' f s x f' := by
  have hf := h.2
  rw [ContinuousLinearMap.tangentSpaceCastModel_comp_restrictScalarsTangent_comp] at hf
  simp only [writtenInExtChartAt, ModelWithCorners.extChartAt_restrictScalars,
    ModelWithCorners.coe_restrictScalars] at hf
  refine ⟨h.1, .of_isLittleO ?_⟩
  simpa only [writtenInExtChartAt, ContinuousLinearMap.coe_restrictScalars'] using hf.isLittleO

/-- If the scalar restriction `f'.restrictScalarsTangent 𝕜` of a `𝕜'`-linear map `f'` is a
derivative of `f` at a point for the scalar restrictions to `𝕜` of boundaryless models over `𝕜'`,
then `f'` is a derivative of `f` at that point for the models over `𝕜'`. This is the converse of
`HasMFDerivAt.restrictScalars`. -/
theorem HasMFDerivAt.of_restrictScalars {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    (h : HasMFDerivAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x
      (f'.restrictScalarsTangent 𝕜)) :
    HasMFDerivAt I I' f x f' :=
  hasMFDerivWithinAt_univ.mp (h.hasMFDerivWithinAt.of_restrictScalars 𝕜)

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
  · rw [mfderiv_zero_of_not_mdifferentiableAt h] at hinj
    intro v w _
    exact hinj (a₁ := v) (a₂ := w) rfl

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

end Boundaryless

variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E] [IsScalarTower 𝕜 𝕜' E']

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace E' N] {f : M → N} {s : Set M} {x : M}

variable (𝕜)

namespace TauCeti

/-- On the overlap of the charts at `x` and `y`, the tangent coordinate change for the model over
`𝕜` is the tangent coordinate change for the model over `𝕜'`, with scalars restricted to `𝕜`: both
are the derivative of the same chart transition. For instance, the tangent coordinate changes of
a complex manifold, regarded as a real manifold, are complex linear. -/
theorem tangentCoordChange_restrictScalars [IsManifold 𝓘(𝕜', E) 1 M] [IsManifold 𝓘(𝕜, E) 1 M]
    {y z : M} (h : z ∈ (chartAt E x).source ∩ (chartAt E y).source) :
    tangentCoordChange 𝓘(𝕜, E) x y z = (tangentCoordChange 𝓘(𝕜', E) x y z).restrictScalars 𝕜 := by
  have h' : z ∈ (extChartAt 𝓘(𝕜', E) x).source ∩ (extChartAt 𝓘(𝕜', E) y).source := by
    simpa only [extChartAt_source] using h
  have h₁ := (hasFDerivWithinAt_tangentCoordChange h').restrictScalars 𝕜
  have h₂ := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(𝕜, E)) h'
  simp only [modelWithCornersSelf_coe, range_id] at h₁ h₂
  exact (h₂.hasFDerivAt Filter.univ_mem).unique (h₁.hasFDerivAt Filter.univ_mem)

/-- On the overlap of the charts at `x` and `y`, the tangent coordinate change for the model over
`𝕜` is `𝕜'`-linear. For instance, the real tangent coordinate changes of a complex manifold are
complex linear. -/
theorem tangentCoordChange_smul [IsManifold 𝓘(𝕜', E) 1 M] [IsManifold 𝓘(𝕜, E) 1 M] {y z : M}
    (h : z ∈ (chartAt E x).source ∩ (chartAt E y).source) (c : 𝕜') (w : E) :
    tangentCoordChange 𝓘(𝕜, E) x y z (c • w) = c • tangentCoordChange 𝓘(𝕜, E) x y z w := by
  rw [tangentCoordChange_restrictScalars 𝕜 (𝕜' := 𝕜') h, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

/-- On the target of the chart at `x`, the derivative over `𝕜` of the inverse of the chart is
`𝕜'`-linear: it is a tangent coordinate change. For instance, on a complex manifold, regarded as
a real manifold, the real derivative of the inverse of a chart commutes with multiplication by
`i`. -/
theorem mfderivWithin_extChartAt_symm_smul [IsManifold 𝓘(𝕜', E) 1 M]
    {z : E} (hz : z ∈ (extChartAt 𝓘(𝕜, E) x).target) (c : 𝕜') (w : E) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) (extChartAt 𝓘(𝕜, E) x).symm (range 𝓘(𝕜, E)) z
        ((c • ContinuousLinearMap.id 𝕜 E) w) =
      (c • ContinuousLinearMap.id 𝕜 E)
        (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) (extChartAt 𝓘(𝕜, E) x).symm (range 𝓘(𝕜, E)) z w) := by
  have : IsManifold 𝓘(𝕜, E) 1 M := IsManifold.restrictScalars 𝕜 (𝕜' := 𝕜') inferInstance
  have hy : (extChartAt 𝓘(𝕜, E) x).symm z ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(𝕜, E) x).map_target hz
  rw [← (extChartAt 𝓘(𝕜, E) x).right_inv hz, ← TangentBundle.symmL_trivializationAt hy,
    TangentBundle.symmL_trivializationAt_eq_core hy]
  exact tangentCoordChange_smul 𝕜 (𝕜' := 𝕜') ⟨hy, mem_chart_source E _⟩ c w

end TauCeti

namespace MDifferentiableAt

variable (R : Type*) {A : Type*}
  [NontriviallyNormedField R] [NontriviallyNormedField A] [Algebra R A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace A E] [NormedSpace R E]
  [IsScalarTower R A E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace A F] [NormedSpace R F]
  [IsScalarTower R A F] {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- The native self-model fibre comparison intertwines derivatives over the two fields. -/
theorem mfderiv_restrictScalarsSelf_apply {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(A, E) 𝓘(A, F) f x)
    (v : RestrictScalars R A (TangentSpace 𝓘(A, E) x)) :
    TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (f x)
        ((RestrictScalars.addEquiv R A _).symm
          (mfderiv 𝓘(A, E) 𝓘(A, F) f x (RestrictScalars.addEquiv R A _ v))) =
      mfderiv 𝓘(R, E) 𝓘(R, F) f x
        (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R x v) := by
  have H := DFunLike.congr_fun (hf.mfderiv_restrictScalars R)
    (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R x v)
  rw [modelWithCornersSelf_restrictScalars, modelWithCornersSelf_restrictScalars] at H
  rw [H]
  simp only [TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv_apply, AddEquiv.apply_symm_apply]
  -- Compare both sides in the model space `F`, where the scalar restriction of the derivative is
  -- `ContinuousLinearMap.restrictScalars`.
  apply (tangentSpaceCastModel 𝓘(R, F) (f x)).injective
  have hB := DFunLike.congr_fun
    (ContinuousLinearMap.tangentSpaceCastModel_comp_restrictScalarsTangent_comp R
      (mfderiv 𝓘(A, E) 𝓘(A, F) f x))
    (tangentSpaceCastModel 𝓘(A, E) x (RestrictScalars.addEquiv R A _ v))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at hB
  rw [modelWithCornersSelf_restrictScalars, modelWithCornersSelf_restrictScalars] at hB
  rw [ContinuousLinearEquiv.apply_symm_apply, hB]

/-- Vector-valued derivatives agree through the native self-model fibre comparison. -/
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
