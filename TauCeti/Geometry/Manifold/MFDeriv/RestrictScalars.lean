/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Restricting the scalars of manifold derivatives

Let `𝕜'` be a normed algebra over `𝕜`, and let `I` and `I'` be boundaryless models whose
vector spaces are normed spaces over both fields, compatibly. A manifold with model `I` has
unchanged charts for `I.restrictScalars 𝕜`. Differentiability over `𝕜'` implies differentiability
over `𝕜`, and its derivative over `𝕜` is its derivative over `𝕜'` with scalars restricted.
This applies to product models and continuous linear changes of model coordinates as well as
self-models.

The tangent spaces for the two models are distinct types carrying module structures over different
fields. Derivative comparisons therefore read both derivatives in the model spaces through
`tangentSpaceCastModel`, as in `HasMFDerivWithinAt`. Conversely, a supplied `𝕜'`-linear map is a
derivative whenever its scalar restriction is a derivative over `𝕜`; mere real differentiability
does not imply complex differentiability.

In particular, the real derivative of a holomorphic map is its complex derivative regarded as an
`ℝ`-linear map. Tangent coordinate changes agree after restricting scalars, and so are still
linear over the larger field. For self-models this also identifies the real derivative of an
inverse chart as complex linear.

For underlying real manifolds and their differentials, see Huybrechts, *Complex Geometry*,
Chapter 1.

## Main results

* `MDifferentiableWithinAt.restrictScalars`, `MDifferentiableAt.restrictScalars`,
  `MDifferentiableOn.restrictScalars`, `MDifferentiable.restrictScalars`: differentiability over
  `𝕜'` implies differentiability over `𝕜`.
* `HasMFDerivWithinAt.restrictScalars`, `HasMFDerivAt.restrictScalars`: a derivative over `𝕜'`,
  with scalars restricted to `𝕜`, is a derivative over `𝕜`.
* `HasMFDerivWithinAt.of_restrictScalars`: conversely, a `𝕜'`-linear map whose scalar restriction
  is a derivative over `𝕜` is a derivative over `𝕜'`.
* `MDifferentiableWithinAt.restrictScalars_mfderivWithin`,
  `MDifferentiableAt.mfderiv_restrictScalars`: the derivative over `𝕜` is the derivative over `𝕜'`
  with scalars restricted to `𝕜`.
* `TauCeti.hasMFDerivWithinAt_restrictScalars_self_iff`: identifies the restricted self-model
  derivative predicate with the usual derivative predicate over the smaller field.
* `TauCeti.tangentCoordChange_restrictScalars`: the tangent coordinate changes over `𝕜` are those
  over `𝕜'` with scalars restricted to `𝕜`; in particular they are `𝕜'`-linear
  (`TauCeti.tangentCoordChange_smul`, or `TauCeti.tangentCoordChange_smul_self` for self-models),
  and so is the derivative of the inverse of a chart
  (`TauCeti.mfderivWithin_extChartAt_symm_smul`).
-/

public section

open Set
open scoped Manifold

section Boundaryless

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜' E'] [IsScalarTower 𝕜 𝕜' E'] {M : Type*} [TopologicalSpace M]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [ChartedSpace H M] {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜' E H} {I' : ModelWithCorners 𝕜' E' H'}
  [I.Boundaryless] [I'.Boundaryless]
  {f : M → N} {s : Set M} {x : M}

variable (𝕜)

/-- A map which is differentiable within a set at a point for the models over `𝕜'` is
differentiable within that set at that point for the models over the smaller field `𝕜`. -/
theorem MDifferentiableWithinAt.restrictScalars
    (h : MDifferentiableWithinAt I I' f s x) :
    MDifferentiableWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x := by
  simp only [mdifferentiableWithinAt_iff', mfld_simps, I.range_eq_univ] at h ⊢
  exact ⟨h.1, h.2.restrictScalars 𝕜⟩

/-- A map which is differentiable at a point for the models over `𝕜'` is differentiable at that
point for the models over the smaller field `𝕜`. -/
theorem MDifferentiableAt.restrictScalars (h : MDifferentiableAt I I' f x) :
    MDifferentiableAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x :=
  mdifferentiableWithinAt_univ.mp (h.mdifferentiableWithinAt.restrictScalars 𝕜)

/-- A map which is differentiable on a set for the models over `𝕜'` is differentiable on that set
for the models over the smaller field `𝕜`. -/
theorem MDifferentiableOn.restrictScalars (h : MDifferentiableOn I I' f s) :
    MDifferentiableOn (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s :=
  fun x hx ↦ (h x hx).restrictScalars 𝕜

/-- A map which is differentiable for the models over `𝕜'` is differentiable for the models over
the smaller field `𝕜`. -/
theorem MDifferentiable.restrictScalars (h : MDifferentiable I I' f) :
    MDifferentiable (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f :=
  fun x ↦ (h x).restrictScalars 𝕜

/-- If `f'` is a derivative of `f` within a set at a point for the models over `𝕜'`, and `g'` is a
`𝕜`-linear map between the tangent spaces over `𝕜` which agrees with `f'` once both are read in the
model spaces, then `g'` is a derivative of `f` within that set at that point for the models over
`𝕜`. -/
theorem HasMFDerivWithinAt.restrictScalars
    {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    {g' : TangentSpace (I.restrictScalars 𝕜) x →L[𝕜] TangentSpace (I'.restrictScalars 𝕜) (f x)}
    (h : HasMFDerivWithinAt I I' f s x f')
    (hg : ((tangentSpaceCastModel I' (f x) : _ →L[𝕜'] E') ∘L f' ∘L
        ((tangentSpaceCastModel I x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 =
      (tangentSpaceCastModel (I'.restrictScalars 𝕜) (f x) : _ →L[𝕜] E') ∘L g' ∘L
        ((tangentSpaceCastModel (I.restrictScalars 𝕜) x).symm : E →L[𝕜] _)) :
    HasMFDerivWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x g' := by
  have hf := h.2.restrictScalars 𝕜
  simp only [hg, mfld_simps, I.range_eq_univ] at hf
  simp only [HasMFDerivWithinAt, mfld_simps, I.range_eq_univ]
  exact ⟨h.1, hf⟩

/-- If `f'` is a derivative of `f` at a point for the models over `𝕜'`, and `g'` is a `𝕜`-linear map
between the tangent spaces over `𝕜` which agrees with `f'` once both are read in the model spaces,
then `g'` is a derivative of `f` at that point for the models over `𝕜`. -/
theorem HasMFDerivAt.restrictScalars
    {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    {g' : TangentSpace (I.restrictScalars 𝕜) x →L[𝕜] TangentSpace (I'.restrictScalars 𝕜) (f x)}
    (h : HasMFDerivAt I I' f x f')
    (hg : ((tangentSpaceCastModel I' (f x) : _ →L[𝕜'] E') ∘L f' ∘L
        ((tangentSpaceCastModel I x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 =
      (tangentSpaceCastModel (I'.restrictScalars 𝕜) (f x) : _ →L[𝕜] E') ∘L g' ∘L
        ((tangentSpaceCastModel (I.restrictScalars 𝕜) x).symm : E →L[𝕜] _)) :
    HasMFDerivAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x g' :=
  hasMFDerivWithinAt_univ.mp (h.hasMFDerivWithinAt.restrictScalars 𝕜 hg)

/-- If `g'` is a derivative of `f` within a set at a point for the models over `𝕜`, and `f'` is a
`𝕜'`-linear map between the tangent spaces over `𝕜'` which agrees with `g'` once both are read in
the model spaces, then `f'` is a derivative of `f` within that set at that point for the models
over `𝕜'`. This is the converse of `HasMFDerivWithinAt.restrictScalars`. -/
theorem HasMFDerivWithinAt.of_restrictScalars
    {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    {g' : TangentSpace (I.restrictScalars 𝕜) x →L[𝕜] TangentSpace (I'.restrictScalars 𝕜) (f x)}
    (h : HasMFDerivWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x g')
    (hg : ((tangentSpaceCastModel I' (f x) : _ →L[𝕜'] E') ∘L f' ∘L
        ((tangentSpaceCastModel I x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 =
      (tangentSpaceCastModel (I'.restrictScalars 𝕜) (f x) : _ →L[𝕜] E') ∘L g' ∘L
        ((tangentSpaceCastModel (I.restrictScalars 𝕜) x).symm : E →L[𝕜] _)) :
    HasMFDerivWithinAt I I' f s x f' := by
  have hf := h.2
  simp only [mfld_simps, I.range_eq_univ] at hf
  simp only [HasMFDerivWithinAt, mfld_simps, I.range_eq_univ]
  exact ⟨h.1, hf.of_restrictScalars 𝕜 hg⟩

/-- If `g'` is a derivative of `f` at a point for the models over `𝕜`, and `f'` is a `𝕜'`-linear map
between the tangent spaces over `𝕜'` which agrees with `g'` once both are read in the model spaces,
then `f'` is a derivative of `f` at that point for the models over `𝕜'`. This is the converse of
`HasMFDerivAt.restrictScalars`. -/
theorem HasMFDerivAt.of_restrictScalars
    {f' : TangentSpace I x →L[𝕜'] TangentSpace I' (f x)}
    {g' : TangentSpace (I.restrictScalars 𝕜) x →L[𝕜] TangentSpace (I'.restrictScalars 𝕜) (f x)}
    (h : HasMFDerivAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x g')
    (hg : ((tangentSpaceCastModel I' (f x) : _ →L[𝕜'] E') ∘L f' ∘L
        ((tangentSpaceCastModel I x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 =
      (tangentSpaceCastModel (I'.restrictScalars 𝕜) (f x) : _ →L[𝕜] E') ∘L g' ∘L
        ((tangentSpaceCastModel (I.restrictScalars 𝕜) x).symm : E →L[𝕜] _)) :
    HasMFDerivAt I I' f x f' :=
  hasMFDerivWithinAt_univ.mp (h.hasMFDerivWithinAt.of_restrictScalars 𝕜 hg)

/-- At a point where `f` is differentiable within a set for the models over `𝕜'`, and where the set
has unique derivatives over the smaller field `𝕜`, the derivative of `f` within the set over `𝕜` is
its derivative over `𝕜'` with scalars restricted to `𝕜`, both read in the model spaces. -/
theorem MDifferentiableWithinAt.restrictScalars_mfderivWithin
    (h : MDifferentiableWithinAt I I' f s x)
    (hs : UniqueMDiffWithinAt (I.restrictScalars 𝕜) s x) :
    ((tangentSpaceCastModel I' (f x) : _ →L[𝕜'] E') ∘L
        mfderivWithin I I' f s x ∘L
        ((tangentSpaceCastModel I x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 =
      (tangentSpaceCastModel (I'.restrictScalars 𝕜) (f x) : _ →L[𝕜] E') ∘L
        mfderivWithin (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f s x ∘L
        ((tangentSpaceCastModel (I.restrictScalars 𝕜) x).symm : E →L[𝕜] _) := by
  have h₁ := h.hasMFDerivWithinAt.2.restrictScalars 𝕜
  have h₂ := (h.restrictScalars 𝕜).hasMFDerivWithinAt.2
  simp only [UniqueMDiffWithinAt, mfld_simps, I.range_eq_univ] at h₁ h₂ hs
  exact hs.eq h₁ h₂

/-- At a point where `f` is differentiable for the models over `𝕜'`, the derivative of `f` over the
smaller field `𝕜` is its derivative over `𝕜'` with scalars restricted to `𝕜`, both read in the model
spaces. For instance, the real derivative of a holomorphic map is its complex derivative. -/
theorem MDifferentiableAt.mfderiv_restrictScalars
    (h : MDifferentiableAt I I' f x) :
    (tangentSpaceCastModel (I'.restrictScalars 𝕜) (f x) : _ →L[𝕜] E') ∘L
        mfderiv (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) f x ∘L
        ((tangentSpaceCastModel (I.restrictScalars 𝕜) x).symm : E →L[𝕜] _) =
      ((tangentSpaceCastModel I' (f x) : _ →L[𝕜'] E') ∘L
        mfderiv I I' f x ∘L
        ((tangentSpaceCastModel I x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 := by
  simpa only [mfderivWithin_univ] using
    (h.mdifferentiableWithinAt.restrictScalars_mfderivWithin 𝕜 (uniqueMDiffWithinAt_univ _)).symm

end Boundaryless

namespace TauCeti

section Self

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace 𝕜' E']
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E' N] {f : M → N} {s : Set M} {x : M}

/-- For self-models, restricting the model scalars gives the usual derivative predicate over
the smaller field, with the derivative read as a map between the model vector spaces. -/
@[simp]
theorem hasMFDerivWithinAt_restrictScalars_self_iff {f' : E →L[𝕜] E'} :
    HasMFDerivWithinAt (𝓘(𝕜', E).restrictScalars 𝕜) (𝓘(𝕜', E').restrictScalars 𝕜) f s x f' ↔
      HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f' := by
  constructor <;> intro h
  all_goals
    refine ⟨h.1, ?_⟩
    have hd := h.2
    simp only [modelWithCornersSelf_restrictScalars] at hd ⊢
    -- The derivative casts are identities on the model spaces, for either self-model.
    exact hd.congr_fderiv (by ext v; rfl)

end Self

section Boundaryless

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] {M : Type*} [TopologicalSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜' E H} [I.Boundaryless] {x : M}

variable (𝕜)

/-- On the overlap of the charts at `x` and `y`, the tangent coordinate change for the model over
`𝕜` is the tangent coordinate change for the model over `𝕜'`, with scalars restricted to `𝕜`: both
are the derivative of the same chart transition. For instance, the tangent coordinate changes of
a complex manifold, regarded as a real manifold, are complex linear. -/
theorem tangentCoordChange_restrictScalars [hI : IsManifold I 1 M]
    {y z : M} (h : z ∈ (chartAt H x).source ∩ (chartAt H y).source) :
    letI := I.isManifold_restrictScalars 𝕜 hI
    tangentCoordChange (I.restrictScalars 𝕜) x y z =
      (tangentCoordChange I x y z).restrictScalars 𝕜 := by
  let := I.isManifold_restrictScalars 𝕜 hI
  have h' : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source := by
    simpa only [extChartAt_source] using h
  have h₁ := (hasFDerivWithinAt_tangentCoordChange h').restrictScalars 𝕜
  have h'' : z ∈ (extChartAt (I.restrictScalars 𝕜) x).source ∩
      (extChartAt (I.restrictScalars 𝕜) y).source := by
    simpa only [extChartAt_source] using h
  have h₂ := hasFDerivWithinAt_tangentCoordChange h''
  simp only [mfld_simps, I.range_eq_univ] at h₁ h₂
  exact (h₂.hasFDerivAt Filter.univ_mem).unique (h₁.hasFDerivAt Filter.univ_mem)

/-- On the overlap of the charts at `x` and `y`, the tangent coordinate change for the model over
`𝕜` is `𝕜'`-linear. For instance, the real tangent coordinate changes of a complex manifold are
complex linear. -/
theorem tangentCoordChange_smul [hI : IsManifold I 1 M] {y z : M}
    (h : z ∈ (chartAt H x).source ∩ (chartAt H y).source) (c : 𝕜') (w : E) :
    letI := I.isManifold_restrictScalars 𝕜 hI
    tangentCoordChange (I.restrictScalars 𝕜) x y z (c • w) =
      c • tangentCoordChange (I.restrictScalars 𝕜) x y z w := by
  let := I.isManifold_restrictScalars 𝕜 hI
  rw [tangentCoordChange_restrictScalars 𝕜 (𝕜' := 𝕜') h, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

end Boundaryless

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {x : M}

variable (𝕜)

/-- For self-models, tangent coordinate changes over the smaller field commute with scalar
multiplication over the larger field on chart overlaps. -/
theorem tangentCoordChange_smul_self [hI : IsManifold 𝓘(𝕜', E) 1 M]
    {y z : M} (h : z ∈ (chartAt E x).source ∩ (chartAt E y).source) (c : 𝕜') (w : E) :
    letI := hI.restrictScalars 𝕜
    tangentCoordChange 𝓘(𝕜, E) x y z (c • w) =
      c • tangentCoordChange 𝓘(𝕜, E) x y z w := by
  let := hI.restrictScalars 𝕜
  simpa only [modelWithCornersSelf_restrictScalars] using
    tangentCoordChange_smul 𝕜 (I := 𝓘(𝕜', E)) h c w

/-- On the target of the chart at `x`, the derivative over `𝕜` of the inverse of the chart is
`𝕜'`-linear: it is a tangent coordinate change. For instance, on a complex manifold, regarded as
a real manifold, the real derivative of the inverse of a chart commutes with multiplication by
`i`. -/
theorem mfderivWithin_extChartAt_symm_smul [IsManifold 𝓘(𝕜', E) 1 M] [IsManifold 𝓘(𝕜, E) 1 M]
    {z : E} (hz : z ∈ (extChartAt 𝓘(𝕜, E) x).target) (c : 𝕜') (w : E) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) (extChartAt 𝓘(𝕜, E) x).symm (range 𝓘(𝕜, E)) z
        ((c • ContinuousLinearMap.id 𝕜 E) w) =
      (c • ContinuousLinearMap.id 𝕜 E)
        (mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E) (extChartAt 𝓘(𝕜, E) x).symm (range 𝓘(𝕜, E)) z w) := by
  have hy : (extChartAt 𝓘(𝕜, E) x).symm z ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(𝕜, E) x).map_target hz
  rw [← (extChartAt 𝓘(𝕜, E) x).right_inv hz, ← TangentBundle.symmL_trivializationAt hy,
    TangentBundle.symmL_trivializationAt_eq_core hy]
  exact tangentCoordChange_smul_self 𝕜 (𝕜' := 𝕜') ⟨hy, mem_chart_source E _⟩ c w

end TauCeti
