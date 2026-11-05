/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Geometry.Manifold.Complex.Euclidean
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.RestrictScalars
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.LinearEquiv
public import TauCeti.Geometry.Manifold.Orientation.Atlas
public import TauCeti.Geometry.Manifold.Orientation.LinearEquiv
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.LinearAlgebra.Complex.Orientation
import Mathlib.LinearAlgebra.Complex.Determinant
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# The canonical orientation of a complex manifold

The real Jacobian determinant of a holomorphic map between open subsets of a finite-dimensional
complex vector space `E` is the squared modulus of its complex Jacobian determinant. Hence a
holomorphic map preserves the real orientation of `E` exactly where its complex derivative is
invertible (`TauCeti.orientationPreservingOn_iff_det_fderiv_ne_zero`), and every holomorphic
coordinate change, with holomorphic inverse, preserves orientation
(`TauCeti.contDiffGroupoid_complex_le_orientationPreservingGroupoid`).

Consequently the holomorphic charts of a complex manifold `M` modelled on `𝓘(ℂ, E)` form an
oriented atlas of the underlying real manifold, modelled on `𝓘(ℝ, E)`. Transporting the canonical
real orientation `TauCeti.complexOrientation E` of the model, the orientation of the real basis
`(b₀, I • b₀, b₁, I • b₁, …)` for any complex basis `b`, through these charts gives the canonical
orientation `TauCeti.complexManifoldOrientation E M` of `M`. It is a manifold orientation in the
sense of `TauCeti.Manifold.Orientation`.

The construction involves no choice: the derivative of *every* chart of the maximal holomorphic
atlas carries the canonical orientation of each tangent space to that of the model
(`TauCeti.map_orientationAt_complexManifoldOrientation`), and this property, required of the
preferred charts only, characterizes it (`TauCeti.eq_complexManifoldOrientation_iff`).

Integration of top-degree forms uses orientation lifts indexed by the form degree, which is the
real dimension `finrank ℝ E`. Reindexing the canonical
orientation of the model along `2 * finrank ℂ E = finrank ℝ E` gives the canonical orientation
lift `TauCeti.complexOrientationLift E M`, indexed by `Fin (finrank ℝ E)`, all of whose chart
signs are `1`: holomorphic coordinate changes have positive real Jacobian determinant. It is the
only lift with this model orientation representing the canonical orientation
(`TauCeti.eq_complexOrientationLift_iff`).

Since a local biholomorphism pulls holomorphic charts back to holomorphic charts, the canonical
orientation is natural: it is the pullback of the canonical orientation of the target along any
local biholomorphism. Applied to the inclusion of an open subset, this says that the canonical
orientation restricts to open submanifolds.

The product `M × M'` of complex manifolds modelled on `𝓘(ℂ, E)` and `𝓘(ℂ, E')` is modelled on
`𝓘(ℂ, E).prod 𝓘(ℂ, E')` rather than on `𝓘(ℂ, E × E')`, so its orientation is the ordered product
`Manifold.Orientation.prod` of the canonical orientations of the factors, `M` before `M'`. This
product orientation is the canonical one: the derivative of every product `Prod.map e e'` of
holomorphic charts carries it to the canonical real orientation of `E × E'`
(`TauCeti.map_orientationAt_prod_complexManifoldOrientation`), and this property of the preferred
product charts characterizes it (`TauCeti.eq_prod_complexManifoldOrientation_iff`). The linear
input is `TauCeti.prod_complexOrientation`.

More generally, any boundaryless complex model `I : ModelWithCorners ℂ E H` restricts scalars to
`I.restrictScalars ℝ : ModelWithCorners ℝ E H` on the same chart carrier `H`. Holomorphic
coordinate changes in `I` preserve orientation in `I.restrictScalars ℝ`
(`ModelWithCorners.contDiffGroupoid_complex_le_orientationPreservingGroupoid_restrictScalars`),
giving the canonical orientation `I.complexManifoldOrientation M` and canonical lift
`I.complexOrientationLift M`, which agree with `complexManifoldOrientation E M` and
`complexOrientationLift E M` on `𝓘(ℂ, E)`.

Because restriction of scalars commutes with `ModelWithCorners.transContinuousLinearEquiv`,
recharting `I` along a complex continuous linear equivalence `e : E ≃L[ℂ] F` transports the
canonical orientation along `e.restrictScalars' ℝ` to the canonical orientation of the recharted
complex manifold
(`ModelWithCorners.orientationAt_transContinuousLinearEquiv_complexManifoldOrientation`,
`ModelWithCorners.complexManifoldOrientation_transContinuousLinearEquiv_self`). Recharting along a
real continuous linear equivalence `e : E ≃L[ℝ] G` preserves the transported orientation
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv`); by
contrast, comparing `I.complexManifoldOrientation M` against the orientation of the recharted
manifold with a *separately fixed* model orientation has `orientationSign` equal to the sign of the
real determinant of `e`
(`ModelWithCorners.orientationSign_toTransContinuousLinearEquiv_complexManifoldOrientation`,
`TauCeti.orientationSign_id_conjCLE`). On `EuclideanSpace ℂ (Fin n)`,
recharting to `TauCeti.complexEuclideanRealModel n` along
`TauCeti.complexEuclideanRealLinearIsometryEquiv n` carries the canonical orientation to the
standard orientation of `EuclideanSpace ℝ (Fin (2 * n))`.

## Main declarations

* `TauCeti.orientationPreservingOn_iff_det_fderiv_ne_zero`: a holomorphic map preserves the real
  orientation exactly where its complex derivative has nonzero determinant.
* `TauCeti.contDiffGroupoid_complex_le_orientationPreservingGroupoid`: holomorphic coordinate
  changes preserve orientation; contrast
  `TauCeti.not_contDiffGroupoid_le_orientationPreservingGroupoid`.
* `TauCeti.isOrientedAtlas_maximalAtlas_complex`: the holomorphic charts form an oriented atlas.
* `TauCeti.complexManifoldOrientation`, `ModelWithCorners.complexManifoldOrientation`: the canonical
  orientation of a complex manifold.
* `TauCeti.orientationAt_complexManifoldOrientation`: its tangent orientation at a point, read
  through any holomorphic chart.
* `TauCeti.complexOrientationLift`, `ModelWithCorners.complexOrientationLift`: the canonical
  orientation as a lift indexed by `Fin (finrank ℝ E)`, with all chart signs `1`
  (`TauCeti.complexOrientationLift_sign`).
* `TauCeti.orientationAt_complexOrientationLift` and `TauCeti.eq_complexOrientationLift_iff`: it
  represents the reindexed canonical orientation, and is characterized by this and its model
  orientation.
* `IsLocalDiffeomorphAt.isOrientationPreservingAt_complexManifoldOrientation`,
  `Diffeomorph.isOrientationPreservingAt_complexManifoldOrientation`: local biholomorphisms, and in
  particular biholomorphisms, preserve canonical orientations.
* `IsLocalDiffeomorph.complexManifoldOrientation_eq_pullback`: the canonical orientation is the
  pullback of the canonical orientation of the target along any local biholomorphism.
* `TauCeti.complexManifoldOrientation_opens_eq_pullback`: the canonical orientation of an open
  subset is the restriction of the canonical orientation of the ambient manifold, that is, its
  pullback along the inclusion.
* `TauCeti.map_orientationAt_prod_complexManifoldOrientation`: products of holomorphic charts carry
  the product of canonical orientations to the canonical orientation of the product model.
* `TauCeti.eq_prod_complexManifoldOrientation_iff`: this property of the preferred product charts
  characterizes the product of canonical orientations.
* `ModelWithCorners.complexManifoldOrientation_transContinuousLinearEquiv_self`,
  `ModelWithCorners.orientationAt_transContinuousLinearEquiv_complexManifoldOrientation`:
  compatibility with complex continuous linear recharting.
* `ModelWithCorners.orientationSign_toTransContinuousLinearEquiv_complexManifoldOrientation`,
  `TauCeti.orientationSign_id_conjCLE`: comparison with a fixed canonical
  model orientation under real continuous linear recharting has the sign of the real determinant.
* `TauCeti.orientationAt_complexManifoldOrientation_complexEuclideanRealModel`: recharting to
  `complexEuclideanRealModel n` carries the canonical orientation to the standard Euclidean one.

## Implementation notes

Tangent orientations are stated for the underlying real manifold structure
`IsManifold 𝓘(ℝ, E) n M` (or `IsManifold (I.restrictScalars ℝ) n M` for a general boundaryless
complex model `I`), obtained from the complex one by `IsManifold.restrictScalars` and
`ModelWithCorners.isManifold_restrictScalars`. Alongside
`TauCeti.ComplexManifold.isManifold_restrictScalars_real` and
`TauCeti.ComplexManifold.isManifold_complexEuclideanRealModel`, this file provides the scoped
instance `TauCeti.ComplexManifold.isManifold_real`, so callers enable them with
`open scoped TauCeti.ComplexManifold`. Since `IsManifold` is a `Prop`, any other proof of the real
structure works as well.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §1.
* D. Huybrechts, *Complex Geometry: An Introduction*, §1.2 and §2.1.
-/

public section

noncomputable section

open Set Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-! ### Holomorphic coordinate changes preserve orientation -/

/-- A holomorphic map on an open subset of a finite-dimensional complex vector space preserves the
real orientation exactly where its complex derivative has nonzero determinant: its real Jacobian
determinant is the squared modulus of the complex one. -/
theorem orientationPreservingOn_iff_det_fderiv_ne_zero {f : E → E} {s : Set E} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) :
    OrientationPreservingOn 𝓘(ℝ, E) f s ↔
      ∀ x ∈ s, LinearMap.det (fderiv ℂ f x : E →ₗ[ℂ] E) ≠ 0 := by
  simp only [orientationPreservingOn_iff, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, range_id, fderivWithin_univ, differentiableWithinAt_univ,
    id_eq]
  refine forall₂_congr fun x hx ↦ ?_
  have hfx : DifferentiableAt ℂ f x := hf.differentiableAt (hs.mem_nhds hx)
  rw [hfx.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars_eq_normSq, Complex.normSq_pos]
  simp [hfx.restrictScalars ℝ]

/-- An open partial homeomorphism of a finite-dimensional complex vector space which is
holomorphic on its source, with inverse holomorphic on its target, preserves orientation on its
source. -/
theorem _root_.OpenPartialHomeomorph.orientationPreservingOn_of_differentiableOn
    (e : OpenPartialHomeomorph E E)
    (he : DifferentiableOn ℂ e e.source) (he' : DifferentiableOn ℂ e.symm e.target) :
    OrientationPreservingOn 𝓘(ℝ, E) e e.source := by
  refine (orientationPreservingOn_iff_det_fderiv_ne_zero e.open_source he).2 fun x hx ↦ ?_
  obtain ⟨A, hA⟩ := e.isInvertible_fderiv hx (he.differentiableAt (e.open_source.mem_nhds hx))
    (he'.differentiableAt (e.open_target.mem_nhds (e.map_source hx)))
  rw [← hA]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

/-- Holomorphic coordinate changes preserve orientation: for `n ≠ 0`, the `C^n` groupoid of the
complex model `𝓘(ℂ, E)` is contained in the orientation-preserving groupoid of the underlying real
model `𝓘(ℝ, E)`. For real coordinate changes this fails
(`TauCeti.not_contDiffGroupoid_le_orientationPreservingGroupoid`). -/
theorem contDiffGroupoid_complex_le_orientationPreservingGroupoid (n : ℕ∞ω) [NeZero n] :
    contDiffGroupoid n 𝓘(ℂ, E) ≤ orientationPreservingGroupoid 𝓘(ℝ, E) := by
  intro e he
  have hn : n ≠ 0 := NeZero.ne n
  have hdiff (e : OpenPartialHomeomorph E E) (he : e ∈ contDiffGroupoid n 𝓘(ℂ, E)) :
      DifferentiableOn ℂ e e.source := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at he
    simpa [contDiffPregroupoid] using he.1.differentiableOn hn
  exact mem_orientationPreservingGroupoid_iff.2
    ⟨e.orientationPreservingOn_of_differentiableOn (hdiff e he)
      (hdiff e.symm ((contDiffGroupoid n 𝓘(ℂ, E)).symm he)),
    e.symm.orientationPreservingOn_of_differentiableOn
      (hdiff e.symm ((contDiffGroupoid n 𝓘(ℂ, E)).symm he)) (hdiff e he)⟩

/-! ### The canonical orientation of a complex manifold -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The atlas of a complex manifold has orientation-preserving coordinate changes, as a real
manifold. -/
instance hasGroupoid_orientationPreservingGroupoid_of_complex [IsManifold 𝓘(ℂ, E) 1 M] :
    HasGroupoid M (orientationPreservingGroupoid 𝓘(ℝ, E)) :=
  hasGroupoid_of_le (G₁ := contDiffGroupoid 1 𝓘(ℂ, E)) inferInstance
    (contDiffGroupoid_complex_le_orientationPreservingGroupoid 1)

/-- For `n ≠ 0`, the maximal holomorphic `C^n` atlas of a complex manifold is an oriented atlas of
the underlying real `C^n` manifold. -/
theorem isOrientedAtlas_maximalAtlas_complex (n : ℕ∞ω) [NeZero n] [IsManifold 𝓘(ℂ, E) n M] :
    IsOrientedAtlas 𝓘(ℝ, E) n (IsManifold.maximalAtlas 𝓘(ℂ, E) n M) where
  subset_maximalAtlas := IsManifold.maximalAtlas_subset_restrictScalars ℝ
  exists_mem_source x := ⟨chartAt E x, IsManifold.chart_mem_maximalAtlas x, mem_chart_source E x⟩
  symm_trans_mem he he' := contDiffGroupoid_complex_le_orientationPreservingGroupoid n
    (IsManifold.compatible_of_mem_maximalAtlas he he')

namespace ComplexManifold

/-- A complex `C^n` manifold is, with the same charts, a real `C^n` manifold modelled on
`𝓘(ℝ, E)`. Tangent orientations of a complex manifold are stated for this real structure. It is
a scoped instance, available after `open scoped TauCeti.ComplexManifold`. -/
scoped instance isManifold_real {n : ℕ∞ω} {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [h : IsManifold 𝓘(ℂ, E) n X] : IsManifold 𝓘(ℝ, E) n X :=
  h.restrictScalars ℝ

end ComplexManifold

open scoped ComplexManifold

variable [IsManifold 𝓘(ℂ, E) 1 M]

omit [FiniteDimensional ℂ E] in
/-- The real dimension `finrank ℝ E = 2 * finrank ℂ E` indexes the canonical orientations. -/
theorem card_fin_two_mul_finrank_complex :
    Fintype.card (Fin (2 * finrank ℂ E)) = finrank ℝ E := by
  rw [Fintype.card_fin, finrank_real_of_complex]

variable (E M) in
/-- The canonical orientation of a complex manifold `M` modelled on `𝓘(ℂ, E)`, as a manifold
orientation of its underlying real manifold. Every holomorphic chart carries it to the canonical
real orientation `TauCeti.complexOrientation E` of the model
(`TauCeti.map_orientationAt_complexManifoldOrientation`). -/
def complexManifoldOrientation : Manifold.Orientation 𝓘(ℝ, E) M (Fin (2 * finrank ℂ E)) :=
  (isOrientedAtlas_maximalAtlas_complex (M := M) 1).orientation (complexOrientation E)
    card_fin_two_mul_finrank_complex

/-- The derivative of a holomorphic chart at `x` is an equivalence carrying the canonical
orientation of the tangent space at `x` to the canonical real orientation of the model. -/
private theorem exists_map_orientationAt_complexManifoldOrientation
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 1 M) {x : M}
    (hx : x ∈ e.source) : ∃ L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E,
      (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x ∧
        Orientation.map _ L.toLinearEquiv
          ((complexManifoldOrientation E M).orientationAt x) = complexOrientation E := by
  unfold complexManifoldOrientation
  exact (isOrientedAtlas_maximalAtlas_complex (M := M) 1).orientation_spec
    (complexOrientation E) card_fin_two_mul_finrank_complex he hx

/-- The derivative of every chart of the maximal holomorphic atlas, represented by a real
continuous linear equivalence `L`, carries the canonical orientation of the tangent space to the
canonical real orientation of the model. -/
theorem map_orientationAt_complexManifoldOrientation (n : ℕ∞ω) [NeZero n]
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) n M) {x : M}
    (hx : x ∈ e.source) (L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E)
    (hL : (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x) :
    Orientation.map _ L.toLinearEquiv
      ((complexManifoldOrientation E M).orientationAt x) = complexOrientation E := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n)) he
  obtain ⟨L', hL', hmap⟩ := exists_map_orientationAt_complexManifoldOrientation he1 hx
  rwa [ContinuousLinearEquiv.coe_injective (hL'.trans hL.symm)] at hmap

/-- The tangent orientation of the canonical orientation of a complex manifold, read through any
holomorphic chart `e` at `x`: it is the canonical orientation of the model, pulled back by the
derivative `L` of `e` at `x`. -/
theorem orientationAt_complexManifoldOrientation (n : ℕ∞ω) [NeZero n]
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) n M) {x : M}
    (hx : x ∈ e.source) (L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E)
    (hL : (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x) :
    (complexManifoldOrientation E M).orientationAt x =
      Orientation.map _ L.symm.toLinearEquiv (complexOrientation E) := by
  rw [← map_orientationAt_complexManifoldOrientation n he hx L hL,
    ContinuousLinearEquiv.toLinearEquiv_symm, ← Orientation.map_symm, Equiv.symm_apply_apply]

/-- A manifold orientation of a complex manifold is its canonical orientation exactly when, at
every point `x`, the derivative of the preferred chart at `x` carries it to the canonical real
orientation of the model. -/
theorem eq_complexManifoldOrientation_iff
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (2 * finrank ℂ E))) :
    o = complexManifoldOrientation E M ↔ ∀ x : M, ∃ L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E,
      (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) x ∧
        Orientation.map _ L.toLinearEquiv (o.orientationAt x) = complexOrientation E := by
  constructor
  · rintro rfl x
    exact exists_map_orientationAt_complexManifoldOrientation
      (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source E x)
  · intro h
    ext x
    obtain ⟨L, hL, hmap⟩ := h x
    exact (Orientation.map _ L.toLinearEquiv).injective (hmap.trans
      (map_orientationAt_complexManifoldOrientation 1 (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_source E x) L hL).symm)

/-- A complex manifold is orientable as a real manifold. -/
instance orientable_of_complex : Orientable 𝓘(ℝ, E) M :=
  Orientable.of_hasGroupoid

/-- At every point `x`, the canonical orientation of the tangent space, read in the preferred
chart at `x`, is the canonical real orientation of the model. -/
@[simp]
theorem orientationAt_complexManifoldOrientation_eq_complexOrientation (x : M) :
    (complexManifoldOrientation E M).orientationAt x = complexOrientation E :=
  (isOrientedAtlas_maximalAtlas_complex 1).orientationAt_orientation _ _
    (IsManifold.chart_mem_maximalAtlas x)

/-! ### The orientation lift indexed by the real dimension -/

variable (E M) in
/-- The canonical orientation of a complex manifold as an orientation lift indexed by the real
dimension `Fin (finrank ℝ E)`. Its model orientation is the canonical real orientation of `E`,
reindexed along `2 * finrank ℂ E = finrank ℝ E`, and all its chart signs are `1`, since
holomorphic coordinate changes preserve orientation. It represents the canonical orientation
(`TauCeti.orientationAt_complexOrientationLift`). -/
def complexOrientationLift : Manifold.OrientationLift 𝓘(ℝ, E) M (Fin (finrank ℝ E)) :=
  Manifold.OrientationLift.ofHasGroupoid
    (Orientation.reindex ℝ E (finCongr (finrank_real_of_complex E).symm) (complexOrientation E))
    (Fintype.card_fin _)

@[simp]
theorem complexOrientationLift_modelOrientation :
    (complexOrientationLift E M).modelOrientation =
      Orientation.reindex ℝ E (finCongr (finrank_real_of_complex E).symm)
        (complexOrientation E) := by
  simp [complexOrientationLift]

/-- Every chart sign of the canonical orientation lift of a complex manifold is `1`. -/
@[simp]
theorem complexOrientationLift_sign (α : M) (x : (chartAt E α).source) :
    (complexOrientationLift E M).sign α x = 1 := by
  simp [complexOrientationLift]

/-- The canonical orientation lift represents the canonical orientation of a complex manifold: at
every point, its tangent orientation, read in the preferred chart, is the canonical real
orientation of the model reindexed by the real dimension, which is also the canonical tangent
orientation there (`TauCeti.orientationAt_complexManifoldOrientation_eq_complexOrientation`). -/
@[simp]
theorem orientationAt_complexOrientationLift (x : M) :
    (complexOrientationLift E M).orientationAt x =
      Orientation.reindex ℝ E (finCongr (finrank_real_of_complex E).symm)
        (complexOrientation E) :=
  Manifold.OrientationLift.orientationAt_ofHasGroupoid _ _ x

/-- An orientation lift of a complex manifold, indexed by the real dimension, is the canonical
lift exactly when its model orientation is the reindexed canonical real orientation of the model
and its tangent orientations are the reindexed canonical ones. In particular, every lift with
these two properties has all chart signs `1`. -/
theorem eq_complexOrientationLift_iff
    (l : Manifold.OrientationLift 𝓘(ℝ, E) M (Fin (finrank ℝ E))) :
    l = complexOrientationLift E M ↔
      l.modelOrientation = Orientation.reindex ℝ E (finCongr (finrank_real_of_complex E).symm)
          (complexOrientation E) ∧
        ∀ x, l.orientationAt x = Orientation.reindex ℝ _
          (finCongr (finrank_real_of_complex E).symm)
          ((complexManifoldOrientation E M).orientationAt x) := by
  constructor
  · rintro rfl
    refine ⟨complexOrientationLift_modelOrientation, fun x ↦ ?_⟩
    rw [orientationAt_complexManifoldOrientation_eq_complexOrientation]
    exact orientationAt_complexOrientationLift x
  · rintro ⟨hm, h⟩
    exact Manifold.OrientationLift.ext_of_orientationAt
      (hm.trans complexOrientationLift_modelOrientation.symm) fun x ↦
      (h x).trans (by
        rw [orientationAt_complexOrientationLift,
          orientationAt_complexManifoldOrientation_eq_complexOrientation]
        -- The tangent space at `x` is the model space, with its own scalar structure.
        rfl)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ, E) 1 N]

/-! ### Naturality under local biholomorphisms -/

/-- Local biholomorphisms preserve canonical orientations: if `f : M → N` is a `C^n` local
biholomorphism at `x`, for `n ≠ 0`, its derivative at `x` carries the canonical orientation of `M`
at `x` to that of `N` at `f x`. -/
theorem _root_.IsLocalDiffeomorphAt.isOrientationPreservingAt_complexManifoldOrientation
    (n : ℕ∞ω) [NeZero n] [IsManifold 𝓘(ℂ, E) n M] [IsManifold 𝓘(ℂ, E) n N] {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) n f x) :
    Manifold.Orientation.IsOrientationPreservingAt (complexManifoldOrientation E M)
      (complexManifoldOrientation E N) f x := by
  -- Read both orientations through the holomorphic chart `e` of `N` at `f x` and a holomorphic
  -- chart `e'` of `M` at `x` agreeing with `e ∘ f` near `x`, whose derivative at `x` is that of
  -- `e` after that of `f`.
  set e := chartAt E (f x)
  obtain ⟨e', he', hx, hcomp⟩ := hf.exists_mem_maximalAtlas_eventuallyEq
    (IsManifold.chart_mem_maximalAtlas (f x)) (mem_chart_source E (f x))
  obtain ⟨L, hL, hmap⟩ :=
    (eq_complexManifoldOrientation_iff (complexManifoldOrientation E N)).1 rfl (f x)
  have hn : n ≠ 0 := NeZero.ne n
  have hfR : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) n f x := hf.restrictScalars ℝ
  let D := hfR.mfderivToContinuousLinearEquiv hn
  have hD : (D : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (f x)) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x :=
    hfR.mfderivToContinuousLinearEquiv_coe hn
  have hDL : ((D.trans L : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e' x := by
    rw [hcomp.mfderiv_eq, mfderiv_comp x (mdifferentiableAt_atlas (chart_mem_atlas E (f x))
      (mem_chart_source E (f x))) (hfR.mdifferentiableAt hn), ← hL, ← hD]
    exact (ContinuousLinearEquiv.comp_coe D L).symm
  refine (Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ D hD).2 ?_
  have hM := map_orientationAt_complexManifoldOrientation n he' hx (D.trans L) hDL
  rw [ContinuousLinearEquiv.trans_toLinearEquiv, Orientation.map_trans] at hM
  exact (Orientation.map _ L.toLinearEquiv).injective (hM.trans hmap.symm)

/-- Biholomorphisms preserve canonical orientations: at every point `x`, the derivative of a
`C^n` biholomorphism `Φ : M → N`, for `n ≠ 0`, carries the canonical orientation of `M` at `x` to
that of `N` at `Φ x`. -/
theorem _root_.Diffeomorph.isOrientationPreservingAt_complexManifoldOrientation (n : ℕ∞ω)
    [NeZero n] [IsManifold 𝓘(ℂ, E) n M] [IsManifold 𝓘(ℂ, E) n N]
    (Φ : M ≃ₘ^n⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ N) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (complexManifoldOrientation E M)
      (complexManifoldOrientation E N) Φ x :=
  (Φ.isLocalDiffeomorph x).isOrientationPreservingAt_complexManifoldOrientation n

/-- The canonical orientation of a complex manifold is the pullback of the canonical orientation
of `N` along any `C^n` local biholomorphism `f : M → N`, for `n ≠ 0`. The arguments `hf'`, `hdf`
and `hι` are the data that `Manifold.Orientation.pullback` requires; they all follow from `hf`. -/
theorem _root_.IsLocalDiffeomorph.complexManifoldOrientation_eq_pullback (n : ℕ∞ω) [NeZero n]
    [IsManifold 𝓘(ℂ, E) n M] [IsManifold 𝓘(ℂ, E) n N] {f : M → N}
    (hf : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) n f) (hf' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f)
    (hdf : ∀ x, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).IsInvertible)
    (hι : Fintype.card (Fin (2 * finrank ℂ E)) = finrank ℝ E) :
    complexManifoldOrientation E M = (complexManifoldOrientation E N).pullback hf' hdf hι :=
  (Manifold.Orientation.eq_pullback_iff _ hf' hdf hι).2 fun x ↦
    (hf x).isOrientationPreservingAt_complexManifoldOrientation n

/-! ### Open submanifolds -/

/-- The inclusion of an open subset `U` of a complex manifold, with the charts `U` inherits from
`M`, preserves canonical orientations at every point. -/
theorem isOrientationPreservingAt_subtype_val_complexManifoldOrientation
    {U : TopologicalSpace.Opens M} (x : U) :
    Manifold.Orientation.IsOrientationPreservingAt (complexManifoldOrientation E U)
      (complexManifoldOrientation E M) Subtype.val x :=
  (isLocalDiffeomorph_subtype_val (n := 1) x).isOrientationPreservingAt_complexManifoldOrientation 1

/-- The canonical orientation of an open subset `U` of a complex manifold, for the charts it
inherits from `M`, is the pullback of the canonical orientation of `M` along the inclusion. The
arguments `hf'`, `hdf` and `hι` are the data that `Manifold.Orientation.pullback` requires. -/
theorem complexManifoldOrientation_opens_eq_pullback {U : TopologicalSpace.Opens M}
    (hf' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (Subtype.val : U → M))
    (hdf : ∀ x : U, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Subtype.val x).IsInvertible)
    (hι : Fintype.card (Fin (2 * finrank ℂ E)) = finrank ℝ E) :
    complexManifoldOrientation E U = (complexManifoldOrientation E M).pullback hf' hdf hι :=
  isLocalDiffeomorph_subtype_val.complexManifoldOrientation_eq_pullback 1 hf' hdf hι

/-! ### Products -/

section Prod

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E') 1 M']

/-- The derivative at `x` of a product `Prod.map e e'` of charts of the maximal holomorphic atlases,
represented by a real continuous linear equivalence `L`, carries the ordered product of the
canonical orientations of `M` and `M'` to the canonical real orientation of the product model
`E × E'`. -/
theorem map_orientationAt_prod_complexManifoldOrientation (n : ℕ∞ω) [NeZero n]
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) n M)
    {e' : OpenPartialHomeomorph M' E'} (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ, E') n M')
    {x : M × M'} (hx : x.1 ∈ e.source) (hx' : x.2 ∈ e'.source)
    (L : TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, E')) x ≃L[ℝ] E × E')
    (hL : (L : TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, E')) x →L[ℝ] E × E') =
      mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, E')) (𝓘(ℝ, E).prod 𝓘(ℝ, E')) (Prod.map e e') x) :
    Orientation.map _ L.toLinearEquiv
        (((complexManifoldOrientation E M).prod (complexManifoldOrientation E' M')).orientationAt
          x) =
      Orientation.reindex ℝ (E × E') (finCongr (by rw [finrank_prod]; ring))
        (complexOrientation (E × E')) := by
  have hn : (1 : ℕ∞ω) ≤ n := ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n)
  have he₁ := IsManifold.maximalAtlas_subset_of_le hn he
  have he₁' := IsManifold.maximalAtlas_subset_of_le hn he'
  obtain ⟨L₁, hL₁, h₁⟩ := exists_map_orientationAt_complexManifoldOrientation he₁ hx
  obtain ⟨L₂, hL₂, h₂⟩ := exists_map_orientationAt_complexManifoldOrientation he₁' hx'
  -- The derivative of `Prod.map e e'` is the product of the derivatives of `e` and `e'`.
  have hLeq : L = L₁.prodCongr L₂ := by
    refine ContinuousLinearEquiv.coe_injective ?_
    rw [hL, mfderiv_prodMap (mdifferentiableAt_of_mem_maximalAtlas
        (IsManifold.maximalAtlas_subset_restrictScalars ℝ he₁) hx)
      (mdifferentiableAt_of_mem_maximalAtlas
        (IsManifold.maximalAtlas_subset_restrictScalars ℝ he₁') hx'), ← hL₁, ← hL₂]
    exact (ContinuousLinearEquiv.coe_prodCongr L₁ L₂).symm
  have key : Orientation.map _ (L₁.prodCongr L₂).toLinearEquiv
      (((complexManifoldOrientation E M).prod (complexManifoldOrientation E' M')).orientationAt
        x) = Orientation.reindex ℝ (E × E') (finCongr (by rw [finrank_prod]; ring))
          (complexOrientation (E × E')) := by
    -- `ContinuousLinearEquiv.prodCongr` is built from `LinearEquiv.prodCongr`.
    have hprod : (L₁.prodCongr L₂).toLinearEquiv =
        L₁.toLinearEquiv.prodCongr L₂.toLinearEquiv := rfl
    rw [Manifold.Orientation.orientationAt_prod, hprod, Orientation.map_prod, h₁, h₂]
    exact prod_complexOrientation
  rw [hLeq]
  exact key

/-- A manifold orientation of a product of complex manifolds is the ordered product of their
canonical orientations exactly when, at every point `x`, the derivative of the preferred product
chart `Prod.map (chartAt E x.1) (chartAt E' x.2)` carries it to the canonical real orientation of
the product model `E × E'`. -/
theorem eq_prod_complexManifoldOrientation_iff
    (o : Manifold.Orientation (𝓘(ℝ, E).prod 𝓘(ℝ, E')) (M × M')
      (Fin (2 * finrank ℂ E + 2 * finrank ℂ E'))) :
    o = (complexManifoldOrientation E M).prod (complexManifoldOrientation E' M') ↔
      ∀ x : M × M', ∃ L : TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, E')) x ≃L[ℝ] E × E',
        (L : TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, E')) x →L[ℝ] E × E') =
          mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, E')) (𝓘(ℝ, E).prod 𝓘(ℝ, E'))
            (Prod.map (chartAt E x.1) (chartAt E' x.2)) x ∧
        Orientation.map _ L.toLinearEquiv (o.orientationAt x) =
          Orientation.reindex ℝ (E × E') (finCongr (by rw [finrank_prod]; ring))
            (complexOrientation (E × E')) := by
  have hmem (x : M × M') :=
    map_orientationAt_prod_complexManifoldOrientation 1 (IsManifold.chart_mem_maximalAtlas x.1)
      (IsManifold.chart_mem_maximalAtlas x.2) (mem_chart_source E x.1) (mem_chart_source E' x.2)
  constructor
  · rintro rfl x
    obtain ⟨L₁, hL₁, -⟩ := (eq_complexManifoldOrientation_iff (complexManifoldOrientation E M)).1
      rfl x.1
    obtain ⟨L₂, hL₂, -⟩ :=
      (eq_complexManifoldOrientation_iff (complexManifoldOrientation E' M')).1 rfl x.2
    let L : TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, E')) x ≃L[ℝ] E × E' := L₁.prodCongr L₂
    have hL : (L : TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, E')) x →L[ℝ] E × E') =
          mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, E')) (𝓘(ℝ, E).prod 𝓘(ℝ, E'))
            (Prod.map (chartAt E x.1) (chartAt E' x.2)) x := by
      rw [mfderiv_prodMap (mdifferentiableAt_atlas (chart_mem_atlas E x.1)
          (mem_chart_source E x.1)) (mdifferentiableAt_atlas (chart_mem_atlas E' x.2)
          (mem_chart_source E' x.2)), ← hL₁, ← hL₂]
      exact ContinuousLinearEquiv.coe_prodCongr L₁ L₂
    exact ⟨L, hL, hmem x L hL⟩
  · intro h
    ext x
    obtain ⟨L, hL, hmap⟩ := h x
    exact (Orientation.map _ L.toLinearEquiv).injective (hmap.trans (hmem x L hL).symm)

end Prod

end TauCeti

/-! ### Boundaryless complex models and restriction of scalars -/

namespace ModelWithCorners

open TauCeti
open scoped Topology TauCeti.ComplexManifold

section RestrictScalars

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace H]

private theorem orientationPreservingOn_restrictScalars_of_mem_contDiffGroupoid
    (I : ModelWithCorners ℂ E H) [I.Boundaryless] {n : ℕ∞ω} [NeZero n]
    {φ : OpenPartialHomeomorph H H} (hφ : φ ∈ contDiffGroupoid n I) :
    OrientationPreservingOn (I.restrictScalars ℝ) φ φ.source := by
  have hn : n ≠ 0 := NeZero.ne n
  have hsymm : φ.symm ∈ contDiffGroupoid n I := (contDiffGroupoid n I).symm hφ
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hφ hsymm
  have hf : DifferentiableOn ℂ (I ∘ φ ∘ I.symm) (I.symm ⁻¹' φ.source) := by
    have h := hφ.1.differentiableOn hn
    rwa [I.range_eq_univ, inter_univ] at h
  have hg : DifferentiableOn ℂ (I ∘ φ.symm ∘ I.symm) (I.symm ⁻¹' φ.target) := by
    have h := hsymm.1.differentiableOn hn
    rwa [I.range_eq_univ, inter_univ] at h
  have hs : IsOpen (I.symm ⁻¹' φ.source) := φ.open_source.preimage I.continuous_symm
  have ht : IsOpen (I.symm ⁻¹' φ.target) := φ.open_target.preimage I.continuous_symm
  rw [orientationPreservingOn_iff]
  intro x hx
  rw [coe_restrictScalars, coe_restrictScalars_symm, I.range_eq_univ, differentiableWithinAt_univ,
    fderivWithin_univ]
  have hx' : I x ∈ I.symm ⁻¹' φ.source := by simpa using hx
  have hφx' : I (φ x) ∈ I.symm ⁻¹' φ.target := by simpa using φ.map_source hx
  have hfx : DifferentiableAt ℂ (I ∘ φ ∘ I.symm) (I x) :=
    hf.differentiableAt (hs.mem_nhds hx')
  have hgx : DifferentiableAt ℂ (I ∘ φ.symm ∘ I.symm) ((I ∘ φ ∘ I.symm) (I x)) := by
    simpa [Function.comp_apply] using hg.differentiableAt (ht.mem_nhds hφx')
  have heq : (I ∘ φ.symm ∘ I.symm) ∘ (I ∘ φ ∘ I.symm) =ᶠ[𝓝 (I x)] id := by
    filter_upwards [hs.mem_nhds hx'] with y hy
    have hy_range : y ∈ range I := by rw [I.range_eq_univ]; trivial
    simp only [Function.comp_apply, id_eq, I.left_inv, φ.left_inv hy, I.right_inv hy_range]
  have hcomp :
      (fderiv ℂ (I ∘ φ.symm ∘ I.symm) ((I ∘ φ ∘ I.symm) (I x))).comp
        (fderiv ℂ (I ∘ φ ∘ I.symm) (I x)) = ContinuousLinearMap.id ℂ E := by
    rw [← fderiv_comp (I x) hgx hfx, heq.fderiv_eq, fderiv_id]
  have hdet_ne : LinearMap.det (fderiv ℂ (I ∘ φ ∘ I.symm) (I x) : E →ₗ[ℂ] E) ≠ 0 := by
    intro hzero
    have h1 := congrArg (fun T : E →L[ℂ] E ↦ LinearMap.det (T : E →ₗ[ℂ] E)) hcomp
    simp [LinearMap.det_comp, hzero] at h1
  refine ⟨hfx.restrictScalars ℝ, ?_⟩
  rw [hfx.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars_eq_normSq]
  exact Complex.normSq_pos.mpr hdet_ne

/-- Holomorphic coordinate changes in a boundaryless complex model `I` preserve orientation in the
underlying real model `I.restrictScalars ℝ`. -/
theorem contDiffGroupoid_complex_le_orientationPreservingGroupoid_restrictScalars
    (I : ModelWithCorners ℂ E H) [I.Boundaryless] (n : ℕ∞ω) [NeZero n] :
    contDiffGroupoid n I ≤ orientationPreservingGroupoid (I.restrictScalars ℝ) := fun _ hφ ↦
  mem_orientationPreservingGroupoid_iff.2
    ⟨orientationPreservingOn_restrictScalars_of_mem_contDiffGroupoid I hφ,
     orientationPreservingOn_restrictScalars_of_mem_contDiffGroupoid I
       ((contDiffGroupoid n I).symm hφ)⟩

variable (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The atlas of a manifold modelled on a boundaryless complex model `I` has orientation-preserving
coordinate changes over `I.restrictScalars ℝ`. -/
instance hasGroupoid_orientationPreservingGroupoid_restrictScalars
    {I : ModelWithCorners ℂ E H} [I.Boundaryless] [IsManifold I 1 M] :
    HasGroupoid M (orientationPreservingGroupoid (I.restrictScalars ℝ)) :=
  hasGroupoid_of_le (G₁ := contDiffGroupoid 1 I) inferInstance
    (I.contDiffGroupoid_complex_le_orientationPreservingGroupoid_restrictScalars 1)

/-- For `n ≠ 0`, the maximal holomorphic `C^n` atlas of a manifold modelled on a boundaryless
complex model `I` is an oriented atlas over `I.restrictScalars ℝ`. -/
theorem isOrientedAtlas_maximalAtlas_complex
    (n : ℕ∞ω) [NeZero n] [IsManifold I n M] :
    IsOrientedAtlas (I.restrictScalars ℝ) n (IsManifold.maximalAtlas I n M) where
  subset_maximalAtlas := I.maximalAtlas_subset_restrictScalars ℝ
  exists_mem_source x := ⟨chartAt H x, IsManifold.chart_mem_maximalAtlas x, mem_chart_source H x⟩
  symm_trans_mem he he' :=
    I.contDiffGroupoid_complex_le_orientationPreservingGroupoid_restrictScalars n
      (IsManifold.compatible_of_mem_maximalAtlas he he')

variable [IsManifold I 1 M]

variable (M) in
/-- The canonical orientation of a complex manifold `M` modelled on a boundaryless complex model
`I : ModelWithCorners ℂ E H`, as a manifold orientation over `I.restrictScalars ℝ`. -/
def complexManifoldOrientation :
    Manifold.Orientation (I.restrictScalars ℝ) M (Fin (2 * finrank ℂ E)) :=
  (I.isOrientedAtlas_maximalAtlas_complex (M := M) 1).orientation (complexOrientation E)
    card_fin_two_mul_finrank_complex

/-- Every chart of the maximal holomorphic atlas of `I` carries `I.complexManifoldOrientation M`
to the canonical real orientation of `E`. -/
theorem map_orientationAt_complexManifoldOrientation (n : ℕ∞ω) [NeZero n]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M) {x : M}
    (hx : x ∈ e.source) (L : TangentSpace (I.restrictScalars ℝ) x ≃L[ℝ] E)
    (hL : (L : TangentSpace (I.restrictScalars ℝ) x →L[ℝ] E) =
      mfderiv (I.restrictScalars ℝ) (I.restrictScalars ℝ) e x) :
    Orientation.map _ L.toLinearEquiv
      ((I.complexManifoldOrientation M).orientationAt x) = complexOrientation E := by
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n)) he
  obtain ⟨L', hL', hmap⟩ :=
    (I.isOrientedAtlas_maximalAtlas_complex (M := M) 1).orientation_spec
      (complexOrientation E) card_fin_two_mul_finrank_complex he1 hx
  rwa [ContinuousLinearEquiv.coe_injective (hL'.trans hL.symm)] at hmap

/-- `I.complexManifoldOrientation M` is characterized by the fact that, at every point `x`, the
derivative of the preferred chart at `x` carries it to `complexOrientation E`. -/
theorem eq_complexManifoldOrientation_iff
    (o : Manifold.Orientation (I.restrictScalars ℝ) M (Fin (2 * finrank ℂ E))) :
    o = I.complexManifoldOrientation M ↔ ∀ x : M,
      ∃ L : TangentSpace (I.restrictScalars ℝ) x ≃L[ℝ] E,
        (L : TangentSpace (I.restrictScalars ℝ) x →L[ℝ] E) =
          mfderiv (I.restrictScalars ℝ) (I.restrictScalars ℝ) (chartAt H x) x ∧
          Orientation.map _ L.toLinearEquiv (o.orientationAt x) = complexOrientation E := by
  constructor
  · rintro rfl x
    exact (I.isOrientedAtlas_maximalAtlas_complex (M := M) 1).orientation_spec
      (complexOrientation E) card_fin_two_mul_finrank_complex
      (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source H x)
  · intro h
    ext x
    obtain ⟨L, hL, hmap⟩ := h x
    exact (Orientation.map _ L.toLinearEquiv).injective (hmap.trans
      (I.map_orientationAt_complexManifoldOrientation 1 (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_source H x) L hL).symm)

/-- At every point `x`, the tangent orientation of `I.complexManifoldOrientation M`, read in the
preferred chart at `x`, is `complexOrientation E`. -/
@[simp]
theorem orientationAt_complexManifoldOrientation_eq_complexOrientation (x : M) :
    (I.complexManifoldOrientation M).orientationAt x = complexOrientation E :=
  (I.isOrientedAtlas_maximalAtlas_complex 1).orientationAt_orientation _ _
    (IsManifold.chart_mem_maximalAtlas x)

/-- `I.complexManifoldOrientation M` is represented by `OrientationLift.ofHasGroupoid` with model
orientation `complexOrientation E`. -/
theorem complexManifoldOrientation_eq_mk_ofHasGroupoid :
    I.complexManifoldOrientation M =
      Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid (complexOrientation E)
          card_fin_two_mul_finrank_complex) := by
  ext x
  simp only [orientationAt_complexManifoldOrientation_eq_complexOrientation,
    Manifold.Orientation.orientationAt_mk, Manifold.OrientationLift.orientationAt_ofHasGroupoid]
  -- The tangent space at `x` is the model space, with its own scalar structure.
  rfl

variable (M) in
/-- The canonical orientation lift of a complex manifold `M` modelled on a boundaryless complex
model `I`, indexed by `Fin (finrank ℝ E)`, with all chart signs `1`. -/
def complexOrientationLift :
    Manifold.OrientationLift (I.restrictScalars ℝ) M (Fin (finrank ℝ E)) :=
  Manifold.OrientationLift.ofHasGroupoid
    (Orientation.reindex ℝ E (finCongr (finrank_real_of_complex E).symm) (complexOrientation E))
    (Fintype.card_fin _)

@[simp]
theorem complexOrientationLift_modelOrientation :
    (I.complexOrientationLift M).modelOrientation =
      Orientation.reindex ℝ E (finCongr (finrank_real_of_complex E).symm)
        (complexOrientation E) := by
  simp [complexOrientationLift]

@[simp]
theorem complexOrientationLift_sign (α : M) (x : (chartAt H α).source) :
    (I.complexOrientationLift M).sign α x = 1 := by
  simp [complexOrientationLift]

@[simp]
theorem orientationAt_complexOrientationLift (x : M) :
    (I.complexOrientationLift M).orientationAt x =
      Orientation.reindex ℝ E (finCongr (finrank_real_of_complex E).symm)
        (complexOrientation E) :=
  Manifold.OrientationLift.orientationAt_ofHasGroupoid _ _ x

end RestrictScalars

/-! ### Recharting along complex continuous linear equivalences -/

section ComplexLinearEquiv

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Recharting a boundaryless complex model `I` along a complex continuous linear equivalence
`e : E ≃L[ℂ] F` transports `I.complexManifoldOrientation M` along `e.restrictScalars' ℝ` to the
canonical orientation of `(M, I.transContinuousLinearEquiv e)`, up to the index cast induced by
`finrank ℂ E = finrank ℂ F`. -/
theorem orientationAt_transContinuousLinearEquiv_complexManifoldOrientation
    (e : E ≃L[ℂ] F) (x : M) :
    ((I.complexManifoldOrientation M).transContinuousLinearEquiv
        (e.restrictScalars' ℝ)).orientationAt x =
      Orientation.reindex ℝ F (finCongr (by rw [e.toLinearEquiv.finrank_eq]))
        (((I.transContinuousLinearEquiv e).complexManifoldOrientation M).orientationAt x) := by
  have htr := (I.isOrientedAtlas_maximalAtlas_complex (M := M) 1
      ).orientation_transContinuousLinearEquiv
    (complexOrientation E) card_fin_two_mul_finrank_complex (e.restrictScalars' ℝ)
  rw [ModelWithCorners.complexManifoldOrientation, htr,
    IsOrientedAtlas.orientationAt_orientation _ _ _ (IsManifold.chart_mem_maximalAtlas x),
    ContinuousLinearEquiv.restrictScalars'_toLinearEquiv, e.toLinearEquiv.map_complexOrientation,
    (I.transContinuousLinearEquiv e).orientationAt_complexManifoldOrientation_eq_complexOrientation]

/-- For a complex continuous linear equivalence `e : E ≃L[ℂ] F`, the real derivative of
`ContinuousLinearEquiv.toTransContinuousLinearEquiv` carries `I.complexManifoldOrientation M` at `x`
to `(I.transContinuousLinearEquiv e).complexManifoldOrientation M`, up to the index cast from
`finrank ℂ E = finrank ℂ F`. -/
theorem map_orientationAt_toTransContinuousLinearEquiv_complexManifoldOrientation
    {m : ℕ∞ω} (e : E ≃L[ℂ] F) (x : M)
    (D : TangentSpace (I.restrictScalars ℝ) x ≃L[ℝ]
      TangentSpace ((I.restrictScalars ℝ).transContinuousLinearEquiv (e.restrictScalars' ℝ))
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m)
          (I.restrictScalars ℝ) M (e.restrictScalars' ℝ) x))
    (hD : (D : TangentSpace (I.restrictScalars ℝ) x →L[ℝ] _) =
      mfderiv (I.restrictScalars ℝ)
        ((I.restrictScalars ℝ).transContinuousLinearEquiv (e.restrictScalars' ℝ))
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m)
          (I.restrictScalars ℝ) M (e.restrictScalars' ℝ)) x) :
    Orientation.map _ D.toLinearEquiv ((I.complexManifoldOrientation M).orientationAt x) =
      Orientation.reindex ℝ F (finCongr (by rw [e.toLinearEquiv.finrank_eq]))
        (((I.transContinuousLinearEquiv e).complexManifoldOrientation M).orientationAt
          (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m)
            (I.restrictScalars ℝ) M (e.restrictScalars' ℝ) x)) :=
  ((I.complexManifoldOrientation M).map_orientationAt_id_transContinuousLinearEquiv
    (e.restrictScalars' ℝ) x D hD).trans
    (I.orientationAt_transContinuousLinearEquiv_complexManifoldOrientation e x)

/-- Recharting `I` along a complex continuous linear automorphism `e : E ≃L[ℂ] E` transports
`I.complexManifoldOrientation M` along `e.restrictScalars' ℝ` directly to
`(I.transContinuousLinearEquiv e).complexManifoldOrientation M`. -/
@[simp]
theorem complexManifoldOrientation_transContinuousLinearEquiv_self
    (e : E ≃L[ℂ] E) :
    ((I.transContinuousLinearEquiv e).complexManifoldOrientation M).congrModel
        (I.restrictScalars_transContinuousLinearEquiv ℝ e) =
      (I.complexManifoldOrientation M).transContinuousLinearEquiv (e.restrictScalars' ℝ) := by
  ext x
  rw [Manifold.Orientation.orientationAt_congrModel,
    I.orientationAt_transContinuousLinearEquiv_complexManifoldOrientation e x]
  simp only [finCongr_refl, Orientation.reindex_refl, Equiv.refl_apply,
    orientationAt_complexManifoldOrientation_eq_complexOrientation]
  -- Both tangent spaces at `x` are the model space `E`, with their own scalar structures.
  rfl

/-- Recharting `I` along a complex continuous linear automorphism `e : E ≃L[ℂ] E` transports
`I.complexOrientationLift M` along `e.restrictScalars' ℝ` directly to
`(I.transContinuousLinearEquiv e).complexOrientationLift M`. -/
@[simp]
theorem complexOrientationLift_transContinuousLinearEquiv_self
    (e : E ≃L[ℂ] E) :
    ((I.transContinuousLinearEquiv e).complexOrientationLift M).congrModel
        (I.restrictScalars_transContinuousLinearEquiv ℝ e) =
      (I.complexOrientationLift M).transContinuousLinearEquiv (e.restrictScalars' ℝ) := by
  ext α x
  · simp only [Manifold.OrientationLift.congrModel_modelOrientation,
      complexOrientationLift_modelOrientation,
      Manifold.OrientationLift.transContinuousLinearEquiv_modelOrientation,
      ContinuousLinearEquiv.restrictScalars'_toLinearEquiv]
    rw [Orientation.map_reindex, e.toLinearEquiv.map_complexOrientation_self]
  · simp

/-- For a complex continuous linear automorphism `e : E ≃L[ℂ] E`, the identity map from `(M, I)` to
`(M, I.transContinuousLinearEquiv e)` preserves canonical orientations at every point. -/
@[simp]
theorem isOrientationPreservingAt_id_complexManifoldOrientation_transContinuousLinearEquiv_self
    (e : E ≃L[ℂ] E) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (I.complexManifoldOrientation M)
      ((I.transContinuousLinearEquiv e).complexManifoldOrientation M) (id : M → M) x := by
  rw [← Manifold.Orientation.isOrientationPreservingAt_congrModel_right
      (I.restrictScalars_transContinuousLinearEquiv ℝ e),
    I.complexManifoldOrientation_transContinuousLinearEquiv_self e]
  exact Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv _ _ x

/-- For a complex continuous linear automorphism `e : E ≃L[ℂ] E`, the orientation sign of `id`
between canonical orientations on `(M, I)` and `(M, I.transContinuousLinearEquiv e)` is `1`. -/
@[simp]
theorem orientationSign_id_complexManifoldOrientation_transContinuousLinearEquiv_self
    (e : E ≃L[ℂ] E) (x : M) :
    Manifold.Orientation.orientationSign (I.complexManifoldOrientation M)
      ((I.transContinuousLinearEquiv e).complexManifoldOrientation M) (id : M → M) x = 1 :=
  Manifold.Orientation.orientationSign_of_isOrientationPreservingAt
    (I.isOrientationPreservingAt_id_complexManifoldOrientation_transContinuousLinearEquiv_self e x)

end ComplexLinearEquiv

/-! ### Recharting along real continuous linear equivalences and sign of the real determinant -/

section RealLinearEquiv

variable {E G H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Transporting `I.complexManifoldOrientation M` along a real continuous linear equivalence
`e : E ≃L[ℝ] G` gives the manifold orientation of `(M, (I.restrictScalars ℝ).trans e)` determined
by the maximal holomorphic atlas and `Orientation.map _ e.toLinearEquiv (complexOrientation E)`.
By `Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv`, the comparison
diffeomorphism always preserves this transported orientation with sign `1`. -/
theorem transContinuousLinearEquiv_complexManifoldOrientation_eq (e : E ≃L[ℝ] G) :
    (I.complexManifoldOrientation M).transContinuousLinearEquiv e =
      ((isOrientedAtlas_transContinuousLinearEquiv_iff (I.restrictScalars ℝ) 1 e).2
        (I.isOrientedAtlas_maximalAtlas_complex 1)).orientation
        (Orientation.map _ e.toLinearEquiv (complexOrientation E))
        (card_fin_two_mul_finrank_complex.trans e.toLinearEquiv.finrank_eq) :=
  (I.isOrientedAtlas_maximalAtlas_complex 1).orientation_transContinuousLinearEquiv _ _ e

/-- Against the separately fixed canonical orientation `complexOrientation E` on `E`, transporting
`I.complexManifoldOrientation M` along `e : E ≃L[ℝ] E` gives the fixed-model orientation when
`0 < LinearMap.det e`. -/
theorem transContinuousLinearEquiv_complexManifoldOrientation_eq_of_det_pos
    {e : E ≃L[ℝ] E} (he : 0 < LinearMap.det (e : E →ₗ[ℝ] E)) :
    (I.complexManifoldOrientation M).transContinuousLinearEquiv e =
      Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid
          (I := (I.restrictScalars ℝ).transContinuousLinearEquiv e)
          (complexOrientation E) card_fin_two_mul_finrank_complex) := by
  rw [I.complexManifoldOrientation_eq_mk_ofHasGroupoid,
    Manifold.Orientation.transContinuousLinearEquiv_mk,
    Manifold.OrientationLift.ofHasGroupoid_transContinuousLinearEquiv]
  congr 2
  exact (Orientation.map_eq_iff_det_pos (complexOrientation E) e.toLinearEquiv
    card_fin_two_mul_finrank_complex).2 he

/-- Against the separately fixed canonical orientation `complexOrientation E` on `E`, transporting
`I.complexManifoldOrientation M` along `e : E ≃L[ℝ] E` gives the opposite of the fixed-model
orientation when `LinearMap.det e < 0`. -/
theorem transContinuousLinearEquiv_complexManifoldOrientation_eq_neg_of_det_neg
    {e : E ≃L[ℝ] E} (he : LinearMap.det (e : E →ₗ[ℝ] E) < 0) :
    (I.complexManifoldOrientation M).transContinuousLinearEquiv e =
      -Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid
          (I := (I.restrictScalars ℝ).transContinuousLinearEquiv e)
          (complexOrientation E) card_fin_two_mul_finrank_complex) := by
  rw [I.complexManifoldOrientation_eq_mk_ofHasGroupoid,
    Manifold.Orientation.transContinuousLinearEquiv_mk,
    Manifold.OrientationLift.ofHasGroupoid_transContinuousLinearEquiv,
    (Orientation.map_eq_neg_iff_det_neg (complexOrientation E) e.toLinearEquiv
      card_fin_two_mul_finrank_complex).2 he,
    Manifold.Orientation.neg_mk]
  congr 1
  ext α x <;> simp

/-- Against the separately fixed canonical orientation `complexOrientation E` on `E`, real
recharting along `e : E ≃L[ℝ] E` preserves orientation when `0 < LinearMap.det e`. -/
theorem isOrientationPreservingAt_toTransContinuousLinearEquiv_of_det_pos
    {m : ℕ∞ω} {e : E ≃L[ℝ] E} (he : 0 < LinearMap.det (e : E →ₗ[ℝ] E))
    (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (I.complexManifoldOrientation M)
      (Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid
          (I := (I.restrictScalars ℝ).transContinuousLinearEquiv e)
          (complexOrientation E) card_fin_two_mul_finrank_complex))
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m)
        (I.restrictScalars ℝ) M e) x := by
  rw [← I.transContinuousLinearEquiv_complexManifoldOrientation_eq_of_det_pos he]
  exact Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv _ e x

/-- Against the separately fixed canonical orientation `complexOrientation E` on `E`, real
recharting along `e : E ≃L[ℝ] E` reverses orientation when `LinearMap.det e < 0`. -/
theorem isOrientationReversingAt_toTransContinuousLinearEquiv_of_det_neg
    {m : ℕ∞ω} {e : E ≃L[ℝ] E} (he : LinearMap.det (e : E →ₗ[ℝ] E) < 0)
    (x : M) :
    Manifold.Orientation.IsOrientationReversingAt (I.complexManifoldOrientation M)
      (Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid
          (I := (I.restrictScalars ℝ).transContinuousLinearEquiv e)
          (complexOrientation E) card_fin_two_mul_finrank_complex))
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m)
        (I.restrictScalars ℝ) M e) x := by
  rw [← Manifold.Orientation.isOrientationPreservingAt_neg_right,
    ← I.transContinuousLinearEquiv_complexManifoldOrientation_eq_neg_of_det_neg he]
  exact Manifold.Orientation.isOrientationPreservingAt_id_transContinuousLinearEquiv _ e x

/-- Comparing `I.complexManifoldOrientation M` with the orientation on
`(M, (I.restrictScalars ℝ).transContinuousLinearEquiv e)` induced by the separately fixed canonical
model orientation `complexOrientation E` has `orientationSign` equal to the sign of the real
determinant of `e : E ≃L[ℝ] E`. -/
theorem orientationSign_toTransContinuousLinearEquiv_complexManifoldOrientation
    {m : ℕ∞ω} (e : E ≃L[ℝ] E) (x : M) :
    Manifold.Orientation.orientationSign (I.complexManifoldOrientation M)
        (Manifold.Orientation.mk
          (Manifold.OrientationLift.ofHasGroupoid
            (I := (I.restrictScalars ℝ).transContinuousLinearEquiv e)
            (complexOrientation E) card_fin_two_mul_finrank_complex))
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m)
          (I.restrictScalars ℝ) M e) x =
      (SignType.sign (LinearMap.det (e : E →ₗ[ℝ] E)) : ℤ) := by
  rw [I.complexManifoldOrientation_eq_mk_ofHasGroupoid]
  exact Manifold.OrientationLift.orientationSign_toTransContinuousLinearEquiv_ofHasGroupoid
    (complexOrientation E) card_fin_two_mul_finrank_complex e x

end RealLinearEquiv

end ModelWithCorners

namespace TauCeti

open scoped ComplexManifold

section SelfAndSpecializations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A complex manifold modelled on a boundaryless complex model `I` is orientable over
`I.restrictScalars ℝ`. -/
instance orientable_restrictScalars_of_complex {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    Orientable (I.restrictScalars ℝ) M :=
  Orientable.of_hasGroupoid

/-- On the self-model `𝓘(ℂ, E)`, `ModelWithCorners.complexManifoldOrientation` agrees with
`TauCeti.complexManifoldOrientation` under `modelWithCornersSelf_restrictScalars`. -/
@[simp]
theorem modelWithCornersSelf_complexManifoldOrientation
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) 1 X] :
    (𝓘(ℂ, E).complexManifoldOrientation X).congrModel (modelWithCornersSelf_restrictScalars ℝ) =
      complexManifoldOrientation E X := by
  ext x
  simp only [Manifold.Orientation.orientationAt_congrModel,
    ModelWithCorners.orientationAt_complexManifoldOrientation_eq_complexOrientation,
    orientationAt_complexManifoldOrientation_eq_complexOrientation]
  -- Both tangent spaces at `x` are the model space `E`, with their own scalar structures.
  rfl

/-- On the self-model `𝓘(ℂ, E)`, `ModelWithCorners.complexOrientationLift` agrees with
`TauCeti.complexOrientationLift` under `modelWithCornersSelf_restrictScalars`. -/
@[simp]
theorem modelWithCornersSelf_complexOrientationLift
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) 1 X] :
    (𝓘(ℂ, E).complexOrientationLift X).congrModel (modelWithCornersSelf_restrictScalars ℝ) =
      complexOrientationLift E X := by
  ext α x <;> simp

/-- Comparing `complexManifoldOrientation E X` against the fixed model orientation
`complexOrientation E` after recharting `𝓘(ℝ, E)` along `e : E ≃L[ℝ] E` has `orientationSign` equal
to the sign of `LinearMap.det e`. -/
theorem orientationSign_toTransContinuousLinearEquiv_complexManifoldOrientation
    {m : ℕ∞ω} {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold 𝓘(ℂ, E) 1 X] (e : E ≃L[ℝ] E) (x : X) :
    Manifold.Orientation.orientationSign (complexManifoldOrientation E X)
        (Manifold.Orientation.mk
          (Manifold.OrientationLift.ofHasGroupoid (I := 𝓘(ℝ, E).transContinuousLinearEquiv e)
            (complexOrientation E) card_fin_two_mul_finrank_complex))
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m) 𝓘(ℝ, E) X e) x =
      (SignType.sign (LinearMap.det (e : E →ₗ[ℝ] E)) : ℤ) := by
  have h : complexManifoldOrientation E X =
      Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid (I := 𝓘(ℝ, E)) (complexOrientation E)
          card_fin_two_mul_finrank_complex) := by
    ext y
    simp only [orientationAt_complexManifoldOrientation_eq_complexOrientation,
      Manifold.Orientation.orientationAt_mk, Manifold.OrientationLift.orientationAt_ofHasGroupoid]
    -- The tangent space at `y` is the model space `E`, with its own scalar structure.
    rfl
  rw [h]
  exact Manifold.OrientationLift.orientationSign_toTransContinuousLinearEquiv_ofHasGroupoid
    (complexOrientation E) card_fin_two_mul_finrank_complex e x

end SelfAndSpecializations

section Conj

/-- On a 1-dimensional complex manifold `X` modelled on `𝓘(ℂ, ℂ)`, recharting the underlying real
model along complex conjugation `Complex.conjCLE : ℂ ≃L[ℝ] ℂ` reverses orientation relative to the
separately fixed canonical orientation `complexOrientation ℂ` (since `det conjCLE = -1 < 0`). -/
theorem isOrientationReversingAt_toTransContinuousLinearEquiv_conjCLE
    {m : ℕ∞ω} {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) 1 X] (x : X) :
    Manifold.Orientation.IsOrientationReversingAt (complexManifoldOrientation ℂ X)
      (Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid
          (I := 𝓘(ℝ, ℂ).transContinuousLinearEquiv Complex.conjCLE)
          (complexOrientation ℂ) card_fin_two_mul_finrank_complex))
      (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := m)
        𝓘(ℝ, ℂ) X Complex.conjCLE) x := by
  have hdet : LinearMap.det (Complex.conjCLE : ℂ →ₗ[ℝ] ℂ) < 0 := by
    have h : (Complex.conjCLE : ℂ →ₗ[ℝ] ℂ) = Complex.conjAe.toLinearEquiv.toLinearMap := rfl
    rw [h, Complex.det_conjAe]
    norm_num
  have h :=
    𝓘(ℂ, ℂ).isOrientationReversingAt_toTransContinuousLinearEquiv_of_det_neg
      (M := X) (m := m) hdet x
  have hmod :
      ((𝓘(ℂ, ℂ).restrictScalars ℝ).transContinuousLinearEquiv Complex.conjCLE) =
        𝓘(ℝ, ℂ).transContinuousLinearEquiv Complex.conjCLE := by
    rw [modelWithCornersSelf_restrictScalars]
  have ho :
      (Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid
          (I := (𝓘(ℂ, ℂ).restrictScalars ℝ).transContinuousLinearEquiv Complex.conjCLE)
          (M := X) (complexOrientation ℂ) card_fin_two_mul_finrank_complex)).congrModel hmod =
        Manifold.Orientation.mk
          (Manifold.OrientationLift.ofHasGroupoid
            (I := 𝓘(ℝ, ℂ).transContinuousLinearEquiv Complex.conjCLE)
            (M := X) (complexOrientation ℂ) card_fin_two_mul_finrank_complex) := by
    ext y
    simp only [Manifold.Orientation.orientationAt_congrModel, Manifold.Orientation.orientationAt_mk,
      Manifold.OrientationLift.orientationAt_ofHasGroupoid]
    -- Both tangent spaces at `y` are `ℂ`, with their own scalar structures.
    rfl
  rw [← modelWithCornersSelf_complexManifoldOrientation, ← ho,
    Manifold.Orientation.isOrientationReversingAt_congrModel_left,
    Manifold.Orientation.isOrientationReversingAt_congrModel_right]
  exact h

/-- On a 1-dimensional complex manifold `X` modelled on `𝓘(ℂ, ℂ)`, the orientation sign of `id`
from `complexManifoldOrientation ℂ X` to the orientation on
`𝓘(ℝ, ℂ).transContinuousLinearEquiv Complex.conjCLE` with fixed model orientation
`complexOrientation ℂ` is `-1`. -/
@[simp]
theorem orientationSign_id_conjCLE
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) 1 X] (x : X) :
    Manifold.Orientation.orientationSign (complexManifoldOrientation ℂ X)
      (Manifold.Orientation.mk
        (Manifold.OrientationLift.ofHasGroupoid
          (I := 𝓘(ℝ, ℂ).transContinuousLinearEquiv Complex.conjCLE)
          (complexOrientation ℂ) card_fin_two_mul_finrank_complex))
      (id : X → X) x = -1 :=
  Manifold.Orientation.orientationSign_of_isOrientationReversingAt
    (isOrientationReversingAt_toTransContinuousLinearEquiv_conjCLE (m := 1) x)

end Conj

section Euclidean

/-- A complex manifold modelled on `𝓘(ℂ, EuclideanSpace ℂ (Fin d))` has orientation-preserving
coordinate changes over `complexEuclideanRealModel d`. -/
instance hasGroupoid_orientationPreservingGroupoid_complexEuclideanRealModel {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin d)) X]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) 1 X] :
    HasGroupoid X (orientationPreservingGroupoid (complexEuclideanRealModel d)) := by
  rw [complexEuclideanRealModel_def]
  infer_instance

/-- Recharting `complexManifoldOrientation (EuclideanSpace ℂ (Fin d)) X` along
`complexEuclideanRealLinearIsometryEquiv d` to `complexEuclideanRealModel d` gives the standard
basis orientation of `EuclideanSpace ℝ (Fin (2 * d))` in every preferred chart, up to the index cast
from `finrank ℂ (EuclideanSpace ℂ (Fin d)) = d`. -/
@[simp]
theorem orientationAt_complexManifoldOrientation_complexEuclideanRealModel {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin d)) X]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) 1 X] (x : X) :
    (((complexManifoldOrientation (EuclideanSpace ℂ (Fin d)) X).transContinuousLinearEquiv
        (complexEuclideanRealLinearIsometryEquiv d).toContinuousLinearEquiv).congrModel
        (complexEuclideanRealModel_def d).symm).orientationAt x =
      Orientation.reindex ℝ _ (finCongr (by rw [finrank_euclideanSpace_fin]))
        (EuclideanSpace.basisFun (Fin (2 * d)) ℝ).toBasis.orientation := by
  have htr := (isOrientedAtlas_maximalAtlas_complex (E := EuclideanSpace ℂ (Fin d)) (M := X) 1
      ).orientation_transContinuousLinearEquiv (complexOrientation (EuclideanSpace ℂ (Fin d)))
    card_fin_two_mul_finrank_complex
    (complexEuclideanRealLinearIsometryEquiv d).toContinuousLinearEquiv
  rw [Manifold.Orientation.orientationAt_congrModel, complexManifoldOrientation, htr,
    IsOrientedAtlas.orientationAt_orientation _ _ _ (IsManifold.chart_mem_maximalAtlas x)]
  exact map_complexEuclideanRealLinearIsometryEquiv_complexOrientation d

end Euclidean

end TauCeti
