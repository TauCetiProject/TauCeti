/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.RestrictScalars
public import TauCeti.Geometry.Manifold.Orientation.Atlas
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.LinearAlgebra.Complex.Orientation
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

## Main declarations

* `TauCeti.orientationPreservingOn_iff_det_fderiv_ne_zero`: a holomorphic map preserves the real
  orientation exactly where its complex derivative has nonzero determinant.
* `TauCeti.contDiffGroupoid_complex_le_orientationPreservingGroupoid`: holomorphic coordinate
  changes preserve orientation; contrast
  `TauCeti.not_contDiffGroupoid_le_orientationPreservingGroupoid`.
* `TauCeti.isOrientedAtlas_maximalAtlas_complex`: the holomorphic charts form an oriented atlas.
* `TauCeti.complexManifoldOrientation`: the canonical orientation of a complex manifold.
* `TauCeti.orientationAt_complexManifoldOrientation`: its tangent orientation at a point, read
  through any holomorphic chart.
* `TauCeti.complexOrientationLift`: the canonical orientation as a lift indexed by
  `Fin (finrank ℝ E)`, with all chart signs `1` (`TauCeti.complexOrientationLift_sign`).
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

## Implementation notes

Tangent orientations are stated for the underlying real manifold structure
`IsManifold 𝓘(ℝ, E) n M`, obtained from the complex one by `IsManifold.restrictScalars`. This
file provides it as the scoped instance `TauCeti.ComplexManifold.isManifold_real`, so callers
enable it with `open scoped TauCeti.ComplexManifold`. Since `IsManifold` is a `Prop`, any other
proof of the real structure works as well.

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
private theorem card_fin_two_mul_finrank_complex :
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
