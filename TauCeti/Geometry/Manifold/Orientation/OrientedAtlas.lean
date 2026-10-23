/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.LinearAlgebra.Determinant

/-!
# Orientation-preserving coordinate changes and oriented atlases

Within-range transition derivatives define the orientation-preserving groupoid and oriented
subatlases, including at boundary and corner points. An oriented atlas supplies an orientation;
the interval is orientable although its half-line charts have opposite transition signs.

## Main declarations

* `orientationPreservingGroupoid` and `IsOrientedAtlas`: positive transitions and oriented atlases.
* `IsOrientedAtlas.det_fderivWithin_pos` and `IsOrientedAtlas.prod`: determinants and products.
* `not_contDiffGroupoid_le_orientationPreservingGroupoid`: smooth changes can reverse orientation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition, Chapter 15.
-/

public section

open Set Filter

open scoped Manifold Topology ContDiff

namespace TauCeti

section Groupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)

/-- A map `f : H → H` preserves orientation on `s`, read in the model through `I`: at the image
`I x` of each point `x ∈ s`, the coordinate expression `I ∘ f ∘ I.symm` is differentiable within
`range I`, with derivative of positive determinant. The model vector space `E` is
finite-dimensional, as determinants are only meaningful there; the determinant is that of the
matrix of the derivative in the basis `Module.finBasis ℝ E`, which is `LinearMap.det` of the
derivative (`TauCeti.orientationPreservingOn_iff`). -/
def OrientationPreservingOn [FiniteDimensional ℝ E] (f : H → H) (s : Set H) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ (I ∘ f ∘ I.symm) (range I) (I x) ∧
    0 < (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
      (fderivWithin ℝ (I ∘ f ∘ I.symm) (range I) (I x) : E →ₗ[ℝ] E)).det

variable [FiniteDimensional ℝ E] {I}

/-- Unfold `TauCeti.OrientationPreservingOn`, with the determinant of the derivative stated
basis-free as `LinearMap.det`. -/
theorem orientationPreservingOn_iff {f : H → H} {s : Set H} :
    OrientationPreservingOn I f s ↔
      ∀ x ∈ s, DifferentiableWithinAt ℝ (I ∘ f ∘ I.symm) (range I) (I x) ∧
        0 < LinearMap.det (fderivWithin ℝ (I ∘ f ∘ I.symm) (range I) (I x) : E →ₗ[ℝ] E) := by
  simp only [OrientationPreservingOn, LinearMap.det_toMatrix]

/-- Orientation preservation on a set is inherited by its subsets. -/
theorem OrientationPreservingOn.mono {f : H → H} {s t : Set H}
    (h : OrientationPreservingOn I f t) (hst : s ⊆ t) : OrientationPreservingOn I f s :=
  fun x hx => h x (hst hx)

/-- The identity preserves orientation on every set. -/
theorem orientationPreservingOn_id (s : Set H) : OrientationPreservingOn I id s := by
  rw [orientationPreservingOn_iff]
  intro x _
  have heq : EqOn (I ∘ id ∘ I.symm) id (range I) := fun y hy => I.right_inv hy
  have hx : (I ∘ id ∘ I.symm) (I x) = id (I x) := heq (mem_range_self x)
  refine ⟨differentiableWithinAt_id.congr heq hx, ?_⟩
  rw [fderivWithin_congr heq hx, fderivWithin_id I.uniqueDiffWithinAt_image]
  simp

/-- A composite of orientation-preserving maps preserves orientation. -/
theorem OrientationPreservingOn.comp {f g : H → H} {s t : Set H}
    (hg : OrientationPreservingOn I g t) (hf : OrientationPreservingOn I f s)
    (hst : MapsTo f s t) : OrientationPreservingOn I (g ∘ f) s := by
  rw [orientationPreservingOn_iff] at hg hf ⊢
  intro x hx
  have hcomp : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ (I ∘ f ∘ I.symm) := by
    ext y
    simp
  have hfx : I (f x) = (I ∘ f ∘ I.symm) (I x) := by simp
  have hmaps : MapsTo (I ∘ f ∘ I.symm) (range I) (range I) := fun _ _ => mem_range_self _
  obtain ⟨hgd, hgdet⟩ := hg (f x) (hst hx)
  obtain ⟨hfd, hfdet⟩ := hf x hx
  rw [hfx] at hgd hgdet
  rw [hcomp]
  refine ⟨hgd.comp (I x) hfd hmaps, ?_⟩
  rw [fderivWithin_comp (I x) hgd hfd hmaps I.uniqueDiffWithinAt_image,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  exact mul_pos hgdet hfdet

/-- On an open set, orientation preservation only depends on the values of the map there. -/
theorem OrientationPreservingOn.congr {f g : H → H} {s : Set H} (hs : IsOpen s)
    (h : OrientationPreservingOn I f s) (hfg : EqOn g f s) : OrientationPreservingOn I g s := by
  intro x hx
  have hnhds : I.symm ⁻¹' s ∈ 𝓝 (I x) :=
    (hs.preimage I.continuous_symm).mem_nhds (by simpa using hx)
  have heq : I ∘ g ∘ I.symm =ᶠ[𝓝[range I] (I x)] I ∘ f ∘ I.symm := by
    filter_upwards [nhdsWithin_le_nhds hnhds] with y hy
    simp [hfg hy]
  have hx' : (I ∘ g ∘ I.symm) (I x) = (I ∘ f ∘ I.symm) (I x) := by simp [hfg hx]
  obtain ⟨hd, hdet⟩ := h x hx
  exact ⟨hd.congr_of_eventuallyEq heq hx', by rwa [heq.fderivWithin_eq hx']⟩

variable (I) in
/-- Given a model with corners `(E, H)`, the pregroupoid of orientation-preserving maps of `H`:
those whose coordinate expression in `E` has derivative of positive determinant. -/
def orientationPreservingPregroupoid : Pregroupoid H where
  property := OrientationPreservingOn I
  comp hf hg _ _ _ := hg.comp (hf.mono inter_subset_left) fun _ hx => hx.2
  id_mem := orientationPreservingOn_id univ
  locality {_ _} _ hloc x hx := by
    obtain ⟨v, -, hxv, hv⟩ := hloc x hx
    exact hv x ⟨hx, hxv⟩
  congr hu hfg hf := hf.congr hu fun x hx => hfg x hx

variable (I) in
/-- Given a model with corners `(E, H)`, the groupoid of orientation-preserving open partial
homeomorphisms of `H`: both the map and its inverse have derivatives of positive determinant when
read in `E` through `I`. -/
def orientationPreservingGroupoid : StructureGroupoid H :=
  (orientationPreservingPregroupoid I).groupoid

/-- Membership in `TauCeti.orientationPreservingGroupoid`, unfolded: the map preserves orientation
on its source and its inverse preserves orientation on its target. -/
theorem mem_orientationPreservingGroupoid_iff {e : OpenPartialHomeomorph H H} :
    e ∈ orientationPreservingGroupoid I ↔
      OrientationPreservingOn I e e.source ∧ OrientationPreservingOn I e.symm e.target :=
  mem_groupoid_of_pregroupoid

/-- The identity of an open set belongs to the orientation-preserving groupoid. -/
theorem ofSet_mem_orientationPreservingGroupoid {s : Set H} (hs : IsOpen s) :
    OpenPartialHomeomorph.ofSet s hs ∈ orientationPreservingGroupoid I := by
  rw [mem_orientationPreservingGroupoid_iff]
  simp only [mfld_simps]
  exact orientationPreservingOn_id _

/-- The orientation-preserving groupoid is closed under restriction to open subsets. -/
instance : ClosedUnderRestriction (orientationPreservingGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      exact (orientationPreservingGroupoid I).mem_of_eqOnSource' _ _
        (ofSet_mem_orientationPreservingGroupoid hs) hes)

section Prod

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [FiniteDimensional ℝ E'] {I' : ModelWithCorners ℝ E' H'}

/-- A product of orientation-preserving maps preserves orientation in the product model: the
derivative of the product is block diagonal, so its determinant is the product of the two. -/
theorem OrientationPreservingOn.prodMap {f : H → H} {f' : H' → H'} {s : Set H} {s' : Set H'}
    (hf : OrientationPreservingOn I f s) (hf' : OrientationPreservingOn I' f' s') :
    OrientationPreservingOn (I.prod I') (Prod.map f f') (s ×ˢ s') := by
  rw [orientationPreservingOn_iff] at hf hf' ⊢
  rintro ⟨x, x'⟩ ⟨hx, hx'⟩
  have hcoord : (I.prod I') ∘ Prod.map f f' ∘ (I.prod I').symm =
      Prod.map (I ∘ f ∘ I.symm) (I' ∘ f' ∘ I'.symm) := by
    ext p <;> simp
  obtain ⟨hd, hdet⟩ := hf x hx
  obtain ⟨hd', hdet'⟩ := hf' x' hx'
  have hderiv : HasFDerivWithinAt (Prod.map (I ∘ f ∘ I.symm) (I' ∘ f' ∘ I'.symm))
      ((fderivWithin ℝ (I ∘ f ∘ I.symm) (range I) (I x)).prodMap
        (fderivWithin ℝ (I' ∘ f' ∘ I'.symm) (range I') (I' x')))
      (range (I.prod I')) ((I.prod I') (x, x')) := by
    rw [ModelWithCorners.range_prod]
    exact HasFDerivWithinAt.prodMap (p := (I x, I' x'))
      (hd.hasFDerivWithinAt.mono (fst_image_prod_subset _ _))
      (hd'.hasFDerivWithinAt.mono (snd_image_prod_subset _ _))
  rw [hcoord]
  refine ⟨hderiv.differentiableWithinAt, ?_⟩
  rw [hderiv.fderivWithin (I.prod I').uniqueDiffWithinAt_image, ContinuousLinearMap.coe_prodMap,
    LinearMap.det_prodMap]
  exact mul_pos hdet hdet'

/-- The product of two orientation-preserving open partial homeomorphisms preserves orientation
in the product model. -/
theorem orientationPreservingGroupoid_prod {e : OpenPartialHomeomorph H H}
    {e' : OpenPartialHomeomorph H' H'} (he : e ∈ orientationPreservingGroupoid I)
    (he' : e' ∈ orientationPreservingGroupoid I') :
    e.prod e' ∈ orientationPreservingGroupoid (I.prod I') := by
  have hcoe : ⇑(e.prod e') = Prod.map e e' := by
    ext p <;> simp
  have hcoe_symm : ⇑(e.prod e').symm = Prod.map e.symm e'.symm := by
    ext p <;> simp
  rw [mem_orientationPreservingGroupoid_iff] at he he' ⊢
  rw [hcoe, hcoe_symm, OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.prod_target]
  exact ⟨he.1.prodMap he'.1, he.2.prodMap he'.2⟩

end Prod

end Groupoid

end TauCeti

/-! ### Linear coordinate changes

On the model vector space itself, a linear automorphism preserves orientation exactly when its
determinant is positive. In particular the reflection of `ℝ` is a smooth coordinate change that
reverses orientation, so some smooth coordinate changes are excluded from the
orientation-preserving groupoid and an oriented atlas is a genuine constraint. -/

namespace ContinuousLinearMap

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A continuous linear map of the model vector space preserves orientation on a set exactly when
the set is empty or the determinant of the map is positive. -/
theorem orientationPreservingOn_iff (A : E →L[ℝ] E) {s : Set E} :
    OrientationPreservingOn 𝓘(ℝ, E) A s ↔ s = ∅ ∨ 0 < LinearMap.det (A : E →ₗ[ℝ] E) := by
  have hcoord : 𝓘(ℝ, E) ∘ A ∘ 𝓘(ℝ, E).symm = A := by
    ext x
    simp
  have hrange : range 𝓘(ℝ, E) = univ := by simp
  simp only [TauCeti.orientationPreservingOn_iff, hcoord, hrange, fderivWithin_univ, A.fderiv,
    A.differentiableAt.differentiableWithinAt, true_and]
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · exact ⟨fun h => Or.inr (h x hx), fun h y _ => h.resolve_left (nonempty_iff_ne_empty.1 ⟨x, hx⟩)⟩

end ContinuousLinearMap

namespace ContinuousLinearEquiv

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear automorphism of the model vector space, viewed as a coordinate change, belongs to the
orientation-preserving groupoid exactly when its determinant is positive. -/
theorem toHomeomorph_toOpenPartialHomeomorph_mem_orientationPreservingGroupoid_iff
    (A : E ≃L[ℝ] E) :
    A.toHomeomorph.toOpenPartialHomeomorph ∈ orientationPreservingGroupoid 𝓘(ℝ, E) ↔
      0 < LinearMap.det (A.toLinearEquiv : E →ₗ[ℝ] E) := by
  rw [mem_orientationPreservingGroupoid_iff]
  simp only [mfld_simps, coe_toHomeomorph, coe_symm_toHomeomorph]
  rw [← coe_coe, ← coe_coe A.symm, ContinuousLinearMap.orientationPreservingOn_iff,
    ContinuousLinearMap.orientationPreservingOn_iff]
  simp [toLinearEquiv_symm, LinearEquiv.det_coe_symm]

end ContinuousLinearEquiv

namespace TauCeti

/-- The reflection `x ↦ -x` of `ℝ` is a smooth coordinate change that reverses orientation: the
`C^n` groupoid of `ℝ` is not contained in the orientation-preserving groupoid. -/
theorem not_contDiffGroupoid_le_orientationPreservingGroupoid (n : ℕ∞ω) :
    ¬ contDiffGroupoid n 𝓘(ℝ, ℝ) ≤ orientationPreservingGroupoid 𝓘(ℝ, ℝ) := by
  intro hle
  let A : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.neg ℝ
  have hmem : A.toHomeomorph.toOpenPartialHomeomorph ∈ contDiffGroupoid n 𝓘(ℝ, ℝ) := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    constructor <;> simp only [contDiffPregroupoid, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, mfld_simps,
      ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.coe_symm_toHomeomorph] <;>
      exact ContDiff.contDiffOn (by fun_prop)
  have hdet := (A.toHomeomorph_toOpenPartialHomeomorph_mem_orientationPreservingGroupoid_iff).1
    (hle hmem)
  norm_num [A] at hdet

/-! ### Oriented atlases -/

section Atlas

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (n : ℕ∞ω) [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An *oriented atlas* of the `C^n` manifold `M`, for `n ≠ 0`: a family of charts from its maximal
`C^n` atlas which covers `M` and whose coordinate changes all preserve orientation. -/
structure IsOrientedAtlas [NeZero n] (A : Set (OpenPartialHomeomorph M H)) : Prop where
  /-- Every chart of an oriented atlas is compatible with the `C^n` structure of `M`. -/
  subset_maximalAtlas : A ⊆ IsManifold.maximalAtlas I n M
  /-- The charts of an oriented atlas cover `M`. -/
  exists_mem_source (x : M) : ∃ e ∈ A, x ∈ e.source
  /-- The coordinate changes of an oriented atlas preserve orientation. -/
  symm_trans_mem {e e' : OpenPartialHomeomorph M H} :
    e ∈ A → e' ∈ A → e.symm ≫ₕ e' ∈ orientationPreservingGroupoid I

variable {I n}

/-- Two charts of an oriented atlas change coordinates with derivative of positive determinant at
every point of their common domain. -/
theorem IsOrientedAtlas.det_fderivWithin_pos {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) {e e' : OpenPartialHomeomorph M H} (he : e ∈ A) (he' : e' ∈ A)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    0 < LinearMap.det
      (fderivWithin ℝ (e'.extend I ∘ (e.extend I).symm) (range I) (e.extend I x) : E →ₗ[ℝ] E) := by
  have hmem : e x ∈ (e.symm ≫ₕ e').source := by
    simpa [e.map_source hx, e.left_inv hx] using hx'
  have hcoord : e'.extend I ∘ (e.extend I).symm = I ∘ ⇑(e.symm ≫ₕ e') ∘ I.symm := by
    ext y
    simp
  rw [hcoord, OpenPartialHomeomorph.extend_coe]
  exact (orientationPreservingOn_iff.1
    (mem_orientationPreservingGroupoid_iff.1 (hA.symm_trans_mem he he')).1 (e x) hmem).2

section Prod

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [FiniteDimensional ℝ E'] {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M'] [IsManifold I n M] [IsManifold I' n M']

/-- The products of the charts of two oriented atlases form an oriented atlas of the product. -/
theorem IsOrientedAtlas.prod {A : Set (OpenPartialHomeomorph M H)}
    {A' : Set (OpenPartialHomeomorph M' H')} (hA : IsOrientedAtlas I n A)
    (hA' : IsOrientedAtlas I' n A') :
    IsOrientedAtlas (I.prod I') n (image2 OpenPartialHomeomorph.prod A A') where
  subset_maximalAtlas := by
    rintro _ ⟨e, he, e', he', rfl⟩
    exact IsManifold.mem_maximalAtlas_prod (hA.subset_maximalAtlas he)
      (hA'.subset_maximalAtlas he')
  exists_mem_source := by
    rintro ⟨x, x'⟩
    obtain ⟨e, he, hx⟩ := hA.exists_mem_source x
    obtain ⟨e', he', hx'⟩ := hA'.exists_mem_source x'
    exact ⟨e.prod e', mem_image2_of_mem he he', by simp [hx, hx']⟩
  symm_trans_mem := by
    rintro _ _ ⟨e₁, he₁, e₁', he₁', rfl⟩ ⟨e₂, he₂, e₂', he₂', rfl⟩
    rw [OpenPartialHomeomorph.prod_symm_trans_prod]
    exact orientationPreservingGroupoid_prod (hA.symm_trans_mem he₁ he₂)
      (hA'.symm_trans_mem he₁' he₂')

end Prod

end Atlas

end TauCeti
