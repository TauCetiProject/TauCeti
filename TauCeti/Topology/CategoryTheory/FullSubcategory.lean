/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Topology.Maps.Proper.Basic

/-!
# Full restrictions of topological groupoids

Let `C` be a category whose objects and total arrows `Quiver.Total C` carry topologies, as for a
topological groupoid, and let `P` be a property of objects. The full subcategory
`P.FullSubcategory` is the full restriction `C|U` to the set `U` of objects satisfying `P`: it
keeps every arrow of `C` between objects of `U`. Its objects get the subspace topology of `U`,
and its total arrows the subspace topology of the arrows with both endpoints in `U`.

The hypotheses of a Hausdorff proper étale presentation pass to these restrictions:

* the total arrows remain Hausdorff and second countable, and continuity of source, target, units,
  composition and inversion is inherited;
* the source-target map stays proper for every `P`
  (`TauCeti.isProperMap_source_target_fullSubcategory`), since its restriction is the pullback of
  the original map along the embedding `U × U → C × C`;
* when `U` is open, source and target remain local homeomorphisms
  (`TauCeti.isLocalHomeomorph_source_fullSubcategory`,
  `TauCeti.isLocalHomeomorph_target_fullSubcategory`), because the restricted total arrows form an
  open subspace of the original ones (`TauCeti.isOpenEmbedding_total_fullSubcategory`).

No saturation of `U` is needed. All isotropy arrows at objects of `U` are kept, including those
acting trivially, so the restriction does not discard ineffective isotropy.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti

variable {C : Type*} [Category C] {P : ObjectProperty C}

/-- The total arrows of a full subcategory are exactly the ambient total arrows with both
endpoints satisfying `P`. -/
theorem range_total_fullSubcategory :
    range (fun a : Quiver.Total P.FullSubcategory ↦
      (⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C)) =
      {a : Quiver.Total C | P a.left ∧ P a.right} := by
  ext ⟨x, y, f⟩
  refine ⟨?_, fun ⟨hx, hy⟩ ↦ ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, ObjectProperty.homMk f⟩, rfl⟩⟩
  rintro ⟨a, ha⟩
  rw [← ha]
  exact ⟨a.left.property, a.right.property⟩

section Objects

variable [TopologicalSpace C]

variable (P) in
/-- The objects of a full subcategory carry the subspace topology. -/
instance instTopologicalSpaceFullSubcategory : TopologicalSpace P.FullSubcategory :=
  .induced ObjectProperty.FullSubcategory.obj inferInstance

/-- The objects of a full subcategory are embedded in the ambient objects. -/
theorem isEmbedding_obj_fullSubcategory :
    IsEmbedding (ObjectProperty.FullSubcategory.obj : P.FullSubcategory → C) :=
  ⟨⟨rfl⟩, fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h⟩

/-- The objects of a full subcategory on an open set of objects form an open subspace. -/
theorem isOpenEmbedding_obj_fullSubcategory (hP : IsOpen {x | P x}) :
    IsOpenEmbedding (ObjectProperty.FullSubcategory.obj : P.FullSubcategory → C) :=
  ⟨isEmbedding_obj_fullSubcategory, by
    convert hP
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩⟩

/-- The objects of a full subcategory of a category with Hausdorff objects are Hausdorff. -/
instance instT2SpaceFullSubcategory [T2Space C] : T2Space P.FullSubcategory :=
  isEmbedding_obj_fullSubcategory.t2Space

/-- The objects of a full subcategory of a category with second-countable objects are second
countable. -/
instance instSecondCountableTopologyFullSubcategory [SecondCountableTopology C] :
    SecondCountableTopology P.FullSubcategory :=
  isEmbedding_obj_fullSubcategory.isInducing.secondCountableTopology

end Objects

variable [TopologicalSpace (Quiver.Total C)]

variable (P) in
/-- The total arrows of a full subcategory carry the subspace topology of the total arrows of the
ambient category. -/
instance instTopologicalSpaceTotalFullSubcategory :
    TopologicalSpace (Quiver.Total P.FullSubcategory) :=
  .induced (fun a ↦ (⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C)) inferInstance

/-- The total arrows of a full subcategory are embedded in the ambient total arrows. -/
theorem isEmbedding_total_fullSubcategory :
    IsEmbedding (fun a : Quiver.Total P.FullSubcategory ↦
      (⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C)) := by
  refine ⟨⟨rfl⟩, ?_⟩
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, f⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩, f'⟩ h
  simp only [Quiver.Total.mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  cases ObjectProperty.hom_ext _ (f := f) (g := f') (eq_of_heq h)
  rfl

/-- The total arrows of a full subcategory of a category with Hausdorff total arrows are
Hausdorff. -/
instance instT2SpaceTotalFullSubcategory [T2Space (Quiver.Total C)] :
    T2Space (Quiver.Total P.FullSubcategory) :=
  isEmbedding_total_fullSubcategory.t2Space

/-- The total arrows of a full subcategory of a category with second-countable total arrows are
second countable. -/
instance instSecondCountableTopologyTotalFullSubcategory
    [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology (Quiver.Total P.FullSubcategory) :=
  isEmbedding_total_fullSubcategory.isInducing.secondCountableTopology

/-- Composition in a full subcategory is continuous on composable pairs when the ambient
composition is. -/
theorem continuous_comp_fullSubcategory
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C)) :
    Continuous fun p : {p : Quiver.Total P.FullSubcategory × Quiver.Total P.FullSubcategory //
        p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ :
        Quiver.Total P.FullSubcategory) := by
  let ι := fun a : Quiver.Total P.FullSubcategory ↦
    (⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C)
  let g := fun p : {p : Quiver.Total P.FullSubcategory × Quiver.Total P.FullSubcategory //
      p.1.right = p.2.left} ↦
    (⟨(ι p.1.1, ι p.1.2), congrArg ObjectProperty.FullSubcategory.obj p.2⟩ :
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})
  have hι : Continuous ι := isEmbedding_total_fullSubcategory.continuous
  have hg : Continuous g := ((hι.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (hι.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  refine isEmbedding_total_fullSubcategory.continuous_iff.mpr ?_
  convert hc.comp hg using 1
  funext ⟨⟨⟨x, y, f⟩, ⟨y', z, f'⟩⟩, h⟩
  dsimp only at h
  subst h
  simp [g, ι]

/-- Inversion in a full subcategory of a groupoid is continuous when the ambient inversion is. -/
theorem continuous_inverse_fullSubcategory {G : Type*} [Groupoid G]
    [TopologicalSpace (Quiver.Total G)] {P : ObjectProperty G}
    (hi : Continuous fun a : Quiver.Total G ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total G)) :
    Continuous fun a : Quiver.Total P.FullSubcategory ↦
      (⟨a.right, a.left, ObjectProperty.homMk (inv a.hom.hom)⟩ :
        Quiver.Total P.FullSubcategory) :=
  -- The inclusion sends the restricted inverse to the ambient one by `ObjectProperty.homMk_hom`.
  isEmbedding_total_fullSubcategory.continuous_iff.mpr
    (hi.comp isEmbedding_total_fullSubcategory.continuous)

variable [TopologicalSpace C]

/-- With continuous source and target, the total arrows of a full subcategory on an open set of
objects form an open subspace of the ambient total arrows. -/
theorem isOpenEmbedding_total_fullSubcategory (hP : IsOpen {x | P x})
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) :
    IsOpenEmbedding (fun a : Quiver.Total P.FullSubcategory ↦
      (⟨a.left.obj, a.right.obj, a.hom.hom⟩ : Quiver.Total C)) :=
  ⟨isEmbedding_total_fullSubcategory, by
    rw [range_total_fullSubcategory]
    exact (hP.preimage hs).inter (hP.preimage ht)⟩

/-- The source of a full subcategory is continuous when the ambient source is. -/
theorem continuous_source_fullSubcategory
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C)) :
    Continuous (Quiver.Total.left : Quiver.Total P.FullSubcategory → P.FullSubcategory) :=
  isEmbedding_obj_fullSubcategory.continuous_iff.mpr
    (hs.comp isEmbedding_total_fullSubcategory.continuous)

/-- The target of a full subcategory is continuous when the ambient target is. -/
theorem continuous_target_fullSubcategory
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) :
    Continuous (Quiver.Total.right : Quiver.Total P.FullSubcategory → P.FullSubcategory) :=
  isEmbedding_obj_fullSubcategory.continuous_iff.mpr
    (ht.comp isEmbedding_total_fullSubcategory.continuous)

/-- On an open set of objects, the source of a full subcategory is a local homeomorphism when
the ambient source is one and the ambient target is continuous. -/
theorem isLocalHomeomorph_source_fullSubcategory (hP : IsOpen {x | P x})
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) :
    IsLocalHomeomorph
      (Quiver.Total.left : Quiver.Total P.FullSubcategory → P.FullSubcategory) :=
  .of_comp (g := ObjectProperty.FullSubcategory.obj)
    (hs.comp (isOpenEmbedding_total_fullSubcategory hP hs.continuous ht).isLocalHomeomorph)
    (isOpenEmbedding_obj_fullSubcategory hP).isLocalHomeomorph
    (continuous_source_fullSubcategory hs.continuous)

/-- On an open set of objects, the target of a full subcategory is a local homeomorphism when
the ambient target is one and the ambient source is continuous. -/
theorem isLocalHomeomorph_target_fullSubcategory (hP : IsOpen {x | P x})
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C)) :
    IsLocalHomeomorph
      (Quiver.Total.right : Quiver.Total P.FullSubcategory → P.FullSubcategory) :=
  .of_comp (g := ObjectProperty.FullSubcategory.obj)
    (ht.comp (isOpenEmbedding_total_fullSubcategory hP hs ht.continuous).isLocalHomeomorph)
    (isOpenEmbedding_obj_fullSubcategory hP).isLocalHomeomorph
    (continuous_target_fullSubcategory ht.continuous)

/-- The source-target map of a full subcategory is proper when the ambient source-target map
is. No openness of the set of objects is needed. -/
theorem isProperMap_source_target_fullSubcategory
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right))) :
    IsProperMap (fun a : Quiver.Total P.FullSubcategory ↦ (a.left, a.right)) := by
  refine hp.of_isEmbedding_of_range_eq isEmbedding_total_fullSubcategory
    (isEmbedding_obj_fullSubcategory.prodMap isEmbedding_obj_fullSubcategory) rfl ?_
  rw [range_total_fullSubcategory]
  ext a
  exact ⟨fun ⟨hx, hy⟩ ↦ ⟨(⟨a.left, hx⟩, ⟨a.right, hy⟩), rfl⟩,
    fun ⟨⟨x, y⟩, h⟩ ↦ by
      simp only [Prod.map_apply, Prod.mk.injEq] at h
      exact ⟨h.1 ▸ x.property, h.2 ▸ y.property⟩⟩

/-- The unit map of a full subcategory is continuous when the ambient unit map is. -/
theorem continuous_unit_fullSubcategory
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    Continuous fun x : P.FullSubcategory ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total P.FullSubcategory) :=
  -- The inclusion sends units to units by `ObjectProperty.FullSubcategory.id_hom`.
  isEmbedding_total_fullSubcategory.continuous_iff.mpr
    (hu.comp isEmbedding_obj_fullSubcategory.continuous)

end TauCeti
