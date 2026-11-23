/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import TauCeti.AlgebraicTopology.Quasicategory.Core

/-!
# Comparing the two homotopy categories of a quasicategory

Mathlib constructs the homotopy category of an arbitrary simplicial set by generators and
relations, and also constructs the homotopy category of a 2-truncated quasicategory by taking
homotopy classes of edges. For a quasicategory the two constructions agree. The comparison
functors here fix the vertices and the classes of edges, and are mutually inverse.

In particular an edge is an equivalence exactly when its class in the generators-and-relations
homotopy category is invertible. This is the form needed when using comparison functors out
of that homotopy category, for example for the differential graded nerve.

The comparison also describes the generators-and-relations homotopy category of a quasicategory
directly: every morphism between two vertices is the class of an edge
(`SSet.HomotopyCategory.homMk_surjective`), two edges have the same class exactly when a
`2`-simplex exhibits one as a composite of the identity and the other
(`SSet.HomotopyCategory.homMk_eq_homMk_iff`), and two vertices are isomorphic exactly when an
equivalence joins them (`SSet.HomotopyCategory.nonempty_iso_mk_iff`). Consequently a map into a
quasicategory is essentially surjective on homotopy categories exactly when every vertex of the
target is joined by an equivalence to a vertex of the image
(`SSet.essSurj_mapHomotopyCategory_iff`).

## References

* J. Lurie, *Higher Topos Theory*, §1.2.3 and §1.2.4.
-/

public section

open CategoryTheory SimplicialObject.Truncated
open scoped Simplicial

namespace SSet.Truncated

universe u

variable (X : Truncated.{u} 2) [Quasicategory₂ X]

namespace HomotopyCategory₂

/-- From homotopy classes of edges to the generators-and-relations homotopy category. -/
noncomputable def toHomotopyCategory : HomotopyCategory₂ X ⥤ X.HomotopyCategory :=
  desc HomotopyCategory.mk (fun e ↦ HomotopyCategory.homMk e)
    HomotopyCategory.homMk_id (fun h ↦ HomotopyCategory.homMk_comp_homMk h)

/-- The comparison fixes vertices. -/
@[simp]
lemma toHomotopyCategory_obj_mk (x : X _⦋0⦌₂) :
    (toHomotopyCategory X).obj (mk x) = HomotopyCategory.mk x :=
  (rfl)

/-- The comparison sends an edge class to the same edge in the generators-and-relations
homotopy category. -/
@[simp]
lemma toHomotopyCategory_map_homMk {x y : X _⦋0⦌₂} (e : Edge x y) :
    (toHomotopyCategory X).map (homMk e) =
      eqToHom (toHomotopyCategory_obj_mk X x) ≫ HomotopyCategory.homMk e ≫
        eqToHom (toHomotopyCategory_obj_mk X y).symm := by
  apply (conj_eqToHom_iff_heq' _ _ _ _).2
  unfold toHomotopyCategory
  exact heq_of_eq (desc_map_homMk ..)

end HomotopyCategory₂

namespace HomotopyCategory

/-- From the generators-and-relations homotopy category to homotopy classes of edges. -/
noncomputable def toHomotopyCategory₂ : X.HomotopyCategory ⥤ HomotopyCategory₂ X :=
  lift HomotopyCategory₂.mk (fun e ↦ HomotopyCategory₂.homMk e)
    (fun x ↦ HomotopyCategory₂.homMk_id (.mk x))
    (fun h ↦ h.homotopyCategory₂_fac)

/-- The inverse comparison fixes vertices. -/
@[simp]
lemma toHomotopyCategory₂_obj_mk (x : X _⦋0⦌₂) :
    (toHomotopyCategory₂ X).obj (mk x) = HomotopyCategory₂.mk x :=
  lift_obj_mk ..

/-- The inverse comparison sends an edge to its homotopy class. -/
@[simp]
lemma toHomotopyCategory₂_map_homMk {x y : X _⦋0⦌₂} (e : Edge x y) :
    (toHomotopyCategory₂ X).map (homMk e) =
      eqToHom (toHomotopyCategory₂_obj_mk X x) ≫ HomotopyCategory₂.homMk e ≫
        eqToHom (toHomotopyCategory₂_obj_mk X y).symm := by
  apply (conj_eqToHom_iff_heq' _ _ _ _).2
  unfold toHomotopyCategory₂
  exact heq_of_eq (lift_map_homMk ..)

/-- Taking homotopy classes of edges and then imposing the composition relations is the
identity on the generators-and-relations homotopy category. -/
@[simp]
lemma toHomotopyCategory₂_comp_toHomotopyCategory :
    toHomotopyCategory₂ X ⋙ HomotopyCategory₂.toHomotopyCategory X = 𝟭 _ := by
  refine functor_ext (fun _ ↦ by simp) ?_
  intro x y e
  simp [eqToHom_map]

end HomotopyCategory

namespace HomotopyCategory₂

/-- Imposing the composition relations and then taking homotopy classes of edges is the
identity on the edge-class homotopy category. -/
@[simp]
lemma toHomotopyCategory_comp_toHomotopyCategory₂ :
    toHomotopyCategory X ⋙ HomotopyCategory.toHomotopyCategory₂ X = 𝟭 _ := by
  refine functor_ext (fun _ ↦ by simp) ?_
  intro x y e
  simp [eqToHom_map]

/-- The edge-class and generators-and-relations homotopy categories are canonically equivalent,
by functors which are inverse on the nose. -/
noncomputable def equivalence : HomotopyCategory₂ X ≌ X.HomotopyCategory where
  functor := toHomotopyCategory X
  inverse := HomotopyCategory.toHomotopyCategory₂ X
  unitIso := eqToIso (toHomotopyCategory_comp_toHomotopyCategory₂ X).symm
  counitIso := eqToIso (HomotopyCategory.toHomotopyCategory₂_comp_toHomotopyCategory X)
  functor_unitIso_comp _ := by simp [eqToHom_map]

/-- The forward functor of the comparison equivalence is the canonical edge-class map. -/
@[simp]
lemma equivalence_functor : (equivalence X).functor = toHomotopyCategory X :=
  (rfl)

/-- The inverse functor of the comparison equivalence sends edges to their homotopy classes. -/
@[simp]
lemma equivalence_inverse : (equivalence X).inverse = HomotopyCategory.toHomotopyCategory₂ X :=
  (rfl)

instance : (toHomotopyCategory X).IsEquivalence :=
  (equivalence X).isEquivalence_functor

end HomotopyCategory₂

end SSet.Truncated

namespace SSet.Edge

variable {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}

/-- An edge of a quasicategory is an equivalence exactly when its class in the
generators-and-relations homotopy category is an isomorphism. -/
lemma isEquivalence_iff_isIso_homotopyCategoryHomMk (e : X.Edge x y) :
    e.IsEquivalence ↔ IsIso (HomotopyCategory.homMk e) := by
  rw [isEquivalence_iff_isIso,
    ← isIso_iff_of_reflects_iso _ (Truncated.HomotopyCategory₂.toHomotopyCategory _),
    Truncated.HomotopyCategory₂.toHomotopyCategory_map_homMk]
  simp [HomotopyCategory.homMk]

end SSet.Edge

namespace SSet.HomotopyCategory

variable {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}

/-- The comparison functor sends the class of an edge to the class of the same edge. -/
private lemma toHomotopyCategory_map_homMk_toTruncated (e : X.Edge x y) :
    (Truncated.HomotopyCategory₂.toHomotopyCategory ((truncation 2).obj X)).map
        (Truncated.HomotopyCategory₂.homMk e.toTruncated) =
      homMk e := by
  rw [Truncated.HomotopyCategory₂.toHomotopyCategory_map_homMk]
  -- The two `eqToHom` factors are identities, since the comparison fixes vertices by definition.
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- In a quasicategory, every morphism of the homotopy category between two vertices is the class
of an edge. -/
lemma homMk_surjective : Function.Surjective (homMk : X.Edge x y → (mk x ⟶ mk y)) := by
  intro φ
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (⟨x⟩ : Truncated.HomotopyCategory₂ ((truncation 2).obj X)) ⟶ ⟨y⟩,
      (Truncated.HomotopyCategory₂.toHomotopyCategory _).map ψ = φ :=
    (Truncated.HomotopyCategory₂.toHomotopyCategory _).map_surjective φ
  obtain ⟨e, rfl⟩ := Truncated.HomotopyCategory₂.homMk_surjective ψ
  exact ⟨Edge.ofTruncated e, (toHomotopyCategory_map_homMk_toTruncated _).symm.trans hψ⟩

/-- In a quasicategory, two edges with the same endpoints have the same class in the homotopy
category exactly when a `2`-simplex exhibits the second as a composite of the identity and the
first. -/
lemma homMk_eq_homMk_iff (e e' : X.Edge x y) :
    homMk e = homMk e' ↔ Nonempty (Edge.CompStruct (.id x) e e') := by
  refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ ?_⟩
  · obtain ⟨h⟩ := Truncated.HomotopyCategory₂.homMk_eq_iff_homotopicR.1
      ((Truncated.HomotopyCategory₂.toHomotopyCategory ((truncation 2).obj X)).map_injective
        ((toHomotopyCategory_map_homMk_toTruncated e).trans
          (h.trans (toHomotopyCategory_map_homMk_toTruncated e').symm)))
    exact ⟨.ofTruncated h⟩
  · exact (toHomotopyCategory_map_homMk_toTruncated e).symm.trans
      ((congrArg (Truncated.HomotopyCategory₂.toHomotopyCategory ((truncation 2).obj X)).map
        (Truncated.HomotopyCategory₂.homMk_eq_iff_homotopicR.2 ⟨h.toTruncated⟩)).trans
        (toHomotopyCategory_map_homMk_toTruncated e'))

/-- In a quasicategory, two vertices are isomorphic in the homotopy category exactly when an
equivalence joins them. -/
lemma nonempty_iso_mk_iff : Nonempty (mk x ≅ mk y) ↔ ∃ e : X.Edge x y, e.IsEquivalence := by
  refine ⟨fun ⟨i⟩ ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · obtain ⟨e, he⟩ := homMk_surjective i.hom
    exact ⟨e, (Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk e).2 (he ▸ inferInstance)⟩
  · have := (Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk e).1 he
    exact ⟨asIso (homMk e)⟩

end SSet.HomotopyCategory

namespace SSet

/-- A map `f : X ⟶ Y` to a quasicategory is essentially surjective on homotopy categories exactly
when every vertex of `Y` is joined by an equivalence to a vertex in the image of `f`. -/
lemma essSurj_mapHomotopyCategory_iff {X Y : SSet.{u}} [Quasicategory Y] (f : X ⟶ Y) :
    (mapHomotopyCategory f).EssSurj ↔
      ∀ y : Y _⦋0⦌, ∃ (x : X _⦋0⦌) (e : Edge (f.app _ x) y), e.IsEquivalence := by
  refine ⟨fun _ y ↦ ?_, fun h ↦ ⟨fun b ↦ ?_⟩⟩
  · obtain ⟨a, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (mapHomotopyCategory f) (HomotopyCategory.mk y)
    induction a with | mk x => ?_
    exact ⟨x, HomotopyCategory.nonempty_iso_mk_iff.1 ⟨i⟩⟩
  · induction b with | mk y => ?_
    obtain ⟨x, e, he⟩ := h y
    exact ⟨HomotopyCategory.mk x, HomotopyCategory.nonempty_iso_mk_iff.2 ⟨e, he⟩⟩

end SSet
