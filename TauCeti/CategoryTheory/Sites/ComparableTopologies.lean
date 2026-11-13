/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Sheaves for comparable topologies

Let `J ≤ K` be Grothendieck topologies on a category `C`, so that `K` is finer than `J`. Every
`K`-sheaf is a `J`-sheaf, which gives the fully faithful inclusion
`TauCeti.CategoryTheory.sheafInclusionOfLE h A : Sheaf K A ⥤ Sheaf J A`. When
`K`-sheafification exists, its left adjoint is `K`-sheafification of the underlying presheaf,
`sheafToPresheaf J A ⋙ presheafToSheaf K A`
(`TauCeti.CategoryTheory.sheafifyAdjunctionOfLE`), so the inclusion is reflective. For
`A = Type _`, this is the morphism of topoi `Sh(C, K) → Sh(C, J)` induced by the identity of `C`:
the inclusion is its direct image and sheafification its inverse image. More generally, the
inverse image preserves finite limits when `A` has finite limits and `K`-sheafification preserves
them (`[HasFiniteLimits A] [HasSheafify K A]`).
The counit of the adjunction is an isomorphism because the inclusion is fully faithful
(Mathlib's `CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful`).

For instance, the small Nisnevich topology of a scheme is coarser than its small étale topology,
and this gives the comparison morphism of topoi from étale sheaves to Nisnevich sheaves.

## Main declarations

* `TauCeti.CategoryTheory.sheafInclusionOfLE`: `K`-sheaves as `J`-sheaves.
* `TauCeti.CategoryTheory.sheafifyAdjunctionOfLE`: `K`-sheafification of `J`-sheaves
  is left adjoint to `sheafInclusionOfLE`.

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §4, for morphisms of topoi.
-/

public section

universe v u v' u'

open CategoryTheory Limits GrothendieckTopology

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : J ≤ K)
  (A : Type u') [Category.{v'} A]

/-- For topologies `J ≤ K`, every `K`-sheaf is a `J`-sheaf: the direct image of the morphism of
topoi `Sh(C, K) → Sh(C, J)` induced by the identity of `C`. -/
abbrev sheafInclusionOfLE : Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.ιOfLE fun _ hF ↦ hF.of_le h

/-- The inclusion of `K`-sheaves into `J`-sheaves does not change underlying presheaves. -/
def sheafInclusionOfLECompSheafToPresheafIso :
    sheafInclusionOfLE h A ⋙ sheafToPresheaf J A ≅ sheafToPresheaf K A :=
  Iso.refl _

@[simp]
theorem sheafInclusionOfLECompSheafToPresheafIso_hom_app (F : Sheaf K A) :
    (sheafInclusionOfLECompSheafToPresheafIso h A).hom.app F = 𝟙 F.obj :=
  (rfl)

@[simp]
theorem sheafInclusionOfLECompSheafToPresheafIso_inv_app (F : Sheaf K A) :
    (sheafInclusionOfLECompSheafToPresheafIso h A).inv.app F = 𝟙 F.obj :=
  (rfl)

variable [HasWeakSheafify K A]

/-- For topologies `J ≤ K`, `K`-sheafification of the presheaf underlying a `J`-sheaf is left
adjoint to the inclusion of `K`-sheaves into `J`-sheaves. It is the restriction of the
sheafification adjunction for `K` to `J`-sheaves. For `A = Type _`, this is the morphism of topoi
`Sh(C, K) → Sh(C, J)` induced by the identity of `C`, with inverse image
`sheafToPresheaf J A ⋙ presheafToSheaf K A`. -/
noncomputable def sheafifyAdjunctionOfLE :
    sheafToPresheaf J A ⋙ presheafToSheaf K A ⊣ sheafInclusionOfLE h A :=
  (sheafificationAdjunction K A).restrictFullyFaithful (fullyFaithfulSheafToPresheaf J A)
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

@[simp]
theorem sheafifyAdjunctionOfLE_unit_app_hom (F : Sheaf J A) :
    ((sheafifyAdjunctionOfLE h A).unit.app F).hom = toSheafify K F.obj := by
  have := (sheafificationAdjunction K A).map_restrictFullyFaithful_unit_app
    (L := sheafToPresheaf J A ⋙ presheafToSheaf K A) (R := sheafInclusionOfLE h A)
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F
  simp only [Functor.id_obj, ObjectProperty.ι_obj, Functor.comp_obj, ObjectProperty.ιOfLE_obj_obj,
    ObjectProperty.ι_map, sheafificationAdjunction_unit_app, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, Category.comp_id] at this
  exact this

@[simp]
theorem sheafifyAdjunctionOfLE_counit_app_hom (G : Sheaf K A) :
    ((sheafifyAdjunctionOfLE h A).counit.app G).hom = sheafifyLift K (𝟙 G.obj) G.property := by
  have := (sheafificationAdjunction K A).map_restrictFullyFaithful_counit_app
    (L := sheafToPresheaf J A ⋙ presheafToSheaf K A) (R := sheafInclusionOfLE h A)
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) G
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.ιOfLE_obj_obj, Functor.id_obj,
    Functor.id_map, Iso.refl_inv, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp] at this
  rw [sheafifyAdjunctionOfLE, ← sheafificationAdjunction_counit_app_val, ← this]

noncomputable instance : Reflective (sheafInclusionOfLE h A) where
  L := sheafToPresheaf J A ⋙ presheafToSheaf K A
  adj := sheafifyAdjunctionOfLE h A

end TauCeti.CategoryTheory
