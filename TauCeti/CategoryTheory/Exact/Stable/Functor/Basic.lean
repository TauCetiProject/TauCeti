/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# Functors between projective stable categories

An additive functor between exact categories is **stable conflation-exact** when it preserves
conflations and projective-injective objects. Between Frobenius exact categories, such a functor
carries every morphism factoring through a projective to one factoring through a projective.
It therefore descends to an additive functor between the projective stable categories.

The construction is functorial: natural transformations and natural isomorphisms descend,
identity and composition are preserved, and an equivalence whose two directions are stable
conflation-exact induces an equivalence of stable categories.

## Main definitions

* `TauCeti.StableConflationExact`: a conflation-exact additive functor preserving
  projective-injective objects.
* `TauCeti.StableConflationExact.stableFunctor`: its induced functor between projective stable
  categories.
* `TauCeti.StableConflationExact.stableNatTrans` and `.stableNatIso`: descent of natural
  transformations and natural isomorphisms.
* `TauCeti.StableConflationExact.stableEquivalence`: the stable equivalence induced by an
  equivalence that is stable conflation-exact in both directions.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

/-- A conflation-exact functor is **stable conflation-exact** when it also sends
projective-injective objects to projective-injective objects. -/
structure StableConflationExact {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
    (E : ExactStructure C) (E' : ExactStructure D) (F : Functor C D) [F.Additive] : Prop where
  /-- The underlying functor preserves conflations. -/
  isConflationExact : E.IsConflationExact E' F
  /-- The underlying functor preserves projective-injective objects. -/
  map_projectiveInjective : ∀ {X : C}, E.projectiveInjective X →
    E'.projectiveInjective (F.obj X)

namespace StableConflationExact

variable {C : Type u₁} {D : Type u₂} {K : Type u₃}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
variable [Category.{v₃} K] [Preadditive K] [HasZeroObject K] [HasBinaryBiproducts K]
variable {E : ExactStructure C} {E' : ExactStructure D} {E'' : ExactStructure K}

/-- The identity functor is stable conflation-exact. -/
protected theorem id (E : ExactStructure C) : StableConflationExact E E (𝟭 C) where
  isConflationExact := ExactStructure.IsConflationExact.id
  map_projectiveInjective hX := hX

/-- A composite of stable conflation-exact functors is stable conflation-exact. -/
protected theorem comp {F : Functor C D} {G : Functor D K} [F.Additive] [G.Additive]
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E' E'' G) :
    StableConflationExact E E'' (F ⋙ G) where
  isConflationExact := hF.isConflationExact.comp hG.isConflationExact
  map_projectiveInjective hX := hG.map_projectiveInjective (hF.map_projectiveInjective hX)

/-- Stable conflation-exactness is preserved by replacing a functor by a naturally isomorphic
additive functor. -/
theorem of_iso {F G : Functor C D} [F.Additive] [G.Additive]
    (hF : StableConflationExact E E' F) (e : F ≅ G) : StableConflationExact E E' G where
  isConflationExact := hF.isConflationExact.of_iso e
  map_projectiveInjective {X} hX :=
    E'.projectiveInjective.prop_of_iso (e.app X) (hF.map_projectiveInjective hX)

/-- Naturally isomorphic additive functors are stable conflation-exact together. -/
theorem iff_of_iso {F G : Functor C D} [F.Additive] [G.Additive] (e : F ≅ G) :
    StableConflationExact E E' F ↔ StableConflationExact E E' G :=
  ⟨fun hF ↦ hF.of_iso e, fun hG ↦ hG.of_iso e.symm⟩

/-- Between Frobenius exact categories, a stable conflation-exact functor carries the projective
stable ideal of the source into the projective stable ideal of the target. -/
theorem projectiveStableIdeal_le_comap {F : Functor C D} [F.Additive]
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) :
    E.projectiveStableIdeal ≤ E'.projectiveStableIdeal.comap F := by
  rw [hE.projectiveStableIdeal_eq_factorIdeal]
  apply ObjectProperty.factorIdeal_le_iff.2
  intro X Y Z hZ i p
  rw [MorphismIdeal.mem_comap_hom, ExactStructure.mem_projectiveStableIdeal_iff, F.map_comp]
  exact ObjectProperty.factorsThrough_comp E'.isProjective
    ((E'.projectiveInjective_iff _).1 (hF.map_projectiveInjective hZ)).1 _ _

/-- A stable conflation-exact functor between Frobenius exact categories descends to their
projective stable categories. -/
noncomputable def stableFunctor {F : Functor C D} [F.Additive]
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) :
    Functor E.ProjectiveStableCategory E'.ProjectiveStableCategory :=
  E.projectiveStableIdeal.map E'.projectiveStableIdeal F
    (hF.projectiveStableIdeal_le_comap hE)

/-- The stable functor applies the original functor on objects from the exact category. -/
@[simp]
theorem stableFunctor_obj_projectiveStableFunctor_obj {F : Functor C D} [F.Additive]
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) (X : C) :
    (hF.stableFunctor hE).obj (E.projectiveStableFunctor.obj X) =
      E'.projectiveStableFunctor.obj (F.obj X) :=
  MorphismIdeal.map_obj_quotientFunctor_obj _ _ _ _ _

/-- The stable functor applies the original functor to representatives of stable morphisms. -/
@[simp]
theorem stableFunctor_map_projectiveStableFunctor_map {F : Functor C D} [F.Additive]
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) {X Y : C} (f : X ⟶ Y) :
    (hF.stableFunctor hE).map (E.projectiveStableFunctor.map f) ≫
        eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE Y) =
      eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X) ≫
        E'.projectiveStableFunctor.map (F.map f) :=
  MorphismIdeal.map_map_quotientFunctor_map _ _ _ _ _

/-- Descent sends the identity stable conflation-exact functor to the identity functor. -/
@[simp]
theorem stableFunctor_id (hE : E.IsFrobenius) :
    (StableConflationExact.id E).stableFunctor hE = 𝟭 E.ProjectiveStableCategory := by
  apply MorphismIdeal.map_id

/-- Descent carries a composite of stable conflation-exact functors to the composite of their
stable functors. -/
theorem stableFunctor_comp {F : Functor C D} {G : Functor D K} [F.Additive] [G.Additive]
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E' E'' G)
    (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) :
    (hF.comp hG).stableFunctor hE = hF.stableFunctor hE ⋙ hG.stableFunctor hE' := by
  apply MorphismIdeal.map_comp

/-- A natural transformation between stable conflation-exact functors descends to a natural
transformation between their stable functors. -/
noncomputable def stableNatTrans {F G : Functor C D} [F.Additive] [G.Additive]
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E E' G)
    (hE : E.IsFrobenius) (α : F ⟶ G) : hF.stableFunctor hE ⟶ hG.stableFunctor hE :=
  E.projectiveStableIdeal.mapNatTrans E'.projectiveStableIdeal
    (hF.projectiveStableIdeal_le_comap hE) (hG.projectiveStableIdeal_le_comap hE) α

/-- On objects from the exact category, a descended natural transformation is represented by
the corresponding component of the original transformation. -/
@[simp]
theorem stableNatTrans_app_projectiveStableFunctor_obj {F G : Functor C D}
    [F.Additive] [G.Additive] (hF : StableConflationExact E E' F)
    (hG : StableConflationExact E E' G) (hE : E.IsFrobenius) (α : F ⟶ G) (X : C) :
    eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X).symm ≫
        (stableNatTrans hF hG hE α).app (E.projectiveStableFunctor.obj X) ≫
          eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE X) =
      E'.projectiveStableFunctor.map (α.app X) :=
  MorphismIdeal.mapNatTrans_app_quotientFunctor_obj _ _ _ _ _ _

/-- Descent sends the identity natural transformation to the identity. -/
@[simp]
theorem stableNatTrans_id {F : Functor C D} [F.Additive]
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) :
    stableNatTrans hF hF hE (𝟙 F) = 𝟙 (hF.stableFunctor hE) :=
  MorphismIdeal.mapNatTrans_id _ _ _ _

/-- Descent preserves vertical composition of natural transformations. -/
@[simp]
theorem stableNatTrans_comp {F G H : Functor C D} [F.Additive] [G.Additive] [H.Additive]
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E E' G)
    (hH : StableConflationExact E E' H) (hE : E.IsFrobenius)
    (α : F ⟶ G) (β : G ⟶ H) :
    stableNatTrans hF hG hE α ≫ stableNatTrans hG hH hE β =
      stableNatTrans hF hH hE (α ≫ β) :=
  MorphismIdeal.comp_mapNatTrans _ _ _ _ _ _ _

/-- A natural isomorphism between stable conflation-exact functors descends to a natural
isomorphism between their stable functors. -/
noncomputable def stableNatIso {F G : Functor C D} [F.Additive] [G.Additive]
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E E' G)
    (hE : E.IsFrobenius) (α : F ≅ G) : hF.stableFunctor hE ≅ hG.stableFunctor hE :=
  E.projectiveStableIdeal.mapNatIso E'.projectiveStableIdeal
    (hF.projectiveStableIdeal_le_comap hE) (hG.projectiveStableIdeal_le_comap hE) α

/-- The forward component of a descended natural isomorphism is the descended transformation. -/
@[simp]
theorem stableNatIso_hom {F G : Functor C D} [F.Additive] [G.Additive]
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E E' G)
    (hE : E.IsFrobenius) (α : F ≅ G) :
    (stableNatIso hF hG hE α).hom = stableNatTrans hF hG hE α.hom :=
  MorphismIdeal.mapNatIso_hom _ _ _ _ _

/-- The inverse component of a descended natural isomorphism is the descended inverse. -/
@[simp]
theorem stableNatIso_inv {F G : Functor C D} [F.Additive] [G.Additive]
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E E' G)
    (hE : E.IsFrobenius) (α : F ≅ G) :
    (stableNatIso hF hG hE α).inv = stableNatTrans hG hF hE α.inv :=
  MorphismIdeal.mapNatIso_inv _ _ _ _ _

/-- An equivalence which is stable conflation-exact in both directions induces an equivalence of
projective stable categories. -/
noncomputable def stableEquivalence (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (hF : StableConflationExact E E' e.functor)
    (hG : StableConflationExact E' E e.inverse)
    (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) :
    E.ProjectiveStableCategory ≌ E'.ProjectiveStableCategory :=
  E.projectiveStableIdeal.mapEquivalence e E'.projectiveStableIdeal <| le_antisymm
    (hF.projectiveStableIdeal_le_comap hE) <| by
      simpa only [MorphismIdeal.comap_functor_comap_inverse] using
        MorphismIdeal.comap_mono e.functor (hG.projectiveStableIdeal_le_comap hE')

/-- The functor of the induced stable equivalence is the descended forward functor. -/
@[simp]
theorem stableEquivalence_functor (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (hF : StableConflationExact E E' e.functor)
    (hG : StableConflationExact E' E e.inverse)
    (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) :
    (stableEquivalence e hF hG hE hE').functor = hF.stableFunctor hE :=
  MorphismIdeal.mapEquivalence_functor _ _ _ _

/-- The inverse of the induced stable equivalence is the descended inverse functor. -/
@[simp]
theorem stableEquivalence_inverse (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (hF : StableConflationExact E E' e.functor)
    (hG : StableConflationExact E' E e.inverse)
    (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) :
    (stableEquivalence e hF hG hE hE').inverse = hG.stableFunctor hE' :=
  MorphismIdeal.mapEquivalence_inverse _ _ _ _

end StableConflationExact

end TauCeti
