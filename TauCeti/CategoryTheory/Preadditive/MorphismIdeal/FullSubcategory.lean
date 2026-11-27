/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Linear

/-!
# Equivalences with full subcategories of ideal quotients

A full additive functor induces an equivalence from the quotient by the pulled-back ideal
onto any full subcategory of the target quotient that it lands in and hits up to isomorphism.
This identifies, for example, the stable quotient of a category of finite modules with the
subcategory of finite objects in the ambient stable quotient.
-/

public section

open CategoryTheory

namespace TauCeti.MorphismIdeal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D) [F.Additive]
  (h : I = J.comap F) (P : ObjectProperty J.Quotient)
  (hP : ∀ X, P (J.quotientFunctor.obj (F.obj X)))

private noncomputable def mapToFullSubcategory : I.Quotient ⥤ P.FullSubcategory :=
  P.lift (I.map J F h.le) fun X ↦ by
    rw [← I.quotientFunctor_obj_as X, map_obj_quotientFunctor_obj]
    exact hP X.as

variable [F.Full]
  (hSurj : ∀ Y : P.FullSubcategory,
    ∃ X, Nonempty (J.quotientFunctor.obj (F.obj X) ≅ Y.obj))

/-- A full additive functor induces an equivalence from the quotient by the pulled-back ideal
onto a full subcategory of the target quotient it lands in and hits up to isomorphism. -/
noncomputable def mapFullSubcategoryEquivalence : I.Quotient ≌ P.FullSubcategory := by
  have : (I.map J F h.le).Faithful := (faithful_map_iff I J F h.le).2 h.ge
  let G := mapToFullSubcategory I J F h P hP
  have : G.Full := by dsimp [G, mapToFullSubcategory]; infer_instance
  have : G.Faithful := by dsimp [G, mapToFullSubcategory]; infer_instance
  have : G.EssSurj := ⟨fun Y ↦ by
    obtain ⟨X, ⟨e⟩⟩ := hSurj Y
    refine ⟨I.quotientFunctor.obj X, ⟨P.fullyFaithfulι.preimageIso ?_⟩⟩
    exact eqToIso (map_obj_quotientFunctor_obj I J F h.le X) ≪≫ e⟩
  letI : G.IsEquivalence := {}
  exact G.asEquivalence

/-- The comparison equivalence commutes with the quotient functors and the full inclusion. -/
noncomputable def quotientFunctorCompMapFullSubcategoryEquivalenceIso :
    I.quotientFunctor ⋙ (mapFullSubcategoryEquivalence I J F h P hP hSurj).functor ⋙ P.ι ≅
      F ⋙ J.quotientFunctor := by
  rw [mapFullSubcategoryEquivalence, Functor.asEquivalence_functor, mapToFullSubcategory]
  exact Functor.isoWhiskerLeft I.quotientFunctor (P.liftCompιIso _ _) ≪≫
    eqToIso (I.quotientFunctor_comp_map J F h.le)

instance : (mapFullSubcategoryEquivalence I J F h P hP hSurj).functor.Additive := by
  rw [mapFullSubcategoryEquivalence, Functor.asEquivalence_functor, mapToFullSubcategory]
  infer_instance

variable (R : Type*) [Semiring R] [Linear R C] [Linear R D] [F.Linear R]

instance : (mapFullSubcategoryEquivalence I J F h P hP hSurj).functor.Linear R := by
  rw [mapFullSubcategoryEquivalence, Functor.asEquivalence_functor, mapToFullSubcategory]
  exact ⟨fun f r ↦ ObjectProperty.hom_ext _ ((I.map J F h.le).map_smul r f)⟩

end TauCeti.MorphismIdeal
