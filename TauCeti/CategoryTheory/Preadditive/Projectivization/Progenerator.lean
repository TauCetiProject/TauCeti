/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Progenerator
public import TauCeti.CategoryTheory.Preadditive.Projectivization.Basic

/-!
# Projectivization of projective objects via a progenerator

For a progenerator `P` in an idempotent-complete preadditive category `C` with finite biproducts,
`proj C = add P` (`TauCeti.IsProgenerator.isProjective_le_additiveClosure` and
`TauCeti.IsProgenerator.additiveClosure_le_isProjective`), so `Hom(P, -)` restricts to an
equivalence `TauCeti.IsProgenerator.projectiveEquivalence` between `proj C` and the finitely
generated projective right `End P`-modules.

## Main definitions

* `TauCeti.IsProgenerator.projectiveEquivalence`: for a progenerator `P` in an
  idempotent-complete category, `Hom(P, -)` restricts to an equivalence between `proj C` and the
  finitely generated projective `(End P)ᵐᵒᵖ`-modules, with comparison isomorphism
  `TauCeti.IsProgenerator.projectiveEquivalenceCompιIso`.
-/

public section

namespace TauCeti.IsProgenerator

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

variable {P : C}

/-- **Projectivization of `proj C`.** For a progenerator `P` of an idempotent-complete preadditive
category `C` with finite biproducts, `Hom(P, -)` induces an equivalence between `proj C`
(`(isProjective C).FullSubcategory`) and the finitely generated projective right
`End P`-modules. -/
noncomputable def projectiveEquivalence (hP : IsProgenerator P) [IsIdempotentComplete C] :
    (isProjective C).FullSubcategory ≌ (finiteProjectiveModules (End P)ᵐᵒᵖ).FullSubcategory :=
  have : (ObjectProperty.ιOfLE hP.isProjective_le_additiveClosure).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff _).mpr
      (hP.additiveClosure_le_isProjective.trans (isProjective C).le_isoClosure)
  (ObjectProperty.ιOfLE hP.isProjective_le_additiveClosure).asEquivalence.trans
    (projectivizationFunctor P).asEquivalence

/-- `hP.projectiveEquivalence.functor` followed by the inclusion into `ModuleCat (End P)ᵐᵒᵖ` is
naturally isomorphic to `Hom(P, -)` on projective objects. -/
noncomputable def projectiveEquivalenceCompιIso (hP : IsProgenerator P)
    [IsIdempotentComplete C] :
    hP.projectiveEquivalence.functor ⋙ (finiteProjectiveModules (End P)ᵐᵒᵖ).ι ≅
      (isProjective C).ι ⋙ preadditiveCoyonedaObj P :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance additive_projectiveEquivalence_functor (hP : IsProgenerator P) [IsIdempotentComplete C] :
    hP.projectiveEquivalence.functor.Additive :=
  have : (hP.projectiveEquivalence.functor ⋙ (finiteProjectiveModules (End P)ᵐᵒᵖ).ι).Additive :=
    Functor.additive_of_iso hP.projectiveEquivalenceCompιIso.symm
  Functor.additive_of_comp_faithful _ (finiteProjectiveModules (End P)ᵐᵒᵖ).ι

/-- The underlying module of `hP.projectiveEquivalence.functor.obj X` is
`(preadditiveCoyonedaObj P).obj X.obj`. -/
@[simp]
theorem projectiveEquivalence_functor_obj_obj (hP : IsProgenerator P) [IsIdempotentComplete C]
    (X : (isProjective C).FullSubcategory) :
    (hP.projectiveEquivalence.functor.obj X).obj = (preadditiveCoyonedaObj P).obj X.obj :=
  (rfl)

@[simp]
theorem projectiveEquivalenceCompιIso_hom_app (hP : IsProgenerator P) [IsIdempotentComplete C]
    (X : (isProjective C).FullSubcategory) :
    hP.projectiveEquivalenceCompιIso.hom.app X =
      eqToHom (hP.projectiveEquivalence_functor_obj_obj X) :=
  (rfl)

@[simp]
theorem projectiveEquivalenceCompιIso_inv_app (hP : IsProgenerator P) [IsIdempotentComplete C]
    (X : (isProjective C).FullSubcategory) :
    hP.projectiveEquivalenceCompιIso.inv.app X =
      eqToHom (hP.projectiveEquivalence_functor_obj_obj X).symm :=
  (rfl)

/-- The action of `hP.projectiveEquivalence.functor` on morphisms agrees with `Hom(P, -)` modulo the
comparison isomorphism `hP.projectiveEquivalenceCompιIso`. -/
@[simp]
theorem projectiveEquivalence_functor_map_hom (hP : IsProgenerator P) [IsIdempotentComplete C]
    {X Y : (isProjective C).FullSubcategory} (f : X ⟶ Y) :
    (hP.projectiveEquivalence.functor.map f).hom =
      hP.projectiveEquivalenceCompιIso.hom.app X ≫
        (preadditiveCoyonedaObj P).map f.hom ≫
        hP.projectiveEquivalenceCompιIso.inv.app Y :=
  (NatIso.naturality_2 hP.projectiveEquivalenceCompιIso f).symm

end TauCeti.IsProgenerator
