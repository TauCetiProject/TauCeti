/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Basic
import TauCeti.Algebra.Category.ModuleCat.Equivalence
import TauCeti.CategoryTheory.Adjunction.Additive

/-!
# Equivalences of categories of finitely generated projective modules

An equivalence of categories `e : ModuleCat A ≌ ModuleCat B` between module categories preserves
and reflects finite generation and projectivity, so it restricts to an additive equivalence
`CategoryTheory.Equivalence.finiteProjectiveModulesEquivalence` between the full subcategories of
finitely generated projective modules.
-/

public section

namespace CategoryTheory.Equivalence

open CategoryTheory.ObjectProperty TauCeti

universe u u'

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B)

/-- An equivalence of module categories pulls the finitely generated projective `B`-modules back
to the finitely generated projective `A`-modules. -/
@[simp]
theorem finiteProjectiveModules_inverseImage :
    (finiteProjectiveModules B).inverseImage e.functor = finiteProjectiveModules A := by
  funext M
  rw [prop_inverseImage_iff, finiteProjectiveModules_iff, finiteProjectiveModules_iff,
    e.finite_functor_obj_iff, e.projective_functor_obj_iff]

/-- **Finitely generated projective modules along an equivalence of module categories.** An
equivalence `e : ModuleCat A ≌ ModuleCat B` restricts to an equivalence from the finitely
generated projective `A`-modules to the finitely generated projective `B`-modules. -/
noncomputable def finiteProjectiveModulesEquivalence :
    (finiteProjectiveModules A).FullSubcategory ≌ (finiteProjectiveModules B).FullSubcategory :=
  e.congrFullSubcategory e.finiteProjectiveModules_inverseImage

instance : e.finiteProjectiveModulesEquivalence.functor.Additive := by
  unfold finiteProjectiveModulesEquivalence
  infer_instance

@[simp]
theorem finiteProjectiveModulesEquivalence_functor_obj_obj
    (M : (finiteProjectiveModules A).FullSubcategory) :
    (e.finiteProjectiveModulesEquivalence.functor.obj M).obj = e.functor.obj M.obj :=
  e.congrFullSubcategory_functor_obj_obj _ M

@[simp]
theorem finiteProjectiveModulesEquivalence_functor_map_hom
    {M N : (finiteProjectiveModules A).FullSubcategory} (f : M ⟶ N) :
    (e.finiteProjectiveModulesEquivalence.functor.map f).hom =
      eqToHom (e.finiteProjectiveModulesEquivalence_functor_obj_obj M) ≫ e.functor.map f.hom ≫
        eqToHom (e.finiteProjectiveModulesEquivalence_functor_obj_obj N).symm :=
  e.congrFullSubcategory_functor_map_hom _ f

@[simp]
theorem finiteProjectiveModulesEquivalence_inverse_obj_obj
    (M : (finiteProjectiveModules B).FullSubcategory) :
    (e.finiteProjectiveModulesEquivalence.inverse.obj M).obj = e.inverse.obj M.obj :=
  e.congrFullSubcategory_inverse_obj_obj _ M

@[simp]
theorem finiteProjectiveModulesEquivalence_inverse_map_hom
    {M N : (finiteProjectiveModules B).FullSubcategory} (f : M ⟶ N) :
    (e.finiteProjectiveModulesEquivalence.inverse.map f).hom =
      eqToHom (e.finiteProjectiveModulesEquivalence_inverse_obj_obj M) ≫ e.inverse.map f.hom ≫
        eqToHom (e.finiteProjectiveModulesEquivalence_inverse_obj_obj N).symm :=
  e.congrFullSubcategory_inverse_map_hom _ f

end CategoryTheory.Equivalence
