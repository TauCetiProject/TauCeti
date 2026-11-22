/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.RestrictedYoneda

/-!
# Finitely presented modules as finitely presented functors

Because a module is finitely presented exactly when it is the cokernel of a morphism between
finitely generated projective modules (`TauCeti.presented_finiteProjectiveModules`), the Yoneda
description of finitely presented functors on a category of projective objects identifies the
finitely presented `R`-modules with `mod (proj R)`, the finitely presented functors on the category
of finitely generated projective `R`-modules. Evaluating the functor attached to a module at the
regular module `R` recovers the underlying abelian group of the module.

## Main definitions

* `TauCeti.finitePresentationEquivalenceMod`: the equivalence between the finitely presented
  `R`-modules and `mod (proj R)`.
* `TauCeti.finitePresentationEquivalenceModCompιIso`: the forward functor is `M ↦ (-, M)|_{proj R}`.
* `TauCeti.finitePresentationEquivalenceModCompEvaluationIso`: the composite of this equivalence
  with evaluation at `R` is the underlying abelian group of a module.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer (1966), 189–231.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace TauCeti

variable (R : Type u) [Ring R]

/-- **The finitely presented modules are `mod (proj R)`.** The functor `M ↦ (-, M)|_{proj R}` is an
equivalence from the finitely presented `R`-modules to the finitely presented functors on the
finitely generated projective `R`-modules. -/
noncomputable def finitePresentationEquivalenceMod :
    (finitePresentationModules R).FullSubcategory ≌
      (isFinitelyPresentedFunctor (finiteProjectiveModules R).FullSubcategory).FullSubcategory :=
  ObjectProperty.equivalenceMod (finiteProjectiveModules_le_categoryTheory_isProjective R)
    (presented_finiteProjectiveModules R).symm

/-- The functor of `finitePresentationEquivalenceMod` is `M ↦ (-, M)|_{proj R}`. -/
noncomputable def finitePresentationEquivalenceModCompιIso :
    (finitePresentationEquivalenceMod R).functor ⋙ (isFinitelyPresentedFunctor _).ι ≅
      (finitePresentationModules R).ι ⋙ (finiteProjectiveModules R).restrictedPreadditiveYoneda :=
  ObjectProperty.equivalenceModCompιIso _ _

/-- The functor attached to a finitely presented `R`-module `M` takes the value `(R, M)` at the
regular module, and `(R, M)` is the underlying abelian group of `M`, naturally in `M`. -/
noncomputable def finitePresentationEquivalenceModCompEvaluationIso :
    ((finitePresentationEquivalenceMod R).functor ⋙ (isFinitelyPresentedFunctor _).ι) ⋙
        (evaluation _ _).obj (op (finiteProjectiveModulesRegular R)) ≅
      (finitePresentationModules R).ι ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  let eR : (finiteProjectiveModulesRegular R).obj ≅ ModuleCat.of R R :=
    eqToIso (finiteProjectiveModulesRegular_obj R)
  Functor.isoWhiskerRight (finitePresentationEquivalenceModCompιIso R) _ ≪≫
    NatIso.ofComponents (fun M ↦
      (({ toFun := fun g ↦ eR.inv ≫ g
          invFun := fun g ↦ eR.hom ≫ g
          left_inv := fun g ↦ by simp
          right_inv := fun g ↦ by simp
          map_add' := fun _ _ ↦ by simp } :
          ((finiteProjectiveModulesRegular R).obj ⟶ M.obj) ≃+
            (ModuleCat.of R R ⟶ M.obj)).trans
        (ModuleCat.homAddEquiv.trans
          (LinearMap.ringLmapEquivSelf R ℕ M.obj).toAddEquiv)).toAddCommGrpIso) fun {M N} f ↦ by
      ext (g : (finiteProjectiveModulesRegular R).obj ⟶ M.obj)
      rfl

end TauCeti
