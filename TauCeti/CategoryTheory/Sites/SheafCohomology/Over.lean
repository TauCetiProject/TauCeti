/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import TauCeti.CategoryTheory.Sites.ExtensionByZero
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal

/-!
# Cohomology on a lower interval

On a preorder site, cohomology at an object agrees with cohomology of the sheaf restricted to
its lower interval. For the site of open subsets of a space, this is the comparison between
cohomology on an open subset and cohomology of the restricted sheaf.

The comparison uses the exact extension-by-zero adjunction, its action on free abelian
representable sheaves, and Mathlib's comparison of Ext groups along exact adjunctions.

## Main declarations

* `TauCeti.CategoryTheory.sheafPullbackFreeYonedaIso`: the action of extension on the source
  objects defining cohomology on an open.
* `TauCeti.CategoryTheory.cohomologyPresheafEvaluationIsoFunctorOverH`: the comparison,
  natural in the coefficient sheaf.
* `TauCeti.CategoryTheory.cohomologyPresheafObjIsoOverH`: `Hⁿ(U, F) ≅ Hⁿ(F.over U)`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, "Coherent sheaves and
cohomology": it supplies the restriction comparison needed to turn affine acyclicity into
vanishing hypotheses for `Scheme.Modules.subsingleton_cohomology_of_two_le`. No formalization
is vendored.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.CategoryTheory

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]

private def sectionsCorepresentation (V : C) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op V) ⋙ forget AddCommGrpCat).CorepresentableBy
      ((freeYonedaSheafFunctor J).obj V) where
  homEquiv := (freeYonedaSheafSectionsEquiv J V _).toEquiv
  homEquiv_comp g f := freeYonedaSheafSectionsEquiv_naturality_right J f g

private def extendedSectionsCorepresentation (V : Over U) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op V.left) ⋙ forget AddCommGrpCat).CorepresentableBy
      (((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).obj
        ((freeYonedaSheafFunctor (J.over U)).obj V)) where
  homEquiv :=
    ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).homEquiv _ _ |>.trans
      (freeYonedaSheafSectionsEquiv (J.over U) V _).toEquiv
  homEquiv_comp g f := by
    let adj := (Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J
    exact (congrArg (freeYonedaSheafSectionsEquiv (J.over U) V _)
      (adj.homEquiv_naturality_right f g)).trans
      (freeYonedaSheafSectionsEquiv_naturality_right (J.over U) _
        ((J.overPullback AddCommGrpCat.{v} U).map g))

/-- Extension to the ambient site sends the free abelian sheaf on `V : Over U` to the free
abelian sheaf on `V.left`. -/
def sheafPullbackFreeYonedaIso (V : Over U) :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).obj
      ((freeYonedaSheafFunctor (J.over U)).obj V) ≅ (freeYonedaSheafFunctor J).obj V.left :=
  (extendedSectionsCorepresentation J U V).uniqueUpToIso (sectionsCorepresentation J V.left)

end

noncomputable section Preorder

variable {P : Type u} [Preorder P] (J : GrothendieckTopology P) (U : P)
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (J.over U) AddCommGrpCat.{u})]

local instance : (J.overPullback AddCommGrpCat.{u} U).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{u} (J.over U) J).isLeftAdjoint

local instance : ((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{u} (J.over U) J).isLeftAdjoint

local instance : ((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance : (J.overPullback AddCommGrpCat.{u} U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- On a preorder site, cohomology at `U` agrees with cohomology at the terminal object of the
localized site, naturally in the coefficient sheaf. -/
private def cohomologyPresheafEvaluationIsoOver (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Pᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
    J.overPullback AddCommGrpCat.{u} U ⋙
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (J.over U) n ⋙
        (evaluation (Over U)ᵒᵖ AddCommGrpCat.{u}).obj (op (Over.mk (𝟙 U))) := by
  rw [cohomologyPresheafFunctor_eq, cohomologyPresheafFunctor_eq]
  exact (Abelian.extFunctor n).mapIso (sheafPullbackFreeYonedaIso J U (Over.mk (𝟙 U))).op ≪≫
    NatIso.ofComponents
      (fun F ↦ AddEquiv.toAddCommGrpIso
        (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{u} (J.over U) J).extEquiv))
      (by
        intro F G f
        ext x
        let adj := (Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{u} (J.over U) J
        exact adj.extEquiv_naturality_right₀ x f)

/-- Cohomology at `U` agrees with the cohomology of the restricted sheaf, naturally in the
coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoFunctorOverH (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Pᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
    J.overPullback AddCommGrpCat.{u} U ⋙ _root_.CategoryTheory.Sheaf.functorH (J.over U) n :=
  cohomologyPresheafEvaluationIsoOver J U n ≪≫
    Functor.isoWhiskerLeft (J.overPullback AddCommGrpCat.{u} U)
      (_root_.CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over U) n
        (Over.mkIdTerminal (X := U)))

/-- Cohomology at an object of a preorder site is the cohomology of the restricted sheaf on its
lower interval. -/
def cohomologyPresheafObjIsoOverH (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    _root_.CategoryTheory.Sheaf.H' F n U ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H (F.over U) n) :=
  (cohomologyPresheafEvaluationIsoFunctorOverH J U n).app F

end Preorder

end TauCeti.CategoryTheory
