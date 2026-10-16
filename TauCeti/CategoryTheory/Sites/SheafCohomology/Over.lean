/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal

/-!
# Cohomology on a localized site

Cohomology at an object agrees with cohomology of the restricted sheaf on the localized site
when restriction and its left adjoint are exact. On a preorder site, this left adjoint is
extension by zero to the ambient site. For the site of open subsets of a space, the comparison
identifies cohomology on an open subset with cohomology of the restricted sheaf.

The comparison uses the action of the left adjoint on free abelian representable sheaves and
Mathlib's `CategoryTheory.Adjunction.extEquiv` for exact adjunctions.

## Main declarations

* `CategoryTheory.GrothendieckTopology.sheafPullbackFreeYonedaIso`: extension on the source
  objects defining cohomology on an object of the site.
* `CategoryTheory.GrothendieckTopology.cohomologyPresheafEvaluationIsoFunctorOverH`: the comparison,
  natural in the coefficient sheaf.
* `CategoryTheory.Sheaf.cohomologyPresheafObjIsoOverH`: `Hⁿ(U, F) ≅ Hⁿ(F.over U)`.

This comparison transports acyclicity of the restricted sheaf to vanishing of cohomology on
the corresponding object, for instance from affine acyclicity to local vanishing hypotheses.
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

open TauCeti.CategoryTheory

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]

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
  (extendedSectionsCorepresentation J U V).uniqueUpToIso (freeYonedaSheafCorepresentableBy J V.left)

end

local instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint] :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).isLeftAdjoint

local instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C) :
    (J.overPullback AddCommGrpCat.{v} U).Additive where
  map_add := rfl

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
  [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
  [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
  [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)]

local instance : ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Under an exact restriction adjunction, cohomology at `U` agrees with cohomology at the
terminal object of the localized site, naturally in the coefficient sheaf. -/
private def cohomologyPresheafEvaluationIsoOver (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (J.over U) n ⋙
        (evaluation (Over U)ᵒᵖ AddCommGrpCat.{w}).obj (op (Over.mk (𝟙 U))) := by
  rw [cohomologyPresheafFunctor_eq, cohomologyPresheafFunctor_eq]
  exact (Abelian.extFunctor n).mapIso (sheafPullbackFreeYonedaIso J U (Over.mk (𝟙 U))).op ≪≫
    NatIso.ofComponents
      (fun F ↦ AddEquiv.toAddCommGrpIso
        (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).extEquiv))
      (by
        intro F G f
        ext x
        let adj := (Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J
        exact adj.extEquiv_naturality_right₀ x f)

/-- Under an exact restriction adjunction, cohomology at `U` agrees with the cohomology of the
restricted sheaf, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoFunctorOverH (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙ _root_.CategoryTheory.Sheaf.functorH (J.over U) n :=
  cohomologyPresheafEvaluationIsoOver J U n ≪≫
    Functor.isoWhiskerLeft (J.overPullback AddCommGrpCat.{v} U)
      (_root_.CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over U) n
        (Over.mkIdTerminal (X := U)))

end

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- Under an exact restriction adjunction, cohomology at an object is the cohomology of the
restricted sheaf on the localized site. -/
noncomputable def cohomologyPresheafObjIsoOverH (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
    [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
    [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)] :
    H' F n U ≅ AddCommGrpCat.of (H (F.over U) n) :=
  (J.cohomologyPresheafEvaluationIsoFunctorOverH U n).app F

end CategoryTheory.Sheaf
