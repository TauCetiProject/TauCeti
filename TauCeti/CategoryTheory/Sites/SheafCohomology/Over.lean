/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal

/-!
# Cohomology on a localized site

Cohomology at an object agrees with cohomology of the restricted sheaf on the localized site
when restriction and its left adjoint are exact. On a preorder site, this left adjoint is
extension by zero to the ambient site. For the site of open subsets of a space, the comparison
identifies cohomology on an open subset with cohomology of the restricted sheaf. More generally,
for every `V : Over U`, cohomology at `V.left` agrees with the cohomology of the restricted sheaf
at `V`, naturally in `V`: the cohomology presheaf of the restricted sheaf is the restriction to
`Over U` of the cohomology presheaf.

The comparison uses the action of the left adjoint on free abelian representable sheaves and
Mathlib's `CategoryTheory.Adjunction.extEquiv` for exact adjunctions.

## Main declarations

* `CategoryTheory.GrothendieckTopology.sheafPullbackFreeYonedaIso`: extension on the source
  objects defining cohomology on an object of the site.
* `CategoryTheory.GrothendieckTopology.cohomologyPresheafFunctorOverIso`: the cohomology presheaf
  of the restricted sheaf on `Over U` is the restriction of the cohomology presheaf, naturally in
  the coefficient sheaf.
* `CategoryTheory.GrothendieckTopology.cohomologyPresheafEvaluationIsoFunctorOverH`: the comparison
  at `U`, natural in the coefficient sheaf.
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

/-- Extension to the ambient site sends the free abelian sheaf on `V : Over U` to the free
abelian sheaf on `V.left`: the inverse of the comparison
`CategoryTheory.Functor.freeYonedaSheafToSheafPullback` for the forgetful functor. -/
def sheafPullbackFreeYonedaIso (V : Over U) :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).obj
      ((freeYonedaSheafFunctor (J.over U)).obj V) ≅ (freeYonedaSheafFunctor J).obj V.left :=
  (asIso (((Over.forget U).freeYonedaSheafToSheafPullback (J.over U) J).app V)).symm

/-- The isomorphism `sheafPullbackFreeYonedaIso` is natural in `V : Over U`. -/
@[reassoc]
lemma sheafPullbackFreeYonedaIso_hom_naturality {V W : Over U} (g : V ⟶ W) :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).map
        ((freeYonedaSheafFunctor (J.over U)).map g) ≫ (sheafPullbackFreeYonedaIso J U W).hom =
      (sheafPullbackFreeYonedaIso J U V).hom ≫ (freeYonedaSheafFunctor J).map g.left := by
  rw [sheafPullbackFreeYonedaIso, sheafPullbackFreeYonedaIso, Iso.symm_hom, Iso.symm_hom,
    asIso_inv, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact (((Over.forget U).freeYonedaSheafToSheafPullback (J.over U) J).naturality g).symm

end

local instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint] :
    ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).isLeftAdjoint

/-- Restriction of abelian sheaves to the localized site `J.over U` is additive. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C) :
    (J.overPullback AddCommGrpCat.{v} U).Additive where
  map_add := rfl

/-- Restriction of abelian sheaves to the localized site `J.over U` preserves injective objects
when its left adjoint, extension to the ambient site, preserves finite limits. -/
instance preservesInjectiveObjects_overPullback {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
    [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)] :
    (J.overPullback AddCommGrpCat.{v} U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J)

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{v})]
  [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
  [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
  [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)]

/-- Under an exact restriction adjunction, cohomology at `V.left` agrees with the cohomology at
`V : Over U` of the restricted sheaf on the localized site, naturally in the coefficient sheaf. -/
private def cohomologyPresheafEvaluationIsoOver (n : ℕ) (V : Over U) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op V.left) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (J.over U) n ⋙
        (evaluation (Over U)ᵒᵖ AddCommGrpCat.{w}).obj (op V) := by
  rw [cohomologyPresheafFunctor_eq, cohomologyPresheafFunctor_eq]
  exact (Abelian.extFunctor n).mapIso (sheafPullbackFreeYonedaIso J U V).op ≪≫
    NatIso.ofComponents
      (fun F ↦ AddEquiv.toAddCommGrpIso
        (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).extEquiv))
      (by
        intro F G f
        ext x
        let adj := (Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J
        exact adj.extEquiv_naturality_right₀ x f)

/-- **Cohomology on a localized site is the restriction of cohomology.** Under an exact
restriction adjunction, the cohomology presheaf `V ↦ Hⁿ(V, F|_U)` of the restriction of `F` to the
localized site `J.over U` is the restriction to `Over U` of the cohomology presheaf
`W ↦ Hⁿ(W, F)` of `F`, naturally in the abelian sheaf `F`
(`CategoryTheory.GrothendieckTopology.cohomologyPresheafFunctorOverIso_hom_app_app_apply`). -/
def cohomologyPresheafFunctorOverIso (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{w}).obj (Over.forget U).op ≅
    J.overPullback AddCommGrpCat.{v} U ⋙
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor (J.over U) n :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents (fun V ↦ (cohomologyPresheafEvaluationIsoOver J U n V.unop).app F)
      (fun {V W} g ↦ by
        ext x
        have h := ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U)
          J).extEquiv_naturality_left₀ ((freeYonedaSheafFunctor (J.over U)).map g.unop)
            ((Abelian.Ext.mk₀ (sheafPullbackFreeYonedaIso J U V.unop).hom).comp
              (F.H'AddEquivExt n V.unop.left x) (zero_add n))
        rw [Abelian.Ext.mk₀_comp_mk₀_assoc, sheafPullbackFreeYonedaIso_hom_naturality,
          ← Abelian.Ext.mk₀_comp_mk₀_assoc] at h
        -- Both sides of the goal are, on `Ext` classes, the two sides of `h`: the restriction maps
        -- of the cohomology presheaves are precomposition with the induced maps of free abelian
        -- sheaves (`Sheaf.cohomologyPresheaf_map_apply`), and the components precompose with
        -- `sheafPullbackFreeYonedaIso` and apply `extEquiv`
        -- (`cohomologyPresheafFunctorOverIso_hom_app_app_apply` below).
        exact h))
    (fun {F G} f ↦ by
      ext V : 2
      exact (cohomologyPresheafEvaluationIsoOver J U n V.unop).hom.naturality f)

/-- On a class written as `Ext` from the free abelian sheaf on `V.left`, the comparison
`cohomologyPresheafFunctorOverIso` precomposes with `sheafPullbackFreeYonedaIso` and applies the
bijection of `Ext` groups of the restriction adjunction. -/
lemma cohomologyPresheafFunctorOverIso_hom_app_app_apply (n : ℕ) (F : Sheaf J AddCommGrpCat.{v})
    (V : Over U) (x : F.H' n V.left) :
    (F.over U).H'AddEquivExt n V
        (((cohomologyPresheafFunctorOverIso J U n).hom.app F).app (op V) x) =
      ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).extEquiv
        ((Abelian.Ext.mk₀ (sheafPullbackFreeYonedaIso J U V).hom).comp
          (F.H'AddEquivExt n V.left x) (zero_add n)) :=
  (rfl)

/-- Under an exact restriction adjunction, cohomology at `U` agrees with the cohomology of the
restricted sheaf, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoFunctorOverH (n : ℕ) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U) ≅
    J.overPullback AddCommGrpCat.{v} U ⋙ _root_.CategoryTheory.Sheaf.functorH (J.over U) n :=
  cohomologyPresheafEvaluationIsoOver J U n (Over.mk (𝟙 U)) ≪≫
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
