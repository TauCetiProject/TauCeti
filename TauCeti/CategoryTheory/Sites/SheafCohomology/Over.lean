/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import TauCeti.Algebra.Homology.Ext.Map.AcyclicResolution
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.CategoryTheory.Sites.Pullback
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

The over-site comparison carries resolution cocycles to their actual transported classes.
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


/-- The actual over-site comparison acts on a class by the exact restriction adjunction. -/
lemma cohomologyPresheafEvaluationIsoFunctorOverH_hom_app_apply
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (x : F.H' n U) :
    (J.cohomologyPresheafEvaluationIsoFunctorOverH U n).hom.app F x =
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over U) n
        (Over.mkIdTerminal (X := U))).hom.app ((J.overPullback AddCommGrpCat.{v} U).obj F)
        (((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J).extEquiv
          ((Abelian.Ext.mk₀ (J.sheafPullbackFreeYonedaIso U (Over.mk (𝟙 U))).hom).comp
            x (zero_add n))) := by
  rfl

/-! ### Resolution classes under the actual over-site comparison -/

open CochainComplex CategoryTheory.Abelian


variable {F : Sheaf J AddCommGrpCat.{v}}
  (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)
  (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1))

/-- Restriction to the over site preserves the class of a resolution cocycle. -/
lemma cohomologyPresheafObjIsoOver_resolutionClass {n : ℕ} (s : (K.X n).obj.obj (op U))
    (hs : (K.d n (n + 1)).hom.app (op U) s = 0) :
    let G := J.overPullback AddCommGrpCat.{v} U
    (J.cohomologyPresheafEvaluationIsoFunctorOverH U n).hom.app F
      (Sheaf.H'.resolutionClass ι hι hι' hK U s hs) =
    (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (J.over U) n
      (Over.mkIdTerminal (X := U))).hom.app (G.obj F)
      (Sheaf.H'.resolutionClass (G.map ι)
        (map_augmentation_comp_d G hι)
        (map_augmentation_exact G hι')
        (map_exactAt_succ G hK)
        (Over.mk (𝟙 U)) s hs) := by
  let G := J.overPullback AddCommGrpCat.{v} U
  let KU : CochainComplex _ ℕ := (G.mapHomologicalComplex (.up ℕ)).obj K
  let c := (freeYonedaSheafSectionsEquiv J U (K.X n)).symm s
  rw [cohomologyPresheafEvaluationIsoFunctorOverH_hom_app_apply]
  congr 1
  -- The right-hand class uses `s` as a section of `G.obj (K.X n)` at `Over.mk (𝟙 U)`, which is
  -- the carrier `(K.X n).obj.obj (op U)` only after unfolding `overPullback`. The rewrites below
  -- that mention this transported section therefore need `erw`.
  erw [Sheaf.H'.resolutionClass_def, Sheaf.H'.resolutionClass_def]
  erw [CochainComplex.mk₀_comp_extMk, extEquiv_extMk]
  congr 1
  apply (freeYonedaSheafSectionsEquiv (J.over U) (Over.mk (𝟙 U)) (KU.X n)).injective
  erw [AddEquiv.apply_symm_apply]
  have hv := (freeYonedaSheafAdjunction_sectionsEquiv (J.over U) J (Over.forget U)
    (Over.mk (𝟙 U)) (K.X n)
    ((J.sheafPullbackFreeYonedaIso U (Over.mk (𝟙 U))).hom ≫ c)).symm
  dsimp only [sheafPullbackFreeYonedaIso, c] at hv
  -- `hv` is stated for `Over.forget U` and the over-site representable, which become the
  -- carriers of the goal only after unfolding the continuous pushforward.
  erw [IsIso.hom_inv_id_assoc, AddEquiv.apply_symm_apply] at hv
  -- `overPullback` is continuous pushforward; its representable has the same op/unop object.
  exact hv

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
