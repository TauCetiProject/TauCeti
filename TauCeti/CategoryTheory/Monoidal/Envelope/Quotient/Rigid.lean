/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Envelope.Quotient.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Duals in quotients by tensor ideals

The quotient of a monoidal preadditive category by a tensor ideal inherits the chosen left and
right duals of its objects. Its evaluations and coevaluations are the classes of the original
ones, and taking adjoint mates commutes with the quotient functor. In particular, left rigidity,
right rigidity and rigidity descend to the quotient. No closure hypothesis beyond being a tensor
ideal is needed.

The duals follow `CategoryTheory.Functor.mapHasLeftDual` and
`CategoryTheory.Functor.mapHasRightDual`, reusing `CategoryTheory.Functor.mapExactPairing` along
the strong monoidal quotient functor. Their carriers are specified explicitly so that the
evaluation equations can be used without unfolding the generic dual-transfer constructions.
The instances use the caller's dual of the underlying object `X.as`, so an individual object
needs a dual only on the corresponding side; rigidity of the whole source category is unnecessary.

This is the rigid structure used in semisimplification of diagram categories by tensor ideals.
For the Temperley–Lieb setting, see F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb
category*, appendix to M. H. Freedman, *A magnetic model with a possible Chern–Simons phase*,
Comm. Math. Phys. 234 (2003), 129–183.
-/

public section

universe v u

namespace TauCeti.MonoidalQuotient

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] {I : MonoidalIdeal C}

/-- The left dual of a quotient object is the class of its underlying object's chosen left
dual. -/
noncomputable instance instHasLeftDual (X : MonoidalQuotient I) [HasLeftDual X.as] :
    HasLeftDual X where
  leftDual := (toMonoidalQuotient I).obj (ᘁ(X.as) : C)
  exact := (toMonoidalQuotient I).mapExactPairing (ᘁ(X.as) : C) X.as

/-- The right dual of a quotient object is the class of its underlying object's chosen right
dual. -/
noncomputable instance instHasRightDual (X : MonoidalQuotient I) [HasRightDual X.as] :
    HasRightDual X where
  rightDual := (toMonoidalQuotient I).obj ((X.as)ᘁ : C)
  exact := (toMonoidalQuotient I).mapExactPairing X.as ((X.as)ᘁ : C)

-- Typeclass search does not unfold the quotient functor's object map to identify its underlying
-- object. These delegates preserve the source dual choices at that public presentation too.
/-- The image of an object with a left dual has the descended left dual. -/
noncomputable instance instHasLeftDualObj (X : C) [HasLeftDual X] :
    HasLeftDual ((toMonoidalQuotient I).obj X) :=
  inferInstanceAs (HasLeftDual (CategoryTheory.Quotient.mk X : MonoidalQuotient I))

/-- The image of an object with a right dual has the descended right dual. -/
noncomputable instance instHasRightDualObj (X : C) [HasRightDual X] :
    HasRightDual ((toMonoidalQuotient I).obj X) :=
  inferInstanceAs (HasRightDual (CategoryTheory.Quotient.mk X : MonoidalQuotient I))

/-- The left dual in the quotient is the class of the chosen left dual in the source. -/
@[simp]
theorem leftDual_eq (X : MonoidalQuotient I) [HasLeftDual X.as] :
    (ᘁX : MonoidalQuotient I) = (toMonoidalQuotient I).obj (ᘁ(X.as) : C) :=
  (rfl)

/-- The right dual in the quotient is the class of the chosen right dual in the source. -/
@[simp]
theorem rightDual_eq (X : MonoidalQuotient I) [HasRightDual X.as] :
    Xᘁ = (toMonoidalQuotient I).obj ((X.as)ᘁ : C) :=
  (rfl)

/-- The evaluation for the descended left dual is the class of the original evaluation. -/
@[simp]
theorem evaluation_leftDual (X : MonoidalQuotient I) [HasLeftDual X.as] :
    ε_ (ᘁX) X = (toMonoidalQuotient I).map (ε_ (ᘁ(X.as) : C) X.as) := by
  exact (Functor.mapExactPairing_evaluation
    (F := toMonoidalQuotient I) (ᘁ(X.as) : C) X.as).trans (by simp)

/-- The coevaluation for the descended left dual is the class of the original coevaluation. -/
@[simp]
theorem coevaluation_leftDual (X : MonoidalQuotient I) [HasLeftDual X.as] :
    η_ (ᘁX) X = (toMonoidalQuotient I).map (η_ (ᘁ(X.as) : C) X.as) := by
  exact (Functor.mapExactPairing_coevaluation
    (F := toMonoidalQuotient I) (ᘁ(X.as) : C) X.as).trans (by simp)

/-- The evaluation for the descended right dual is the class of the original evaluation. -/
@[simp]
theorem evaluation_rightDual (X : MonoidalQuotient I) [HasRightDual X.as] :
    ε_ X Xᘁ = (toMonoidalQuotient I).map (ε_ X.as ((X.as)ᘁ : C)) := by
  exact (Functor.mapExactPairing_evaluation
    (F := toMonoidalQuotient I) X.as ((X.as)ᘁ : C)).trans (by simp)

/-- The coevaluation for the descended right dual is the class of the original coevaluation. -/
@[simp]
theorem coevaluation_rightDual (X : MonoidalQuotient I) [HasRightDual X.as] :
    η_ X Xᘁ = (toMonoidalQuotient I).map (η_ X.as ((X.as)ᘁ : C)) := by
  exact (Functor.mapExactPairing_coevaluation
    (F := toMonoidalQuotient I) X.as ((X.as)ᘁ : C)).trans (by simp)

-- These equations retain the literal source object and its caller-provided dual instance.
-- Rewriting the general equations first leaves a dependent dual of the underlying-object
-- projection, which the simplifier cannot identify with that caller's instance. The mapped-object
-- rules therefore run before simplification of their dependent arguments.
/-- The left dual of the image of an object is the image of its chosen left dual. -/
@[simp↓]
theorem leftDual_obj (X : C) [HasLeftDual X] :
    (ᘁ((toMonoidalQuotient I).obj X) : MonoidalQuotient I) =
      (toMonoidalQuotient I).obj (ᘁX) :=
  leftDual_eq (CategoryTheory.Quotient.mk X)

/-- The right dual of the image of an object is the image of its chosen right dual. -/
@[simp↓]
theorem rightDual_obj (X : C) [HasRightDual X] :
    ((toMonoidalQuotient I).obj X)ᘁ = (toMonoidalQuotient I).obj (Xᘁ) :=
  rightDual_eq (CategoryTheory.Quotient.mk X)

/-- Evaluation on the image of an object with its descended left dual. -/
@[simp↓]
theorem evaluation_leftDual_obj (X : C) [HasLeftDual X] :
    ε_ (ᘁ((toMonoidalQuotient I).obj X)) ((toMonoidalQuotient I).obj X) =
      (toMonoidalQuotient I).map (ε_ (ᘁX) X) :=
  evaluation_leftDual (CategoryTheory.Quotient.mk X)

/-- Coevaluation on the image of an object with its descended left dual. -/
@[simp↓]
theorem coevaluation_leftDual_obj (X : C) [HasLeftDual X] :
    η_ (ᘁ((toMonoidalQuotient I).obj X)) ((toMonoidalQuotient I).obj X) =
      (toMonoidalQuotient I).map (η_ (ᘁX) X) :=
  coevaluation_leftDual (CategoryTheory.Quotient.mk X)

/-- Evaluation on the image of an object with its descended right dual. -/
@[simp↓]
theorem evaluation_rightDual_obj (X : C) [HasRightDual X] :
    ε_ ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj X)ᘁ =
      (toMonoidalQuotient I).map (ε_ X Xᘁ) :=
  evaluation_rightDual (CategoryTheory.Quotient.mk X)

/-- Coevaluation on the image of an object with its descended right dual. -/
@[simp↓]
theorem coevaluation_rightDual_obj (X : C) [HasRightDual X] :
    η_ ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj X)ᘁ =
      (toMonoidalQuotient I).map (η_ X Xᘁ) :=
  coevaluation_rightDual (CategoryTheory.Quotient.mk X)

/-- A quotient by a tensor ideal of a left rigid monoidal preadditive category is left rigid. -/
noncomputable instance instLeftRigidCategory [LeftRigidCategory C] :
    LeftRigidCategory (MonoidalQuotient I) where

/-- A quotient by a tensor ideal of a right rigid monoidal preadditive category is right rigid. -/
noncomputable instance instRightRigidCategory [RightRigidCategory C] :
    RightRigidCategory (MonoidalQuotient I) where

/-- A quotient by a tensor ideal of a rigid monoidal preadditive category is rigid. -/
noncomputable instance instRigidCategory [RigidCategory C] :
    RigidCategory (MonoidalQuotient I) where

/-- The left adjoint mate of a class is the class of the left adjoint mate. -/
@[simp]
theorem leftAdjointMate_map {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    (ᘁ((toMonoidalQuotient I).map f)) = (toMonoidalQuotient I).map (ᘁf) := by
  apply ExactPairing.leftDualHom_ext (Y := (toMonoidalQuotient I).obj X)
  rw [leftAdjointMate_comp_evaluation]
  simp only [evaluation_leftDual_obj, CategoryTheory.Quotient.whiskerLeft_map,
    ← Functor.map_comp]
  -- Rewriting `leftDual_obj` here gives an ill-typed motive: the following mapped evaluation
  -- has fixed source the image of `Y ⊗ ᘁY`, while rewriting abstracts its dual object alone.
  -- The chosen dual and quotient whiskering are definitionally the source images, so applying
  -- `map` to the characteristic equation identifies the entire composite without transport.
  exact congrArg (toMonoidalQuotient I).map (leftAdjointMate_comp_evaluation f).symm

/-- The right adjoint mate of a class is the class of the right adjoint mate. -/
@[simp]
theorem rightAdjointMate_map {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    ((toMonoidalQuotient I).map f)ᘁ = (toMonoidalQuotient I).map (fᘁ) := by
  apply ExactPairing.rightHom_ext (X := (toMonoidalQuotient I).obj X)
  rw [rightAdjointMate_comp_evaluation]
  simp only [evaluation_rightDual_obj, CategoryTheory.Quotient.map_whiskerRight,
    ← Functor.map_comp]
  -- As above, rewriting `rightDual_obj` abstracts the whiskering object but leaves the mapped
  -- evaluation's fixed source, the image of `Yᘁ ⊗ Y`; the resulting motive is ill-typed.
  -- The descended dual and whiskering are definitionally the source images, allowing `map`
  -- to identify the entire characteristic composite without transporting its evaluation.
  exact congrArg (toMonoidalQuotient I).map (rightAdjointMate_comp_evaluation f).symm

/-- The dual comparison for the quotient functor is the identity: its chosen duals are
exactly the images of the source duals. -/
@[simp]
theorem mapRightDualIso_eq_refl (X : C) [HasRightDual X] :
    (toMonoidalQuotient I).mapRightDualIso X = Iso.refl _ := by
  apply Iso.ext
  apply ExactPairing.rightHom_ext (X := (toMonoidalQuotient I).obj X)
  simpa using Functor.mapRightDualIso_hom_whiskerRight_evaluation
    (F := toMonoidalQuotient I) X

/-- A morphism from a descended right dual is determined by its composite with the
image of any source evaluation. -/
theorem eq_map_of_whiskerRight_evaluation {X Y : C} [HasRightDual X] [ExactPairing X Y]
    (f : ((toMonoidalQuotient I).obj X)ᘁ ⟶ (toMonoidalQuotient I).obj Y)
    (g : Xᘁ ⟶ Y)
    (h : f ▷ (toMonoidalQuotient I).obj X ≫ (toMonoidalQuotient I).map (ε_ X Y) =
      (toMonoidalQuotient I).map (g ▷ X ≫ ε_ X Y)) :
    f = (toMonoidalQuotient I).map g := by
  let := (toMonoidalQuotient I).mapExactPairing X Y
  apply ExactPairing.rightHom_ext (X := (toMonoidalQuotient I).obj X)
  simpa only [Functor.mapExactPairing_evaluation, CategoryTheory.Quotient.functor_μ,
    CategoryTheory.Quotient.functor_η, Category.id_comp, Category.comp_id,
    CategoryTheory.Quotient.map_whiskerRight, ← Functor.map_comp] using h

section RightRigid

variable [RightRigidCategory C]

/-- Taking a mate commutes with the quotient functor for the global rigid choices too,
including at the unit where instance search otherwise selects the canonical self-duality. -/
theorem rightAdjointMate_map_rightRigid {X Y : C} (f : X ⟶ Y) :
    @rightAdjointMate (MonoidalQuotient I) _ _
      ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj Y)
      (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual _)
      ((toMonoidalQuotient I).map f) = (toMonoidalQuotient I).map (fᘁ) :=
  rightAdjointMate_map f

/-- The tensor comparison of the right dual descends to the quotient. -/
@[simp]
theorem rightDualTensorIso_obj_hom (X Y : C) :
    (rightDualTensorIso ((toMonoidalQuotient I).obj X)
      ((toMonoidalQuotient I).obj Y)).hom =
        (toMonoidalQuotient I).map (rightDualTensorIso X Y).hom := by
  apply eq_map_of_whiskerRight_evaluation (X := X ⊗ Y) (Y := Yᘁ ⊗ Xᘁ)
  have h := TauCeti.rightDualTensorIso_hom_whiskerRight_evaluation
    (X := (toMonoidalQuotient I).obj X) (Y := (toMonoidalQuotient I).obj Y)
  simp only [ExactPairing.tensor_evaluation, evaluation_rightDual] at h ⊢
  -- With the descended evaluations explicit, the quotient's tensor and whiskering composites
  -- are the source composites mapped as a whole, without transporting their dependent endpoints.
  exact h.trans (congrArg (toMonoidalQuotient I).map
    (TauCeti.rightDualTensorIso_hom_whiskerRight_evaluation (X := X) (Y := Y)).symm)

/-- The inverse tensor comparison of the right dual also descends. -/
@[simp]
theorem rightDualTensorIso_obj_inv (X Y : C) :
    (rightDualTensorIso ((toMonoidalQuotient I).obj X)
      ((toMonoidalQuotient I).obj Y)).inv =
        (toMonoidalQuotient I).map (rightDualTensorIso X Y).inv := by
  have h : rightDualTensorIso ((toMonoidalQuotient I).obj X)
      ((toMonoidalQuotient I).obj Y) =
        (toMonoidalQuotient I).mapIso (rightDualTensorIso X Y) :=
    Iso.ext (rightDualTensorIso_obj_hom X Y)
  exact congrArg Iso.inv h

/-- The tensorator of the double right dual is the class of its original tensorator. -/
@[simp]
theorem doubleRightDualFunctor_μ_obj (X Y : C) :
    μ (doubleRightDualFunctor (MonoidalQuotient I))
      ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj Y) =
        (toMonoidalQuotient I).map (μ (doubleRightDualFunctor C) X Y) := by
  rw [doubleRightDualFunctor_μ, doubleRightDualFunctor_μ, rightDualTensorIso_obj_hom]
  -- Rewriting the inverse comparison cannot match the descended duals with mapped source
  -- duals at the rewriter's transparency, including the composite's fixed bidual endpoints.
  -- Compose the descent equations as terms, using the chosen duals' definitional identification.
  exact (congrArg₂ (· ≫ ·) (rightDualTensorIso_obj_inv Yᘁ Xᘁ)
    (rightAdjointMate_map_rightRigid (rightDualTensorIso X Y).hom)).trans
      ((toMonoidalQuotient I).map_comp _ _).symm

/-- The inverse tensorator of the double right dual descends to the quotient. -/
@[simp]
theorem doubleRightDualFunctor_δ_obj (X Y : C) :
    δ (doubleRightDualFunctor (MonoidalQuotient I))
      ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj Y) =
        (toMonoidalQuotient I).map (δ (doubleRightDualFunctor C) X Y) := by
  rw [doubleRightDualFunctor_δ, doubleRightDualFunctor_δ, rightDualTensorIso_obj_inv]
  -- As for the tensorator, rewriting cannot match the tensor comparison at descended duals
  -- with its mapped-source form while retaining the composite's fixed bidual endpoints.
  -- Term congruence uses their definitional identification without abstracting those endpoints.
  exact (congrArg₂ (· ≫ ·) (rightAdjointMate_map_rightRigid (rightDualTensorIso X Y).inv)
    (rightDualTensorIso_obj_hom Yᘁ Xᘁ)).trans
      ((toMonoidalQuotient I).map_comp _ _).symm

/-- The identification of the chosen right dual of the unit with the unit descends. The
rigid category's choice is explicit, since the unit also has a canonical self-duality. -/
@[simp]
theorem rightDualIso_exactPairingUnit_hom :
    (rightDualIso
      (RightRigidCategory.rightDual (𝟙_ (MonoidalQuotient I))).exact
      exactPairingUnit).hom =
    (toMonoidalQuotient I).map (rightDualIso
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
  apply eq_map_of_whiskerRight_evaluation (X := 𝟙_ C) (Y := 𝟙_ C)
  refine (ExactPairing.rightDualIso_hom_whiskerRight_evaluation
    (RightRigidCategory.rightDual (𝟙_ (MonoidalQuotient I))).exact exactPairingUnit).trans ?_
  exact (evaluation_rightDual_obj (𝟙_ C)).trans
    (congrArg (toMonoidalQuotient I).map
      (ExactPairing.rightDualIso_hom_whiskerRight_evaluation
        (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).symm)

/-- The inverse identification of the chosen unit dual descends. -/
@[simp]
theorem rightDualIso_exactPairingUnit_inv :
    (rightDualIso (RightRigidCategory.rightDual (𝟙_ (MonoidalQuotient I))).exact
      exactPairingUnit).inv =
    (toMonoidalQuotient I).map (rightDualIso
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv := by
  have h : rightDualIso (RightRigidCategory.rightDual (𝟙_ (MonoidalQuotient I))).exact
      exactPairingUnit = (toMonoidalQuotient I).mapIso
        (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit) :=
    Iso.ext rightDualIso_exactPairingUnit_hom
  exact congrArg Iso.inv h

/-- The unit comparison of the double right dual descends, using the rigid structure's
chosen dual of the unit on both sides. -/
@[simp]
theorem doubleRightDualFunctor_ε_eq_map :
    ε (doubleRightDualFunctor (MonoidalQuotient I)) =
      (toMonoidalQuotient I).map (ε (doubleRightDualFunctor C)) := by
  rw [doubleRightDualFunctor_ε_eq_rightAdjointMate,
    doubleRightDualFunctor_ε_eq_rightAdjointMate,
    rightDualIso_exactPairingUnit_hom, rightDualIso_exactPairingUnit_inv]
  -- Rewriting the mate and map_comp leaves dual-instance presentations of the unit that
  -- rw cannot identify. Term congruence identifies the rigidly chosen dual and its image
  -- definitionally, keeping the composite's unit and bidual endpoints together.
  exact (congrArg₂ (· ≫ ·) (Eq.refl _)
    (rightAdjointMate_map_rightRigid (rightDualIso
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom)).trans
        ((toMonoidalQuotient I).map_comp _ _).symm

/-- The inverse unit comparison of the double right dual descends to the quotient. -/
@[simp]
theorem doubleRightDualFunctor_η_eq_map :
    η (doubleRightDualFunctor (MonoidalQuotient I)) =
      (toMonoidalQuotient I).map (η (doubleRightDualFunctor C)) := by
  apply (cancel_epi (ε (doubleRightDualFunctor (MonoidalQuotient I)))).mp
  rw [Functor.Monoidal.ε_η, doubleRightDualFunctor_ε_eq_map]
  -- rw [← Functor.map_comp] cannot match the mapped bidual of the source unit with the
  -- quotient unit's bidual at its transparency. Map the entire inverse law instead;
  -- these endpoints are definitionally equal for the descended rigid dual choices.
  exact ((toMonoidalQuotient I).map_comp _ _).symm.trans
    (congrArg (toMonoidalQuotient I).map (Functor.Monoidal.ε_η (doubleRightDualFunctor C)))
      |>.trans ((toMonoidalQuotient I).map_id _) |>.symm

end RightRigid

end TauCeti.MonoidalQuotient
