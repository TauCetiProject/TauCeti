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

open CategoryTheory MonoidalCategory

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
  simp only [evaluation_leftDual_obj, whiskerLeft_map, ← Functor.map_comp]
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
  simp only [evaluation_rightDual_obj, map_whiskerRight, ← Functor.map_comp]
  -- As above, rewriting `rightDual_obj` abstracts the whiskering object but leaves the mapped
  -- evaluation's fixed source, the image of `Yᘁ ⊗ Y`; the resulting motive is ill-typed.
  -- The descended dual and whiskering are definitionally the source images, allowing `map`
  -- to identify the entire characteristic composite without transporting its evaluation.
  exact congrArg (toMonoidalQuotient I).map (rightAdjointMate_comp_evaluation f).symm

end TauCeti.MonoidalQuotient
