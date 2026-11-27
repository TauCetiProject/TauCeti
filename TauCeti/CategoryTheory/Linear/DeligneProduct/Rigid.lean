/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.DeligneProduct.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Envelope.Mat.Rigid

/-!
# Duals in the Deligne tensor product

In the linear tensor product of two rigid monoidal linear categories, duals of pairs are
componentwise and their evaluations and coevaluations are pure tensors. The matrix-category
duality then equips the Deligne product with duals of all finite families of pairs. For a pure
object, the dual is again pure, and evaluation and coevaluation are one-entry matrices of the
corresponding pure tensors.
-/

public section

open CategoryTheory MonoidalCategory

universe w v₁ v₂ u₁ u₂

namespace TauCeti.LinearTensor

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear k D]

/-- Componentwise exact pairing of pairs with exact pairings in both coordinates. -/
@[instance_reducible]
def exactPairing (P Q : LinearTensor k C D)
    [ExactPairing P.fst Q.fst] [ExactPairing P.snd Q.snd] : ExactPairing P Q where
  coevaluation' := tmul (η_ P.fst Q.fst) (η_ P.snd Q.snd)
  evaluation' := tmul (ε_ P.fst Q.fst) (ε_ P.snd Q.snd)
  coevaluation_evaluation' := by simp [ExactPairing.coevaluation_evaluation]
  evaluation_coevaluation' := by simp [ExactPairing.evaluation_coevaluation]

/-- The coevaluation of the componentwise pairing is the pure tensor of the coevaluations. -/
@[simp]
theorem exactPairing_coevaluation (P Q : LinearTensor k C D)
    [ExactPairing P.fst Q.fst] [ExactPairing P.snd Q.snd] :
    letI := exactPairing P Q
    η_ P Q = tmul (η_ P.fst Q.fst) (η_ P.snd Q.snd) :=
  (rfl)

/-- The evaluation of the componentwise pairing is the pure tensor of the evaluations. -/
@[simp]
theorem exactPairing_evaluation (P Q : LinearTensor k C D)
    [ExactPairing P.fst Q.fst] [ExactPairing P.snd Q.snd] :
    letI := exactPairing P Q
    ε_ P Q = tmul (ε_ P.fst Q.fst) (ε_ P.snd Q.snd) :=
  (rfl)

/-- The right dual of a pair is the pair of right duals. -/
instance instRightRigidCategory [RightRigidCategory C] [RightRigidCategory D] :
    RightRigidCategory (LinearTensor k C D) where
  rightDual P :=
    { rightDual := ⟨P.fstᘁ, P.sndᘁ⟩
      exact := exactPairing P ⟨P.fstᘁ, P.sndᘁ⟩ }

/-- The left dual of a pair is the pair of left duals. -/
instance instLeftRigidCategory [LeftRigidCategory C] [LeftRigidCategory D] :
    LeftRigidCategory (LinearTensor k C D) where
  leftDual P :=
    { leftDual := ⟨ᘁP.fst, ᘁP.snd⟩
      exact := exactPairing ⟨ᘁP.fst, ᘁP.snd⟩ P }

/-- The linear tensor product of two rigid monoidal linear categories is rigid. -/
instance instRigidCategory [RigidCategory C] [RigidCategory D] :
    RigidCategory (LinearTensor k C D) where

/-- The chosen right dual is computed componentwise. -/
theorem rightDual_def [RightRigidCategory C] [RightRigidCategory D] (P : LinearTensor k C D) :
    Pᘁ = ⟨P.fstᘁ, P.sndᘁ⟩ :=
  rfl

/-- The chosen left dual is computed componentwise. -/
theorem leftDual_def [LeftRigidCategory C] [LeftRigidCategory D] (P : LinearTensor k C D) :
    (ᘁP : LinearTensor k C D) = ⟨ᘁP.fst, ᘁP.snd⟩ :=
  rfl

/-- The first component of the right dual is the right dual of the first component. -/
@[simp]
theorem rightDual_fst [RightRigidCategory C] [RightRigidCategory D] (P : LinearTensor k C D) :
    (Pᘁ).fst = P.fstᘁ :=
  (rfl)

/-- The second component of the right dual is the right dual of the second component. -/
@[simp]
theorem rightDual_snd [RightRigidCategory C] [RightRigidCategory D] (P : LinearTensor k C D) :
    (Pᘁ).snd = P.sndᘁ :=
  (rfl)

/-- The first component of the left dual is the left dual of the first component. -/
@[simp]
theorem leftDual_fst [LeftRigidCategory C] [LeftRigidCategory D] (P : LinearTensor k C D) :
    (ᘁP).fst = ᘁP.fst :=
  (rfl)

/-- The second component of the left dual is the left dual of the second component. -/
@[simp]
theorem leftDual_snd [LeftRigidCategory C] [LeftRigidCategory D] (P : LinearTensor k C D) :
    (ᘁP).snd = ᘁP.snd :=
  (rfl)

-- Prefer the chosen-dual formulas to the general exact-pairing rewrites, which leave
-- projections of the dual pair to be simplified.
/-- The evaluation for the chosen right dual is the pure tensor of the right evaluations. -/
@[simp high]
theorem rightDual_evaluation [RightRigidCategory C] [RightRigidCategory D]
    (P : LinearTensor k C D) :
    ε_ P Pᘁ = tmul (ε_ P.fst P.fstᘁ) (ε_ P.snd P.sndᘁ) :=
  (rfl)

/-- The coevaluation for the chosen right dual is the pure tensor of the right coevaluations. -/
@[simp high]
theorem rightDual_coevaluation [RightRigidCategory C] [RightRigidCategory D]
    (P : LinearTensor k C D) :
    η_ P Pᘁ = tmul (η_ P.fst P.fstᘁ) (η_ P.snd P.sndᘁ) :=
  (rfl)

/-- The evaluation for the chosen left dual is the pure tensor of the left evaluations. -/
@[simp high]
theorem leftDual_evaluation [LeftRigidCategory C] [LeftRigidCategory D]
    (P : LinearTensor k C D) :
    ε_ (ᘁP) P = tmul (ε_ (ᘁP.fst) P.fst) (ε_ (ᘁP.snd) P.snd) :=
  (rfl)

/-- The coevaluation for the chosen left dual is the pure tensor of the left coevaluations. -/
@[simp high]
theorem leftDual_coevaluation [LeftRigidCategory C] [LeftRigidCategory D]
    (P : LinearTensor k C D) :
    η_ (ᘁP) P = tmul (η_ (ᘁP.fst) P.fst) (η_ (ᘁP.snd) P.snd) :=
  (rfl)

end TauCeti.LinearTensor

namespace TauCeti.DeligneProduct

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear k D]

-- Simplify the duality operations before rewriting the pure objects as matrix embeddings.
-- After `bifunctor_obj_obj`, `using!` identifies the inferred Deligne and matrix dual instances
-- by definitional equality.
section RightDual

variable [RightRigidCategory C] [RightRigidCategory D]

/-- The chosen right dual of a pure object is the pure object of the right duals. -/
@[simp↓]
theorem rightDual_bifunctor_obj_obj (X : C) (Y : D) :
    (((bifunctor k C D).obj X).obj Y)ᘁ = ((bifunctor k C D).obj Xᘁ).obj Yᘁ := by
  simpa only [bifunctor_obj_obj, LinearTensor.rightDual_def] using!
    (Mat_.rightDual_embedding_obj (⟨X, Y⟩ : LinearTensor k C D))

/-- The evaluation of a pure object against its right dual is the one-entry matrix whose entry
is the pure tensor of the evaluations in the factors. -/
@[simp↓]
theorem evaluation_rightDual_bifunctor_obj_obj (X : C) (Y : D) :
    ε_ (((bifunctor k C D).obj X).obj Y) ((((bifunctor k C D).obj X).obj Y)ᘁ) =
      fun _ _ ↦ LinearTensor.tmul (ε_ X Xᘁ) (ε_ Y Yᘁ) := by
  simpa only [bifunctor_obj_obj, LinearTensor.rightDual_evaluation] using!
    (Mat_.evaluation_rightDual_embedding_obj (⟨X, Y⟩ : LinearTensor k C D))

/-- The coevaluation of a pure object with its right dual is the one-entry matrix whose entry
is the pure tensor of the coevaluations in the factors. -/
@[simp↓]
theorem coevaluation_rightDual_bifunctor_obj_obj (X : C) (Y : D) :
    η_ (((bifunctor k C D).obj X).obj Y) ((((bifunctor k C D).obj X).obj Y)ᘁ) =
      fun _ _ ↦ LinearTensor.tmul (η_ X Xᘁ) (η_ Y Yᘁ) := by
  simpa only [bifunctor_obj_obj, LinearTensor.rightDual_coevaluation] using!
    (Mat_.coevaluation_rightDual_embedding_obj (⟨X, Y⟩ : LinearTensor k C D))

end RightDual

section LeftDual

variable [LeftRigidCategory C] [LeftRigidCategory D]

/-- The chosen left dual of a pure object is the pure object of the left duals. -/
@[simp↓]
theorem leftDual_bifunctor_obj_obj (X : C) (Y : D) :
    (ᘁ(((bifunctor k C D).obj X).obj Y) : DeligneProduct k C D) =
      ((bifunctor k C D).obj (ᘁX)).obj (ᘁY) := by
  simpa only [bifunctor_obj_obj, LinearTensor.leftDual_def] using!
    (Mat_.leftDual_embedding_obj (⟨X, Y⟩ : LinearTensor k C D))

/-- The evaluation of a pure object against its left dual is the one-entry matrix whose entry
is the pure tensor of the evaluations in the factors. -/
@[simp↓]
theorem evaluation_leftDual_bifunctor_obj_obj (X : C) (Y : D) :
    ε_ (ᘁ(((bifunctor k C D).obj X).obj Y)) (((bifunctor k C D).obj X).obj Y) =
      fun _ _ ↦ LinearTensor.tmul (ε_ (ᘁX) X) (ε_ (ᘁY) Y) := by
  simpa only [bifunctor_obj_obj, LinearTensor.leftDual_evaluation] using!
    (Mat_.evaluation_leftDual_embedding_obj (⟨X, Y⟩ : LinearTensor k C D))

/-- The coevaluation of a pure object with its left dual is the one-entry matrix whose entry
is the pure tensor of the coevaluations in the factors. -/
@[simp↓]
theorem coevaluation_leftDual_bifunctor_obj_obj (X : C) (Y : D) :
    η_ (ᘁ(((bifunctor k C D).obj X).obj Y)) (((bifunctor k C D).obj X).obj Y) =
      fun _ _ ↦ LinearTensor.tmul (η_ (ᘁX) X) (η_ (ᘁY) Y) := by
  simpa only [bifunctor_obj_obj, LinearTensor.leftDual_coevaluation] using!
    (Mat_.coevaluation_leftDual_embedding_obj (⟨X, Y⟩ : LinearTensor k C D))

end LeftDual

end TauCeti.DeligneProduct
