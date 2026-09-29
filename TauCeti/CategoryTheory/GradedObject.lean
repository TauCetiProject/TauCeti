/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.GradedObject.Single
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Additive structures on graded objects

This file equips Mathlib's canonical category `CategoryTheory.GradedObject β C` with the
pointwise preadditive, linear, and abelian structures inherited from `C`. It also records that
the canonical reindexing and shift functors are additive and linear.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe w v u t

variable {C : Type u} [Category.{v} C]

/-- Pointwise addition of morphisms of graded objects. -/
instance gradedObjectHomAdd (β : Type w) [Preadditive C] (X Y : GradedObject β C) :
    Add (X ⟶ Y) :=
  ⟨fun f g i => f i + g i⟩

/-- Pointwise negation of morphisms of graded objects. -/
instance gradedObjectHomNeg (β : Type w) [Preadditive C] (X Y : GradedObject β C) :
    Neg (X ⟶ Y) :=
  ⟨fun f i => -f i⟩

/-- The pointwise preadditive structure on Mathlib's category of graded objects. -/
instance gradedObjectPreadditive (β : Type w) [Preadditive C] :
    Preadditive (GradedObject β C) where
  homGroup X Y := by
    change AddCommGroup (∀ i, X i ⟶ Y i)
    infer_instance
  add_comp := by intros; funext i; apply add_comp
  comp_add := by intros; funext i; apply comp_add

/-- The pointwise linear structure on Mathlib's category of graded objects. -/
instance gradedObjectLinear (β : Type w) (R : Type t) [Semiring R] [Preadditive C] [Linear R C] :
    Linear R (GradedObject β C) where
  homModule X Y := by
    change Module R (∀ i, X i ⟶ Y i)
    infer_instance
  smul_comp := by intros; funext i; apply Linear.smul_comp
  comp_smul := by intros; funext i; apply Linear.comp_smul

/-- Reindexing a graded object is additive. -/
instance gradedObjectComapAdditive {I J : Type*} [Preadditive C] (f : J → I) :
    (GradedObject.comap C f).Additive where
  map_add {X Y} {f₁ f₂} := by
    funext j
    change f₁ (f j) + f₂ (f j) = f₁ (f j) + f₂ (f j)
    rfl

/-- Reindexing a graded object is linear. -/
instance gradedObjectComapLinear {I J : Type*} [Preadditive C]
    (R : Type t) [Semiring R] [Linear R C] (f : J → I) :
    (GradedObject.comap C f).Linear R where
  map_smul {X Y} f₁ r := by
    funext j
    change r • f₁ (f j) = r • f₁ (f j)
    rfl

/-- Mathlib's canonical shift functor on graded objects is additive. -/
instance gradedObjectShiftFunctorAdditive {β : Type*} [AddCommGroup β] [Preadditive C]
    (s : β) (n : ℤ) : (shiftFunctor (GradedObjectWithShift s C) n).Additive where
  map_add {X Y} {f₁ f₂} := by
    funext j
    change f₁ (j + n • s) + f₂ (j + n • s) =
      f₁ (j + n • s) + f₂ (j + n • s)
    rfl

/-- Mathlib's canonical shift functor on graded objects is linear. -/
instance gradedObjectShiftFunctorLinear {β : Type*} [AddCommGroup β] [Preadditive C]
    (R : Type t) [Semiring R] [Linear R C] (s : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).Linear R where
  map_smul {X Y} f₁ r := by
    funext j
    change r • f₁ (j + n • s) = r • f₁ (j + n • s)
    rfl

instance gradedObjectShiftEquivFunctorAdditive {β : Type*} [AddCommGroup β] [Preadditive C]
    (s : β) (n : ℤ) : (shiftEquiv (GradedObjectWithShift s C) n).functor.Additive :=
  gradedObjectShiftFunctorAdditive s n

instance gradedObjectShiftEquivFunctorLinear {β : Type*} [AddCommGroup β] [Preadditive C]
    (R : Type t) [Semiring R] [Linear R C] (s : β) (n : ℤ) :
    (shiftEquiv (GradedObjectWithShift s C) n).functor.Linear R :=
  gradedObjectShiftFunctorLinear R s n

noncomputable instance gradedObjectHasFiniteLimits (β : Type w) [Abelian C] :
    HasFiniteLimits (GradedObject β C) := by
  let _ : Preadditive (β → C) := gradedObjectPreadditive β
  exact ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence
    (piEquivalenceFunctorDiscrete β C).functor⟩

/-- The pointwise abelian structure on Mathlib's category of graded objects. -/
noncomputable instance gradedObjectAbelian (β : Type w) [Abelian C] :
    Abelian (GradedObject β C) := by
  let _ : Preadditive (β → C) := gradedObjectPreadditive β
  exact abelianOfEquivalence (piEquivalenceFunctorDiscrete β C).functor

noncomputable instance gradedObjectWithShiftAbelian {β : Type w} [AddCommGroup β]
    (s : β) [Abelian C] : Abelian (GradedObjectWithShift s C) :=
  gradedObjectAbelian β

end TauCeti
