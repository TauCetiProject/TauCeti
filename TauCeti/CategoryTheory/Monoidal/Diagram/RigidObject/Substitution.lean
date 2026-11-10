/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Basic
public import Mathlib.Algebra.Group.End

/-!
# Substitution of winding words

A generator in a rigid boundary can be replaced by an arbitrary boundary word, including the
empty word. At level `n`, the replacing word must first undergo `n` right duals (negative `n`
means left duals). Odd levels reverse the replacing ports, while even levels retain their
order; the integer levels themselves are never reduced modulo two.

`WindingWord.subst` implements this operation. It commutes with both duals, has associative
composition and a two-sided unit, and `RigidObject.normalize_subst` identifies it with
substitution before normalization of formal rigid objects. Consequently normalization equality
is preserved by object substitution, without imposing a pivotal identification.

The winding convention follows Joyal and Street, *Planar diagrams and tensor algebra*, §2.
The integer iteration reuses powers in Mathlib's permutation group.
-/

public section

namespace TauCeti

universe u v w

namespace WindingWord

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Integer iteration of right duality. Negative powers use left duality, its inverse. -/
def dualPow (n : ℤ) (L : WindingWord α) : WindingWord α := (rightDualEquiv ^ n) L

@[simp] theorem dualPow_zero (L : WindingWord α) : dualPow 0 L = L := by
  simp [dualPow]

/-- Integer dual iterations compose by addition, retaining the full winding level. -/
theorem dualPow_add (m n : ℤ) (L : WindingWord α) :
    dualPow (m + n) L = dualPow m (dualPow n L) := by
  simp [dualPow, zpow_add, Equiv.Perm.mul_apply]

@[simp] theorem dualPow_one (L : WindingWord α) : dualPow 1 L = L.rightDual := by
  simp [dualPow]

@[simp] theorem dualPow_neg_one (L : WindingWord α) : dualPow (-1) L = L.leftDual := by
  simp [dualPow]

@[simp] theorem dualPow_add_one (n : ℤ) (L : WindingWord α) :
    dualPow (n + 1) L = (dualPow n L).rightDual := by
  rw [add_comm n 1, dualPow_add, dualPow_one]

@[simp] theorem dualPow_sub_one (n : ℤ) (L : WindingWord α) :
    dualPow (n - 1) L = (dualPow n L).leftDual := by
  rw [sub_eq_add_neg, add_comm n (-1), dualPow_add, dualPow_neg_one]

@[simp] theorem length_dualPow (n : ℤ) (L : WindingWord α) :
    (dualPow n L).length = L.length := by
  induction n using Int.induction_on <;> simp_all

@[simp] theorem dualPow_rightDual (n : ℤ) (L : WindingWord α) :
    dualPow n L.rightDual = (dualPow n L).rightDual := by
  rw [← dualPow_one L, ← dualPow_add, add_comm n 1, dualPow_add, dualPow_one]

@[simp] theorem dualPow_leftDual (n : ℤ) (L : WindingWord α) :
    dualPow n L.leftDual = (dualPow n L).leftDual := by
  rw [← dualPow_neg_one L, ← dualPow_add, add_comm n (-1), dualPow_add, dualPow_neg_one]

@[simp] theorem dualPow_shift (n k : ℤ) (L : WindingWord α) :
    dualPow n (shift k L) = shift k (dualPow n L) := by
  induction n using Int.induction_on <;> simp_all

/-- An even number of duals preserves port order and shifts every integer level. -/
@[simp] theorem dualPow_two_mul (k : ℤ) (L : WindingWord α) :
    dualPow (2 * k) L = shift (2 * k) L := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h : 2 * ((k : ℤ) + 1) = (2 * k + 1) + 1 := by omega
    simp only [h, dualPow_add_one, ih, rightDual_rightDual, shift_shift]
    exact congrArg (fun n ↦ shift n L) (by omega)
  | pred k ih =>
    have h : 2 * (-(k : ℤ) - 1) = (2 * -k - 1) - 1 := by omega
    simp only [h, dualPow_sub_one, ih, leftDual_leftDual, shift_shift]
    exact congrArg (fun n ↦ shift n L) (by omega)

@[simp] theorem dualPow_nil (n : ℤ) : dualPow n ([] : WindingWord α) = [] := by
  induction n using Int.induction_on <;> simp_all

/-- Dual iteration of a single port adds to its level, with no parity reduction. -/
@[simp] theorem dualPow_singleton (n : ℤ) (a : α) (m : ℤ) :
    dualPow n [(a, m)] = [(a, m + n)] := by
  induction n using Int.induction_on <;> simp_all <;> simp [sub_eq_add_neg, add_assoc]

/-- Substitute a word for each generator, transporting it through the integer dual level
of each occurrence. This may replace one port by many ports, or by no ports. -/
def subst (f : α → WindingWord β) (L : WindingWord α) : WindingWord β :=
  L.flatMap fun p ↦ dualPow p.2 (f p.1)

@[simp] theorem subst_nil (f : α → WindingWord β) : subst f [] = [] := by rfl

@[simp] theorem subst_cons (f : α → WindingWord β) (a : α) (n : ℤ) (L : WindingWord α) :
    subst f ((a, n) :: L) = dualPow n (f a) ++ subst f L := by rfl

@[simp] theorem subst_append (f : α → WindingWord β) (L M : WindingWord α) :
    subst f (L ++ M) = subst f L ++ subst f M := by
  simp [subst]

/-- Substitution respects right duality, including reversal of all replacing ports. -/
@[simp] theorem subst_rightDual (f : α → WindingWord β) (L : WindingWord α) :
    subst f L.rightDual = (subst f L).rightDual := by
  induction L with
  | nil => simp
  | cons p L ih => rcases p with ⟨a, n⟩; simp [ih]

/-- Substitution also respects left duality. -/
@[simp] theorem subst_leftDual (f : α → WindingWord β) (L : WindingWord α) :
    subst f L.leftDual = (subst f L).leftDual := by
  induction L with
  | nil => simp
  | cons p L ih => rcases p with ⟨a, n⟩; simp [ih]

/-- All integer iterates of duality commute with substitution. -/
@[simp] theorem subst_dualPow (f : α → WindingWord β) (n : ℤ) (L : WindingWord α) :
    subst f (dualPow n L) = dualPow n (subst f L) := by
  induction n using Int.induction_on <;> simp_all

/-- Substituting words successively agrees with substituting their composites. -/
@[simp] theorem subst_subst (g : β → WindingWord γ) (f : α → WindingWord β)
    (L : WindingWord α) : subst g (subst f L) = subst (fun a ↦ subst g (f a)) L := by
  induction L with
  | nil => simp
  | cons p L ih => rcases p with ⟨a, n⟩; simp [ih]

/-- A level-zero single port is the identity substitution. -/
@[simp] theorem subst_self (L : WindingWord α) : subst (fun a ↦ [(a, 0)]) L = L := by
  induction L with
  | nil => simp
  | cons p L ih => rcases p with ⟨a, n⟩; simp [ih]

end WindingWord

namespace RigidObject

variable {α : Type u} {β : Type v}

/-- Normalization commutes with replacement of generators by arbitrary rigid objects. The
right-hand side substitutes whole boundary words, not independent atoms for tensor products. -/
@[simp] theorem normalize_subst (f : α → RigidObject β) (X : RigidObject α) :
    normalize (subst f X) = WindingWord.subst (fun a ↦ normalize (f a)) (normalize X) := by
  induction X <;> simp_all

/-- An equality of normalized boundaries remains valid after any object substitution. -/
theorem normalize_subst_eq (f : α → RigidObject β) {X Y : RigidObject α}
    (h : normalize X = normalize Y) : normalize (subst f X) = normalize (subst f Y) := by
  simp [h]

end RigidObject

end TauCeti
