/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.List.Basic

/-!
# Rigid object expressions and winding words

`RigidObject` is the object syntax with tensor, unit and two formal dual operations.
Its normalization `RigidObject.normalize` takes values in `WindingWord`: finite ordered
words of generators with integer dual levels. Right duality reverses order and adds one;
left duality reverses order and subtracts one. Mixed duals cancel on words, whereas two
right duals shift every level by two. In particular, normalization does not install a
pivotal identification.

`RigidObject.ofWord` realizes every winding word by an expression, and
`RigidObject.normalize_ofWord` proves that normalization is surjective. These are
combinatorial object constructions, not categorical comparison isomorphisms or a
coherence theorem. `CategoryTheory.FreeMonoidalCategory.toRigidObject` includes Mathlib's
structural object syntax.

The integer-level convention is that of Joyal and Street, *Planar diagrams and tensor
algebra*, §2: the right dual of a letter at level n is at level n + 1.
-/

public section

open scoped CategoryTheory.MonoidalCategory

namespace TauCeti

universe u v w

/-- An ordered boundary word, with an integer iterated-dual level on each generator. -/
abbrev WindingWord (α : Type u) := List (α × ℤ)

namespace WindingWord

variable {α : Type u}

/-- Add the same integer to every dual level, without changing the order of the ports. -/
def shift (n : ℤ) (L : WindingWord α) : WindingWord α :=
  L.map fun p ↦ (p.1, p.2 + n)

@[simp] theorem shift_nil (n : ℤ) : shift n ([] : WindingWord α) = [] := by rfl

@[simp] theorem shift_cons (n : ℤ) (p : α × ℤ) (L : WindingWord α) :
    shift n (p :: L) = (p.1, p.2 + n) :: shift n L := by rfl

@[simp] theorem shift_append (n : ℤ) (L M : WindingWord α) :
    shift n (L ++ M) = shift n L ++ shift n M := by simp [shift]

@[simp] theorem length_shift (n : ℤ) (L : WindingWord α) : (shift n L).length = L.length := by
  simp [shift]

@[simp] theorem shift_zero (L : WindingWord α) : shift 0 L = L := by simp [shift]

/-- Shifts compose by addition, without reducing levels modulo two. -/
@[simp] theorem shift_shift (m n : ℤ) (L : WindingWord α) :
    shift m (shift n L) = shift (n + m) L := by
  simp [shift, List.map_map, Function.comp_def, add_assoc]

@[simp] theorem shift_reverse (n : ℤ) (L : WindingWord α) :
    shift n L.reverse = (shift n L).reverse := by
  simp [shift]

/-- The boundary of the chosen right dual: reverse the ports and increase their levels. -/
def rightDual (L : WindingWord α) : WindingWord α := shift 1 L.reverse

/-- The boundary of the chosen left dual: reverse the ports and decrease their levels. -/
def leftDual (L : WindingWord α) : WindingWord α := shift (-1) L.reverse

theorem rightDual_eq_shift_reverse (L : WindingWord α) :
    L.rightDual = shift 1 L.reverse := by rfl

theorem leftDual_eq_shift_reverse (L : WindingWord α) :
    L.leftDual = shift (-1) L.reverse := by rfl

@[simp] theorem rightDual_shift (n : ℤ) (L : WindingWord α) :
    (shift n L).rightDual = shift n L.rightDual := by
  simp [rightDual, shift, List.map_reverse, List.map_map, Function.comp_def, add_right_comm]

@[simp] theorem leftDual_shift (n : ℤ) (L : WindingWord α) :
    (shift n L).leftDual = shift n L.leftDual := by
  simp [leftDual, shift, List.map_reverse, List.map_map, Function.comp_def, add_right_comm]

@[simp] theorem rightDual_nil : rightDual ([] : WindingWord α) = [] := by rfl

@[simp] theorem leftDual_nil : leftDual ([] : WindingWord α) = [] := by rfl

@[simp] theorem rightDual_cons (p : α × ℤ) (L : WindingWord α) :
    rightDual (p :: L) = rightDual L ++ [(p.1, p.2 + 1)] := by
  simp [rightDual, shift]

@[simp] theorem leftDual_cons (p : α × ℤ) (L : WindingWord α) :
    leftDual (p :: L) = leftDual L ++ [(p.1, p.2 - 1)] := by
  simp [leftDual, shift, sub_eq_add_neg]

@[simp] theorem rightDual_append (L M : WindingWord α) :
    rightDual (L ++ M) = rightDual M ++ rightDual L := by
  simp [rightDual]

@[simp] theorem leftDual_append (L M : WindingWord α) :
    leftDual (L ++ M) = leftDual M ++ leftDual L := by
  simp [leftDual]

@[simp] theorem length_rightDual (L : WindingWord α) : L.rightDual.length = L.length := by
  simp [rightDual, shift]

@[simp] theorem length_leftDual (L : WindingWord α) : L.leftDual.length = L.length := by
  simp [leftDual, shift]

@[simp] theorem leftDual_rightDual (L : WindingWord α) : L.rightDual.leftDual = L := by
  simp [leftDual, rightDual, shift, List.map_reverse, List.map_map, Function.comp_def]

@[simp] theorem rightDual_leftDual (L : WindingWord α) : L.leftDual.rightDual = L := by
  simp [leftDual, rightDual, shift, List.map_reverse, List.map_map, Function.comp_def]

/-- Two right duals preserve port order and increase every level by two. -/
theorem rightDual_rightDual (L : WindingWord α) : L.rightDual.rightDual = shift 2 L := by
  simp [rightDual, shift, List.map_reverse, List.map_map, Function.comp_def, add_assoc]

/-- Two left duals preserve port order and decrease every level by two. -/
theorem leftDual_leftDual (L : WindingWord α) : L.leftDual.leftDual = shift (-2) L := by
  simp [leftDual, shift, List.map_reverse, List.map_map, Function.comp_def, add_assoc]

/-- Right duality is a bijection of boundary words, with left duality as inverse. -/
def rightDualEquiv : WindingWord α ≃ WindingWord α where
  toFun := rightDual
  invFun := leftDual
  left_inv := leftDual_rightDual
  right_inv := rightDual_leftDual

@[simp] theorem rightDualEquiv_apply (L : WindingWord α) : rightDualEquiv L = L.rightDual := by rfl

@[simp] theorem rightDualEquiv_symm_apply (L : WindingWord α) :
    rightDualEquiv.symm L = L.leftDual := by rfl

end WindingWord

/-- Formal rigid objects on generators `α`. Neither mixed-dual cancellation nor any
pivotal identification is an equality of raw expressions. -/
inductive RigidObject (α : Type u)
  | of (a : α)
  | unit
  | tensor (X Y : RigidObject α)
  | rightDual (X : RigidObject α)
  | leftDual (X : RigidObject α)
  deriving DecidableEq

namespace RigidObject

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Normalize a formal object to its ordered, integer-labelled boundary. -/
def normalize : RigidObject α → WindingWord α
  | .of a => [(a, 0)]
  | .unit => []
  | .tensor X Y => normalize X ++ normalize Y
  | .rightDual X => (normalize X).rightDual
  | .leftDual X => (normalize X).leftDual

@[simp] theorem normalize_of (a : α) : normalize (.of a) = [(a, 0)] := by rfl

@[simp] theorem normalize_unit : normalize (.unit : RigidObject α) = [] := by rfl

@[simp] theorem normalize_tensor (X Y : RigidObject α) :
    normalize (X.tensor Y) = normalize X ++ normalize Y := by rfl

@[simp] theorem normalize_rightDual (X : RigidObject α) :
    normalize X.rightDual = (normalize X).rightDual := by rfl

@[simp] theorem normalize_leftDual (X : RigidObject α) :
    normalize X.leftDual = (normalize X).leftDual := by rfl

/-- Replace each generating object by an arbitrary formal rigid object. -/
def subst (f : α → RigidObject β) : RigidObject α → RigidObject β
  | .of a => f a
  | .unit => .unit
  | .tensor X Y => (subst f X).tensor (subst f Y)
  | .rightDual X => (subst f X).rightDual
  | .leftDual X => (subst f X).leftDual

@[simp] theorem subst_of (f : α → RigidObject β) (a : α) : subst f (.of a) = f a := by rfl

@[simp] theorem subst_unit (f : α → RigidObject β) : subst f .unit = .unit := by rfl

@[simp] theorem subst_tensor (f : α → RigidObject β) (X Y : RigidObject α) :
    subst f (X.tensor Y) = (subst f X).tensor (subst f Y) := by rfl

@[simp] theorem subst_rightDual (f : α → RigidObject β) (X : RigidObject α) :
    subst f X.rightDual = (subst f X).rightDual := by rfl

@[simp] theorem subst_leftDual (f : α → RigidObject β) (X : RigidObject α) :
    subst f X.leftDual = (subst f X).leftDual := by rfl

/-- Substitution of expressions is associative. -/
@[simp] theorem subst_subst (g : β → RigidObject γ) (f : α → RigidObject β)
    (X : RigidObject α) : subst g (subst f X) = subst (fun a ↦ subst g (f a)) X := by
  induction X <;> simp_all

/-- The generating-object inclusion is the identity substitution. -/
@[simp] theorem subst_self (X : RigidObject α) : subst of X = X := by
  induction X <;> simp_all

end RigidObject

end TauCeti

namespace CategoryTheory.FreeMonoidalCategory

open TauCeti (RigidObject)

variable {α : Type u}

/-- Include Mathlib's parenthesized monoidal objects into the rigid object syntax. -/
def toRigidObject : FreeMonoidalCategory α → RigidObject α
  | .of a => .of a
  | .unit => .unit
  | .tensor X Y => (toRigidObject X).tensor (toRigidObject Y)

@[simp] theorem toRigidObject_of (a : α) : toRigidObject (.of a) = .of a := by rfl

@[simp] theorem toRigidObject_unit :
    toRigidObject (𝟙_ (FreeMonoidalCategory α)) = .unit := by rfl

@[simp] theorem toRigidObject_tensor (X Y : FreeMonoidalCategory α) :
    toRigidObject (X ⊗ Y) = (toRigidObject X).tensor (toRigidObject Y) := by rfl

/-- The inclusion of monoidal object expressions preserves their raw syntax faithfully. -/
theorem toRigidObject_injective : Function.Injective (toRigidObject (α := α)) := by
  intro X Y h
  induction X generalizing Y with
  | of a => cases Y <;> simp_all [toRigidObject]
  | unit => cases Y <;> simp_all [toRigidObject]
  | tensor X Z ihX ihZ =>
    cases Y with
    | of a => cases h
    | unit => cases h
    | tensor Y W =>
      exact congrArg₂ FreeMonoidalCategory.tensor
        (ihX (RigidObject.tensor.inj h).1) (ihZ (RigidObject.tensor.inj h).2)

/-- Every letter in the normalization of a monoidal object has dual level zero. -/
theorem snd_eq_zero_of_mem_normalize_toRigidObject (X : FreeMonoidalCategory α) :
    ∀ p ∈ RigidObject.normalize X.toRigidObject, p.2 = 0 := by
  induction X <;> simp_all [toRigidObject]
  aesop

end CategoryTheory.FreeMonoidalCategory

namespace TauCeti

namespace RigidObject

variable {α : Type u}

/-- An atom at an integer level, expressed using only the two formal dual constructors. -/
def atLevel (a : α) : ℤ → RigidObject α
  | .ofNat n => rightDual^[n] (.of a)
  | .negSucc n => leftDual^[n + 1] (.of a)

@[simp] theorem atLevel_natCast (a : α) (n : ℕ) :
    atLevel a (n : ℤ) = rightDual^[n] (.of a) := by rfl

@[simp] theorem atLevel_negSucc (a : α) (n : ℕ) :
    atLevel a (.negSucc n) = leftDual^[n + 1] (.of a) := by rfl

private theorem normalize_rightDual_iterate (a : α) (n : ℕ) :
    normalize (rightDual^[n] (.of a)) = [(a, (n : ℤ))] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ih]

private theorem normalize_leftDual_iterate (a : α) (n : ℕ) :
    normalize (leftDual^[n] (.of a)) = [(a, -(n : ℤ))] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ih, sub_eq_add_neg, add_comm]

/-- The level of a realized atom is exactly the specified integer, not its parity. -/
@[simp] theorem normalize_atLevel (a : α) (n : ℤ) : normalize (atLevel a n) = [(a, n)] := by
  cases n with
  | ofNat n => exact normalize_rightDual_iterate a n
  | negSucc n =>
    rw [atLevel_negSucc, normalize_leftDual_iterate]
    simp only [Int.natCast_add, Int.natCast_one, Int.negSucc_eq]

/-- Realize a word by a right-associated tensor of its levelled atoms, ending in the unit. -/
def ofWord : WindingWord α → RigidObject α
  | [] => .unit
  | (a, n) :: L => (atLevel a n).tensor (ofWord L)

@[simp] theorem ofWord_nil : ofWord ([] : WindingWord α) = .unit := by rfl

@[simp] theorem ofWord_cons (a : α) (n : ℤ) (L : WindingWord α) :
    ofWord ((a, n) :: L) = (atLevel a n).tensor (ofWord L) := by rfl

/-- Every winding word is the normalization of its canonical realizing expression. -/
@[simp] theorem normalize_ofWord (L : WindingWord α) : normalize (ofWord L) = L := by
  induction L with
  | nil => rfl
  | cons p L ih => rcases p with ⟨a, n⟩; simp [ih]

/-- Normalization reaches every finite integer-labelled boundary. -/
theorem normalize_surjective : Function.Surjective (normalize : RigidObject α → WindingWord α) :=
  fun L ↦ ⟨ofWord L, normalize_ofWord L⟩

/-- Double right duality of a generator is not erased by normalization. -/
theorem normalize_rightDual_rightDual_ne (a : α) :
    normalize (RigidObject.of a).rightDual.rightDual ≠ normalize (.of a) := by
  simp

end RigidObject

end TauCeti
