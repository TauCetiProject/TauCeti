/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Basic
public import Mathlib.Data.ZMod.Defs

/-!
# Parity words and modulo-two reduction of rigid object boundaries

In a pivotal category every object is monoidally naturally isomorphic to its double right dual,
so the integer dual-winding level recorded by `WindingWord` matters on objects only modulo two.
This file introduces `ParityWord α := List (α × ZMod 2)`, the modulo-two boundary word model,
together with `WindingWord.toParity : WindingWord α → ParityWord α` and the composite
normalization `RigidObject.normalizeParity : RigidObject α → ParityWord α`.

Whereas `WindingWord.rightDual` (`+1`) and `WindingWord.leftDual` (`-1`) have infinite order,
`ParityWord.dual` reverses ports and flips parities in `ZMod 2`; it is strictly involutive
`ParityWord.dual_dual`, and both `WindingWord.rightDual` and `WindingWord.leftDual` project to
`ParityWord.dual` under `WindingWord.toParity`. Sectioning via `{0, 1} ⊂ ℤ`
(`ParityWord.toWindingWord`, `RigidObject.ofParityWord`) proves surjectivity of both reductions.

## References

* [A. Joyal and R. Street, *Planar diagrams and tensor algebra*][joyalStreet1988]
* [P. Selinger, *A survey of graphical languages for monoidal categories*][selinger2011]
-/

public section

open scoped CategoryTheory.MonoidalCategory

namespace TauCeti

universe u

/-- An ordered boundary word whose generators carry dual-orientation parities in `ZMod 2`
(`0` for covariant/forward, `1` for contravariant/dual). -/
abbrev ParityWord (α : Type u) := List (α × ZMod 2)

namespace ParityWord

variable {α : Type u}

/-- Every parity in `ZMod 2` is either `0` or `1`. -/
theorem eq_zero_or_one : ∀ ε : ZMod 2, ε = 0 ∨ ε = 1 := by decide

private theorem zmod2_add_self : ∀ ε : ZMod 2, ε + ε = 0 := by decide

/-- Add `ε : ZMod 2` to every parity in a word without changing port order. -/
@[expose]
def shift (ε : ZMod 2) (L : ParityWord α) : ParityWord α := L.map fun p ↦ (p.1, p.2 + ε)

@[simp] theorem shift_nil (ε : ZMod 2) : shift ε ([] : ParityWord α) = [] := by rfl
@[simp] theorem shift_cons (ε : ZMod 2) (p : α × ZMod 2) (L : ParityWord α) :
    shift ε (p :: L) = (p.1, p.2 + ε) :: shift ε L := by rfl
@[simp] theorem shift_append (ε : ZMod 2) (L M : ParityWord α) :
    shift ε (L ++ M) = shift ε L ++ shift ε M := by simp [shift]
@[simp] theorem length_shift (ε : ZMod 2) (L : ParityWord α) :
    (shift ε L).length = L.length := by simp [shift]
@[simp] theorem shift_zero (L : ParityWord α) : shift 0 L = L := by simp [shift]
@[simp] theorem shift_reverse (ε : ZMod 2) (L : ParityWord α) :
    shift ε L.reverse = (shift ε L).reverse := by simp [shift]

@[simp] theorem mem_shift_iff (p : α × ZMod 2) (ε : ZMod 2) (L : ParityWord α) :
    p ∈ shift ε L ↔ (p.1, p.2 + ε) ∈ L := by
  have hsub : ∀ a b δ : ZMod 2, (a = b + δ) ↔ (a + δ = b) := by decide
  induction L with | nil => simp | cons _ _ ih => simp [ih, Prod.ext_iff, hsub]

/-- Parity shifts compose by addition in `ZMod 2`. -/
@[simp] theorem shift_shift (δ ε : ZMod 2) (L : ParityWord α) :
    shift δ (shift ε L) = shift (ε + δ) L := by
  simp [shift, List.map_map, Function.comp_def, add_assoc]

/-- Shifting twice by the same parity is the identity on `ParityWord`. -/
theorem shift_self (ε : ZMod 2) (L : ParityWord α) : shift ε (shift ε L) = L := by
  rw [shift_shift, zmod2_add_self, shift_zero]

/-- Pivotal boundary duality: reverse the port order and flip every parity in `ZMod 2`. -/
@[expose]
def dual (L : ParityWord α) : ParityWord α := shift 1 L.reverse

theorem dual_eq_shift_reverse (L : ParityWord α) : L.dual = shift 1 L.reverse := by rfl
@[simp] theorem mem_dual_iff (p : α × ZMod 2) (L : ParityWord α) :
    p ∈ L.dual ↔ (p.1, p.2 + 1) ∈ L := by simp [dual_eq_shift_reverse]
@[simp] theorem dual_nil : dual ([] : ParityWord α) = [] := by rfl
@[simp] theorem dual_cons (p : α × ZMod 2) (L : ParityWord α) :
    dual (p :: L) = dual L ++ [(p.1, p.2 + 1)] := by simp [dual, shift]
@[simp] theorem dual_append (L M : ParityWord α) :
    dual (L ++ M) = dual M ++ dual L := by simp [dual]
@[simp] theorem length_dual (L : ParityWord α) : L.dual.length = L.length := by simp [dual]
@[simp] theorem dual_shift (ε : ZMod 2) (L : ParityWord α) :
    (shift ε L).dual = shift ε L.dual := by
  simp [dual, shift, List.map_reverse, List.map_map, Function.comp_def, add_right_comm]

/-- Boundary duality on parity words is strictly involutive. -/
@[simp] theorem dual_dual (L : ParityWord α) : L.dual.dual = L := by
  rw [dual_eq_shift_reverse L.dual, dual_eq_shift_reverse L, ← shift_reverse,
    List.reverse_reverse, shift_self]

/-- `ParityWord.dual` as a self-inverse equivalence on parity words. -/
def dualEquiv : ParityWord α ≃ ParityWord α := ⟨dual, dual, dual_dual, dual_dual⟩

@[simp] theorem dualEquiv_apply (L : ParityWord α) : dualEquiv L = L.dual := by rfl
@[simp] theorem dualEquiv_symm : (dualEquiv (α := α)).symm = dualEquiv := by rfl

/-- Canonical integer representative `{0, 1} ⊂ ℤ` of a parity in `ZMod 2`. -/
def toLevel : ZMod 2 → ℤ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

@[simp] theorem toLevel_zero : toLevel 0 = 0 := by rfl
@[simp] theorem toLevel_one : toLevel 1 = 1 := by rfl
@[simp] theorem intCast_toLevel (ε : ZMod 2) : (toLevel ε : ZMod 2) = ε := by
  rcases eq_zero_or_one ε with rfl | rfl <;> rfl

/-- Embed a parity word into `WindingWord α` using dual levels in `{0, 1}`. -/
def toWindingWord (L : ParityWord α) : WindingWord α := L.map fun p ↦ (p.1, toLevel p.2)

@[simp] theorem toWindingWord_nil : toWindingWord ([] : ParityWord α) = [] := by rfl
@[simp] theorem toWindingWord_cons (p : α × ZMod 2) (L : ParityWord α) :
    toWindingWord (p :: L) = (p.1, toLevel p.2) :: toWindingWord L := by rfl
@[simp] theorem toWindingWord_append (L M : ParityWord α) :
    toWindingWord (L ++ M) = toWindingWord L ++ toWindingWord M := by simp [toWindingWord]
@[simp] theorem length_toWindingWord (L : ParityWord α) :
    L.toWindingWord.length = L.length := by simp [toWindingWord]

end ParityWord

namespace WindingWord

variable {α : Type u}

/-- Reduce every integer dual-winding level in `L : WindingWord α` modulo two. -/
@[expose]
def toParity (L : WindingWord α) : ParityWord α := L.map fun p ↦ (p.1, (p.2 : ZMod 2))

@[simp] theorem toParity_nil : toParity ([] : WindingWord α) = [] := by rfl
@[simp] theorem toParity_cons (p : α × ℤ) (L : WindingWord α) :
    toParity (p :: L) = (p.1, (p.2 : ZMod 2)) :: toParity L := by rfl
@[simp] theorem toParity_append (L M : WindingWord α) :
    toParity (L ++ M) = toParity L ++ toParity M := by simp [toParity]
@[simp] theorem length_toParity (L : WindingWord α) :
    L.toParity.length = L.length := by simp [toParity]
@[simp] theorem toParity_reverse (L : WindingWord α) :
    toParity L.reverse = L.toParity.reverse := by simp [toParity]

/-- `ParityWord.toWindingWord` is a right inverse to `WindingWord.toParity`. -/
@[simp] theorem toParity_toWindingWord (L : ParityWord α) : L.toWindingWord.toParity = L := by
  simp [toParity, ParityWord.toWindingWord, List.map_map, Function.comp_def]

/-- Modulo-two reduction from winding words to parity words is surjective. -/
theorem toParity_surjective : Function.Surjective (toParity (α := α)) :=
  fun L ↦ ⟨L.toWindingWord, toParity_toWindingWord L⟩

/-- Integer shifts descend to `ZMod 2` shifts on parity words. -/
@[simp] theorem toParity_shift (n : ℤ) (L : WindingWord α) :
    (shift n L).toParity = ParityWord.shift (n : ZMod 2) L.toParity := by
  induction L <;> simp_all

/-- Even integer level shifts vanish under modulo-two parity reduction. -/
theorem toParity_shift_two_mul (k : ℤ) (L : WindingWord α) :
    (shift (2 * k) L).toParity = L.toParity := by simp [(by decide : (2 : ZMod 2) = 0)]

/-- Right duality on winding words projects to `ParityWord.dual`. -/
@[simp] theorem toParity_rightDual (L : WindingWord α) :
    L.rightDual.toParity = L.toParity.dual := by
  simp [rightDual_eq_shift_reverse, ParityWord.dual_eq_shift_reverse]

/-- Left duality on winding words also projects to `ParityWord.dual` (`-1 = 1` in `ZMod 2`). -/
@[simp] theorem toParity_leftDual (L : WindingWord α) :
    L.leftDual.toParity = L.toParity.dual := by
  simp [leftDual_eq_shift_reverse, ParityWord.dual_eq_shift_reverse,
    (by decide : (-1 : ZMod 2) = 1)]

end WindingWord

namespace RigidObject

variable {α : Type u}

/-- Normalize `RigidObject α` directly to its `ZMod 2` parity boundary word. -/
@[expose]
def normalizeParity : RigidObject α → ParityWord α
  | .of a => [(a, 0)]
  | .unit => []
  | .tensor X Y => normalizeParity X ++ normalizeParity Y
  | .rightDual X => (normalizeParity X).dual
  | .leftDual X => (normalizeParity X).dual

@[simp] theorem normalizeParity_of (a : α) : normalizeParity (.of a) = [(a, 0)] := by rfl
@[simp] theorem normalizeParity_unit : normalizeParity (.unit : RigidObject α) = [] := by rfl
@[simp] theorem normalizeParity_tensor (X Y : RigidObject α) :
    normalizeParity (X.tensor Y) = normalizeParity X ++ normalizeParity Y := by rfl
@[simp] theorem normalizeParity_rightDual (X : RigidObject α) :
    normalizeParity X.rightDual = (normalizeParity X).dual := by rfl
@[simp] theorem normalizeParity_leftDual (X : RigidObject α) :
    normalizeParity X.leftDual = (normalizeParity X).dual := by rfl

/-- Direct parity normalization agrees with `normalize` followed by `WindingWord.toParity`. -/
theorem normalizeParity_eq_toParity_normalize (X : RigidObject α) :
    X.normalizeParity = X.normalize.toParity := by induction X <;> simp_all

/-- Unlike `RigidObject.normalize`, `RigidObject.normalizeParity` erases double right/left duals. -/
theorem normalizeParity_rightDual_rightDual (X : RigidObject α) :
    X.rightDual.rightDual.normalizeParity = X.normalizeParity := by simp
theorem normalizeParity_leftDual_leftDual (X : RigidObject α) :
    X.leftDual.leftDual.normalizeParity = X.normalizeParity := by simp

/-- Realize a generator with a `ZMod 2` parity as `.of a` or `(RigidObject.of a).rightDual`. -/
def atParity (a : α) : ZMod 2 → RigidObject α
  | ⟨0, _⟩ => .of a
  | ⟨1, _⟩ => (RigidObject.of a).rightDual

@[simp] theorem atParity_zero (a : α) : atParity a 0 = .of a := by rfl
@[simp] theorem atParity_one (a : α) : atParity a 1 = (RigidObject.of a).rightDual := by rfl

theorem atParity_eq_atLevel_toLevel (a : α) (ε : ZMod 2) :
    atParity a ε = atLevel a (ParityWord.toLevel ε) := by
  rcases ParityWord.eq_zero_or_one ε with rfl | rfl
  exacts [(atLevel_natCast a 0).symm, (atLevel_natCast a 1).symm]
@[simp] theorem normalizeParity_atParity (a : α) (ε : ZMod 2) :
    normalizeParity (atParity a ε) = [(a, ε)] := by
  rw [atParity_eq_atLevel_toLevel, normalizeParity_eq_toParity_normalize, normalize_atLevel]; simp

/-- Realize a parity word as a right-associated formal tensor product ending in `.unit`. -/
def ofParityWord : ParityWord α → RigidObject α
  | [] => .unit
  | (a, ε) :: L => (atParity a ε).tensor (ofParityWord L)

@[simp] theorem ofParityWord_nil : ofParityWord ([] : ParityWord α) = .unit := by rfl
@[simp] theorem ofParityWord_cons (a : α) (ε : ZMod 2) (L : ParityWord α) :
    ofParityWord ((a, ε) :: L) = (atParity a ε).tensor (ofParityWord L) := by rfl

theorem ofParityWord_eq_ofWord_toWindingWord (L : ParityWord α) :
    ofParityWord L = ofWord L.toWindingWord := by
  induction L with
  | nil => simp
  | cons p L ih => rcases p with ⟨a, ε⟩; simp [atParity_eq_atLevel_toLevel, ih]
@[simp] theorem normalizeParity_ofParityWord (L : ParityWord α) :
    normalizeParity (ofParityWord L) = L := by
  rw [ofParityWord_eq_ofWord_toWindingWord, normalizeParity_eq_toParity_normalize,
    normalize_ofWord, WindingWord.toParity_toWindingWord]

/-- Parity normalization reaches every finite `ZMod 2`-labelled boundary word. -/
theorem normalizeParity_surjective :
    Function.Surjective (normalizeParity : RigidObject α → ParityWord α) :=
  fun L ↦ ⟨ofParityWord L, normalizeParity_ofParityWord L⟩

end RigidObject

end TauCeti

namespace CategoryTheory.FreeMonoidalCategory

open TauCeti

variable {α : Type u}

/-- Every letter in the parity normalization of a pure monoidal object has parity `0`. -/
theorem snd_eq_zero_of_mem_normalizeParity_toRigidObject (X : FreeMonoidalCategory α) :
    ∀ p ∈ X.toRigidObject.normalizeParity, p.2 = 0 := by
  rw [RigidObject.normalizeParity_eq_toParity_normalize]
  rintro p hp; rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  simp [snd_eq_zero_of_mem_normalize_toRigidObject X q hq]

end CategoryTheory.FreeMonoidalCategory
