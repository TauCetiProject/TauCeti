/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.ParityWord.Basic
public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Substitution
import Mathlib.Algebra.CharP.Two

/-!
# Substitution of parity words

`ParityWord.dualPow` packages the `ZMod 2`-indexed action of boundary duality (`0 ↦ id`,
`1 ↦ ParityWord.dual`), and `ParityWord.subst` splices multi-port (or empty) parity words along
`List.flatMap`. We establish its left and right unit laws (`ParityWord.subst_singleton` and
`ParityWord.subst_self`), associativity (`ParityWord.subst_subst`), compatibility with
`ParityWord.shift` and `ParityWord.dual`, and commutation with modulo-two reduction
(`WindingWord.toParity_subst` and `RigidObject.normalizeParity_subst`).

## References

* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, §2.
* P. Selinger, *A survey of graphical languages for monoidal categories*, §4.2.
-/

public section

open scoped CharTwo

namespace TauCeti

universe u v w

namespace ParityWord

variable {α : Type u} {β : Type v} {γ : Type w}

/-- `ZMod 2`-indexed iteration of boundary duality: parity `0` acts trivially and parity `1`
applies `ParityWord.dual`. -/
def dualPow : ZMod 2 → ParityWord α → ParityWord α
  | ⟨0, _⟩ => fun L ↦ L
  | ⟨1, _⟩ => dual

@[simp] theorem dualPow_zero (L : ParityWord α) : dualPow 0 L = L := (rfl)

@[simp] theorem dualPow_one (L : ParityWord α) : dualPow 1 L = L.dual := (rfl)

/-- Parity-indexed dual powers compose by addition in `ZMod 2`. -/
theorem dualPow_add (δ ε : ZMod 2) (L : ParityWord α) :
    dualPow (δ + ε) L = dualPow δ (dualPow ε L) := by
  rcases ZMod.eq_zero_or_eq_one δ with rfl | rfl <;>
    rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

/-- Applying the same `ZMod 2` dual power twice is the identity on `ParityWord`. -/
@[simp] theorem dualPow_dualPow_self (ε : ZMod 2) (L : ParityWord α) :
    dualPow ε (dualPow ε L) = L := by
  rw [← dualPow_add, CharTwo.add_self_eq_zero, dualPow_zero]

@[simp] theorem length_dualPow (ε : ZMod 2) (L : ParityWord α) :
    (dualPow ε L).length = L.length := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl <;> simp

@[simp] theorem dualPow_dual (ε : ZMod 2) (L : ParityWord α) :
    dualPow ε L.dual = (dualPow ε L).dual := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl <;> simp

@[simp] theorem dualPow_shift (ε δ : ZMod 2) (L : ParityWord α) :
    dualPow ε (shift δ L) = shift δ (dualPow ε L) := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl <;> simp

@[simp] theorem dualPow_nil (ε : ZMod 2) : dualPow ε ([] : ParityWord α) = [] := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl <;> simp

@[simp] theorem dualPow_singleton (ε : ZMod 2) (p : α × ZMod 2) :
    dualPow ε [p] = [(p.1, p.2 + ε)] := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl <;> simp

@[simp] theorem mem_dualPow_iff (p : α × ZMod 2) (ε : ZMod 2) (L : ParityWord α) :
    p ∈ dualPow ε L ↔ (p.1, p.2 + ε) ∈ L := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl <;> simp

/-- Substitute a parity word for each generator, applying `ParityWord.dualPow` according to the
parity of each port occurrence. -/
def subst (f : α → ParityWord β) (L : ParityWord α) : ParityWord β :=
  L.flatMap fun p ↦ dualPow p.2 (f p.1)

theorem subst_def (f : α → ParityWord β) (L : ParityWord α) :
    subst f L = L.flatMap fun p ↦ dualPow p.2 (f p.1) := (rfl)

@[simp] theorem mem_subst_iff (q : β × ZMod 2) (f : α → ParityWord β) (L : ParityWord α) :
    q ∈ subst f L ↔ ∃ p ∈ L, (q.1, q.2 + p.2) ∈ f p.1 := by
  simp [subst_def]

@[simp] theorem subst_nil (f : α → ParityWord β) : subst f [] = [] := (rfl)

@[simp] theorem subst_cons (f : α → ParityWord β) (p : α × ZMod 2) (L : ParityWord α) :
    subst f (p :: L) = dualPow p.2 (f p.1) ++ subst f L := (rfl)

/-- Left-unit law on a single port: substituting into `[p]` applies `dualPow p.2` to `f p.1`
(in particular `subst f [(a, 0)] = f a`). -/
theorem subst_singleton (f : α → ParityWord β) (p : α × ZMod 2) :
    subst f [p] = dualPow p.2 (f p.1) := by
  simp [subst_cons]

@[simp] theorem subst_append (f : α → ParityWord β) (L M : ParityWord α) :
    subst f (L ++ M) = subst f L ++ subst f M := by
  simp [subst]

/-- Replacing every generator by the empty parity word yields the empty parity word. -/
@[simp] theorem subst_nil_left (L : ParityWord α) :
    subst (fun _ ↦ ([] : ParityWord β)) L = [] := by
  induction L <;> simp_all

/-- Shifting every replacing word shifts the substituted boundary without reversing ports. -/
@[simp] theorem subst_shift_left (f : α → ParityWord β) (ε : ZMod 2) (L : ParityWord α) :
    subst (fun a ↦ shift ε (f a)) L = shift ε (subst f L) := by
  induction L <;> simp_all

/-- Shifting the input parities transports each replacing word by `dualPow`. -/
@[simp] theorem subst_shift (f : α → ParityWord β) (ε : ZMod 2) (L : ParityWord α) :
    subst f (shift ε L) = subst (fun a ↦ dualPow ε (f a)) L := by
  induction L with
  | nil => simp
  | cons _ _ ih => simp [ih, dualPow_add]

/-- Substitution commutes with `ParityWord.dual`, reversing multi-port replacements. -/
@[simp] theorem subst_dual (f : α → ParityWord β) (L : ParityWord α) :
    subst f L.dual = (subst f L).dual := by
  induction L with
  | nil => simp
  | cons p _ ih => rcases p with ⟨a, ε⟩; simp [ih, dualPow_add]

@[simp] theorem subst_dualPow (f : α → ParityWord β) (ε : ZMod 2) (L : ParityWord α) :
    subst f (dualPow ε L) = dualPow ε (subst f L) := by
  rcases ZMod.eq_zero_or_eq_one ε with rfl | rfl <;> simp

/-- Parity word substitution is associative. -/
@[simp] theorem subst_subst (g : β → ParityWord γ) (f : α → ParityWord β) (L : ParityWord α) :
    subst g (subst f L) = subst (fun a ↦ subst g (f a)) L := by
  induction L with
  | nil => simp
  | cons p _ ih => rcases p with ⟨a, ε⟩; simp [ih]

/-- Replacing each generator by its single port at parity `ε` shifts the boundary by `ε`. -/
@[simp] theorem subst_singleton_left (ε : ZMod 2) (L : ParityWord α) :
    subst (fun a ↦ [(a, ε)]) L = shift ε L := by
  induction L with
  | nil => simp
  | cons _ _ ih => simp [ih, add_comm]

/-- Right-identity law for parity word substitution: replacing each generator `a` by its single
port `(a, 0)` leaves every parity word unchanged. -/
theorem subst_self (L : ParityWord α) : subst (fun a ↦ [(a, 0)]) L = L := by
  simp

end ParityWord

namespace WindingWord

variable {α : Type u} {β : Type v}

/-- Modulo-two reduction intertwines integer `WindingWord.dualPow` with `ParityWord.dualPow`. -/
@[simp] theorem toParity_dualPow (n : ℤ) (L : WindingWord α) :
    (dualPow n L).toParity = ParityWord.dualPow (n : ZMod 2) L.toParity := by
  induction n using Int.induction_on with
  | zero => simp
  | succ _ ih => simp [ih, add_comm _ (1 : ZMod 2), ParityWord.dualPow_add]
  | pred _ ih => simp [ih, add_comm _ (1 : ZMod 2), ParityWord.dualPow_add]

/-- Modulo-two reduction commutes with boundary word substitution. -/
@[simp] theorem toParity_subst (f : α → WindingWord β) (L : WindingWord α) :
    (subst f L).toParity = ParityWord.subst (fun a ↦ (f a).toParity) L.toParity := by
  induction L <;> simp_all

end WindingWord

namespace RigidObject

variable {α : Type u} {β : Type v}

/-- Direct parity normalization commutes with substitution of formal rigid objects. -/
@[simp] theorem normalizeParity_subst (f : α → RigidObject β) (X : RigidObject α) :
    normalizeParity (subst f X) =
      ParityWord.subst (fun a ↦ normalizeParity (f a)) (normalizeParity X) := by
  simp [normalizeParity_eq_toParity_normalize]

end RigidObject

end TauCeti
