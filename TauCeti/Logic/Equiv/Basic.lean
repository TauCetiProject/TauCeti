/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Commuting two subtype restrictions

Restricting a type `E` first to the elements satisfying `p` and then to those satisfying `q`
leaves the same elements as restricting in the opposite order. When the second predicate in each
order is stated on the subtype, rather than on `E`, this is the equivalence
`Equiv.subtypeSubtypeComm`; it identifies, for instance, the edges left after deleting two vertices
of a graph one after the other, in either order.

A function `f : α → β` with `f i = f j` at two distinct points is determined by its values away
from `j`, since its value at `j` is its value at `i`. The equivalence
`Equiv.subtypeApplyEqApplyEquivFun` restricts such functions to `{a // a ≠ j}`; it counts the
functions identifying two given points, as in collision bounds for uniform sampling.

The file also records that the transposition of two points of a linear order is the transposition
of their minimum and maximum (`Equiv.swap_min_max`).
-/

public section

namespace Equiv

/-- Removing the elements failing `p` and then those failing `q` leaves the same elements as
removing them in the opposite order. The predicates `q'` on `Subtype p` and `p'` on `Subtype q`
are the restrictions of `q` and `p`. -/
def subtypeSubtypeComm {E : Type*} {p q : E → Prop} {p' : Subtype q → Prop}
    {q' : Subtype p → Prop} (hp : ∀ e he, p' ⟨e, he⟩ ↔ p e) (hq : ∀ e he, q' ⟨e, he⟩ ↔ q e) :
    {e : Subtype p // q' e} ≃ {e : Subtype q // p' e} :=
  (subtypeSubtypeEquivSubtypeExists p q').trans <|
    (subtypeEquivRight fun e ↦
      ⟨fun ⟨hpe, hqe⟩ ↦ ⟨(hq e hpe).mp hqe, (hp e _).mpr hpe⟩,
        fun ⟨hqe, hpe⟩ ↦ ⟨(hp e hqe).mp hpe, (hq e _).mpr hqe⟩⟩).trans
      (subtypeSubtypeEquivSubtypeExists q p').symm

/-- `Equiv.subtypeSubtypeComm` does not move the underlying element of `E`. -/
@[simp]
theorem coe_coe_subtypeSubtypeComm_apply {E : Type*} {p q : E → Prop} {p' : Subtype q → Prop}
    {q' : Subtype p → Prop} (hp : ∀ e he, p' ⟨e, he⟩ ↔ p e) (hq : ∀ e he, q' ⟨e, he⟩ ↔ q e)
    (e : {e : Subtype p // q' e}) : ((subtypeSubtypeComm hp hq e : Subtype q) : E) = e.1.1 :=
  (rfl)

/-- The inverse of `Equiv.subtypeSubtypeComm` does not move the underlying element of `E`. -/
@[simp]
theorem coe_coe_subtypeSubtypeComm_symm_apply {E : Type*} {p q : E → Prop}
    {p' : Subtype q → Prop} {q' : Subtype p → Prop} (hp : ∀ e he, p' ⟨e, he⟩ ↔ p e)
    (hq : ∀ e he, q' ⟨e, he⟩ ↔ q e) (e : {e : Subtype q // p' e}) :
    (((subtypeSubtypeComm hp hq).symm e : Subtype p) : E) = e.1.1 :=
  (rfl)

section subtypeApplyEqApplyEquivFun

variable {α β : Sort*} [DecidableEq α] {i j : α}

/-- The functions `f : α → β` with `f i = f j` at two distinct points `i` and `j` are equivalent to
the functions on `{a // a ≠ j}`: such an `f` is restricted to the points other than `j`, and a
function `g` on them is extended by its value at `i`. -/
def subtypeApplyEqApplyEquivFun (hij : i ≠ j) :
    {f : α → β // f i = f j} ≃ ({a // a ≠ j} → β) where
  toFun f a := f.1 a
  invFun g := ⟨fun a ↦ if ha : a = j then g ⟨i, hij⟩ else g ⟨a, ha⟩, by simp [hij]⟩
  left_inv := fun ⟨f, (hf : f i = f j)⟩ ↦ by
    ext a
    by_cases ha : a = j <;> simp [ha, hf]
  right_inv g := by
    funext a
    simp [a.2]

/-- `Equiv.subtypeApplyEqApplyEquivFun` restricts a function to the points other than `j`. -/
@[simp]
theorem subtypeApplyEqApplyEquivFun_apply (hij : i ≠ j) (f : {f : α → β // f i = f j})
    (a : {a // a ≠ j}) : subtypeApplyEqApplyEquivFun hij f a = f.1 a :=
  (rfl)

/-- The inverse of `Equiv.subtypeApplyEqApplyEquivFun` extends a function on the points other
than `j` by its value at `i`. -/
@[simp]
theorem coe_subtypeApplyEqApplyEquivFun_symm_apply (hij : i ≠ j) (g : {a // a ≠ j} → β) (a : α) :
    ((subtypeApplyEqApplyEquivFun hij).symm g : α → β) a =
      if ha : a = j then g ⟨i, hij⟩ else g ⟨a, ha⟩ :=
  (rfl)

end subtypeApplyEqApplyEquivFun

/-- The transposition of two points of a linear order, written with the smaller point first. -/
theorem swap_min_max {α : Type*} [LinearOrder α] (a b : α) :
    swap (min a b) (max a b) = swap a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, swap_comm]

end Equiv
