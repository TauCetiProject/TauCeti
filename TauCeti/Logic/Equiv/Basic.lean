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

/-- The transposition of two points of a linear order, written with the smaller point first. -/
theorem swap_min_max {α : Type*} [LinearOrder α] (a b : α) :
    swap (min a b) (max a b) = swap a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, swap_comm]

end Equiv
