/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Basic

/-!
# Commuting two subtype restrictions

Restricting a type `E` first to the elements satisfying `p` and then to those satisfying `q`
leaves the same elements as restricting in the opposite order. When the second predicate in each
order is stated on the subtype, rather than on `E`, this is the equivalence
`Equiv.subtypeSubtypeComm`; it identifies, for instance, the edges left after deleting two vertices
of a graph one after the other, in either order.
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

end Equiv
