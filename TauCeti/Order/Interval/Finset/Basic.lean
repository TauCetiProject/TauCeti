/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Addition-fiber equivalences for `Finset.Iic`

In a canonically ordered commutative semigroup with ordered subtraction, order-reflecting addition,
and finite initial intervals, pairs `(b, c)` summing to `a` correspond bijectively to elements
`b ∈ Finset.Iic a` via `b ↦ (b, a - b)`. Summing over all `a` then reindexes the cone
`Σ a, {b // b ∈ Finset.Iic a}` by the product `α × α`, as needed for Cauchy products indexed by
`Finset.Iic` (such as multi-index power series on `ι → ℕ`).

## Main definitions

* `TauCeti.addFiberEquivIic`: equivalence
  `{p : α × α // p.1 + p.2 = a} ≃ {b : α // b ∈ Finset.Iic a}`.
* `TauCeti.sigmaIicEquivProd`: equivalence `(Σ a : α, {b : α // b ∈ Finset.Iic a}) ≃ α × α`.
-/

public section

namespace TauCeti

variable {α : Type*} [AddCommSemigroup α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] [AddLeftReflectLE α] [LocallyFiniteOrderBot α]

/-- Pairs `(b, c)` in `α × α` with `b + c = a` correspond to elements `b ∈ Finset.Iic a` via
`(b, c) ↦ b` with inverse `b ↦ (b, a - b)`. -/
def addFiberEquivIic (a : α) :
    {p : α × α // p.1 + p.2 = a} ≃ {b : α // b ∈ Finset.Iic a} where
  toFun p := ⟨p.1.1, Finset.mem_Iic.2 (le_self_add.trans_eq p.2)⟩
  invFun b := ⟨(b.1, a - b.1), add_tsub_cancel_of_le (Finset.mem_Iic.1 b.2)⟩
  left_inv := fun ⟨⟨_, _⟩, h⟩ ↦
    Subtype.ext <| Prod.ext rfl (tsub_eq_of_eq_add_rev h.symm)
  right_inv := fun ⟨_, _⟩ ↦ rfl

@[simp]
theorem coe_addFiberEquivIic_apply (a : α) (p : {p : α × α // p.1 + p.2 = a}) :
    (addFiberEquivIic a p : α) = p.1.1 := by
  rfl

@[simp]
theorem coe_addFiberEquivIic_symm_apply (a : α) (b : {b : α // b ∈ Finset.Iic a}) :
    ((addFiberEquivIic a).symm b : α × α) = (b.1, a - b.1) := by
  rfl

/-- Reindexing the Cauchy-product cone `(a, b ∈ Finset.Iic a)` by the summands `(b, a - b)`. -/
def sigmaIicEquivProd :
    (Σ a : α, {b : α // b ∈ Finset.Iic a}) ≃ α × α :=
  (Equiv.sigmaCongrRight fun a ↦ (addFiberEquivIic a).symm).trans
    (Equiv.sigmaFiberEquiv fun p : α × α ↦ p.1 + p.2)

@[simp]
theorem sigmaIicEquivProd_apply (x : Σ a : α, {b : α // b ∈ Finset.Iic a}) :
    sigmaIicEquivProd x = (x.2.1, x.1 - x.2.1) := by
  rfl

@[simp]
theorem sigmaIicEquivProd_symm_apply (p : α × α) :
    sigmaIicEquivProd.symm p = ⟨p.1 + p.2, p.1, Finset.mem_Iic.2 le_self_add⟩ := by
  rfl

end TauCeti
