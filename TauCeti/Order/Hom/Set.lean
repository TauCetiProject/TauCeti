/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Set

/-!
# Order isomorphisms on subsets and dual preimages

`OrderIso.Iic` restricts an order isomorphism `e : α ≃o β` to the interval below a point,
`Set.Iic x ≃o Set.Iic (e x)`. It is built as a structure instance, so an application of it does
not rewrite on its own: a consumer that meets `(e.Iic x) y` in a goal has to unfold the
construction to get anywhere. The evaluation lemmas `OrderIso.Iic_apply_coe` and
`OrderIso.Iic_symm_apply_coe` supply the missing simp rules in both directions.

For any `[LE α]`, `Set.preimageOfDualOrderIso` and `Set.preimageToDualOrderIso` identify the
subtype of a subset pulled back along `OrderDual.ofDual` (respectively `OrderDual.toDual`) with the
order dual of the original subtype.
-/

public section

namespace OrderIso

variable {α β : Type*} [Lattice α] [Lattice β]

/-- **Applying a restricted order isomorphism is applying the original.** -/
@[simp]
theorem Iic_apply_coe (e : α ≃o β) (x : α) (y : Set.Iic x) : ((e.Iic x) y : β) = e y :=
  rfl

/-- **Applying the inverse of a restricted order isomorphism is applying the original
inverse.** -/
@[simp]
theorem Iic_symm_apply_coe (e : α ≃o β) (x : α) (y : Set.Iic (e x)) :
    ((e.Iic x).symm y : α) = e.symm y :=
  rfl

end OrderIso

namespace Set

variable {α : Type*} [LE α]

/-- Pulling a subset `s : Set α` back along `OrderDual.ofDual : αᵒᵈ → α` gives a subtype
order-isomorphic to `(↥s)ᵒᵈ`. -/
def preimageOfDualOrderIso (s : Set α) : ↥(OrderDual.ofDual ⁻¹' s) ≃o (↥s)ᵒᵈ where
  toFun x := OrderDual.toDual ⟨OrderDual.ofDual x.val, x.property⟩
  invFun x := ⟨OrderDual.toDual (OrderDual.ofDual x).val, Set.mem_preimage.2
    (by simpa only [OrderDual.ofDual_toDual] using (OrderDual.ofDual x).property)⟩
  left_inv x := Subtype.ext (OrderDual.toDual_ofDual x.val)
  right_inv x := OrderDual.ext <| Subtype.ext (OrderDual.ofDual_toDual (OrderDual.ofDual x).val)
  map_rel_iff' {a b} := by
    rw [Equiv.coe_fn_mk, Equiv.coe_fn_mk, Equiv.toFun_as_coe, OrderDual.toDual_le_toDual,
      ← Subtype.coe_le_coe, ← Subtype.coe_le_coe, OrderDual.ofDual_le_ofDual]

/-- Evaluating `Set.preimageOfDualOrderIso` on an element of `OrderDual.ofDual ⁻¹' s`. -/
@[simp]
theorem preimageOfDualOrderIso_apply (s : Set α) (x : ↥(OrderDual.ofDual ⁻¹' s)) :
    s.preimageOfDualOrderIso x = OrderDual.toDual ⟨OrderDual.ofDual x.val, x.property⟩ :=
  (rfl)

/-- Evaluating the inverse of `Set.preimageOfDualOrderIso` after coercing to `αᵒᵈ`. -/
@[simp]
theorem preimageOfDualOrderIso_symm_apply_coe (s : Set α) (x : (↥s)ᵒᵈ) :
    (s.preimageOfDualOrderIso.symm x : αᵒᵈ) = OrderDual.toDual (OrderDual.ofDual x).val :=
  (rfl)

/-- Pulling a subset `s : Set αᵒᵈ` back along `OrderDual.toDual : α → αᵒᵈ` gives a subtype
order-isomorphic to `(↥s)ᵒᵈ`. -/
def preimageToDualOrderIso (s : Set αᵒᵈ) : ↥(OrderDual.toDual ⁻¹' s) ≃o (↥s)ᵒᵈ where
  toFun x := OrderDual.toDual ⟨OrderDual.toDual x.val, x.property⟩
  invFun x := ⟨OrderDual.ofDual (OrderDual.ofDual x).val, Set.mem_preimage.2
    (by simpa only [OrderDual.toDual_ofDual] using (OrderDual.ofDual x).property)⟩
  left_inv x := Subtype.ext (OrderDual.ofDual_toDual x.val)
  right_inv x := OrderDual.ext <| Subtype.ext (OrderDual.toDual_ofDual (OrderDual.ofDual x).val)
  map_rel_iff' {a b} := by
    rw [Equiv.coe_fn_mk, Equiv.coe_fn_mk, Equiv.toFun_as_coe, OrderDual.toDual_le_toDual,
      ← Subtype.coe_le_coe, ← Subtype.coe_le_coe, OrderDual.toDual_le_toDual]

/-- Evaluating `Set.preimageToDualOrderIso` on an element of `OrderDual.toDual ⁻¹' s`. -/
@[simp]
theorem preimageToDualOrderIso_apply (s : Set αᵒᵈ) (x : ↥(OrderDual.toDual ⁻¹' s)) :
    s.preimageToDualOrderIso x = OrderDual.toDual ⟨OrderDual.toDual x.val, x.property⟩ :=
  (rfl)

/-- Evaluating the inverse of `Set.preimageToDualOrderIso` after coercing to `α`. -/
@[simp]
theorem preimageToDualOrderIso_symm_apply_coe (s : Set αᵒᵈ) (x : (↥s)ᵒᵈ) :
    (s.preimageToDualOrderIso.symm x : α) = OrderDual.ofDual (OrderDual.ofDual x).val :=
  (rfl)

end Set

end
