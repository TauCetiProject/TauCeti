/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The order of a product of subgroups

For a family of subgroups `H i ≤ G i` over a finite index type, the product subgroup
`Subgroup.pi Set.univ H ≤ ∀ i, G i` has order `∏ i, #(H i)` (`Subgroup.card_pi`). Mathlib's
`Subgroup.index_pi` is the corresponding statement for the index, for a family of subgroups of a
single group.
-/

public section

namespace Subgroup

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

/-- The product of a finite family of subgroups has the product of their orders. -/
@[to_additive /-- The product of a finite family of additive subgroups has the product of their
orders. -/]
theorem card_pi [Fintype η] (H : ∀ i, Subgroup (f i)) :
    Nat.card (Subgroup.pi Set.univ H) = ∏ i, Nat.card (H i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun x i := ⟨x.val i, x.property i (Set.mem_univ i)⟩
      invFun y := ⟨fun i ↦ y i, fun i _ ↦ (y i).property⟩
      left_inv _ := rfl
      right_inv _ := rfl }

end Subgroup
