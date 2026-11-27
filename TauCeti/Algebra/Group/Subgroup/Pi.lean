/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Product equivalences and orders for `Subgroup.pi`

For a family of subgroups `H : ∀ i, Subgroup (G i)`, Mathlib defines `Subgroup.pi Set.univ H` as
the subgroup of `∀ i, G i` whose `i`-th coordinate lies in `H i`, and `Equiv.Set.univPi` identifies
its underlying set with `∀ i, H i`. This file upgrades that equivalence to the group isomorphism
`Subgroup.piEquiv` (and additive group isomorphism `AddSubgroup.piEquiv`), the dependent-product
analogue of `Subgroup.prodEquiv`, and deduces over a finite index type that `Subgroup.pi Set.univ H`
has order `∏ i, #(H i)` (`Subgroup.card_pi`; compare Mathlib's `Subgroup.index_pi` for the index of
a family of subgroups of a single group).

## Main definitions and results

* `Subgroup.piEquiv`, `AddSubgroup.piEquiv`: `Subgroup.pi Set.univ H ≃* ∀ i, H i` and
  `AddSubgroup.pi Set.univ H ≃+ ∀ i, H i`.
* `Subgroup.coe_piEquiv_apply`, `Subgroup.coe_piEquiv_symm_apply` (and additive forms):
  characteristic `simp` lemmas for evaluating `piEquiv` and its inverse.
* `Subgroup.card_pi`, `AddSubgroup.card_pi`:
  `Nat.card (Subgroup.pi Set.univ H) = ∏ i, Nat.card (H i)`.
-/

public section

namespace Subgroup

section PiEquiv

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- The product subgroup `Subgroup.pi Set.univ H` is isomorphic to the dependent product
`∀ i, H i`, the `Pi` analogue of `Subgroup.prodEquiv`. -/
@[to_additive
/-- The product additive subgroup `AddSubgroup.pi Set.univ H` is isomorphic to the dependent
product `∀ i, H i`, the `Pi` analogue of `AddSubgroup.prodEquiv`. -/]
def piEquiv (H : ∀ i, Subgroup (G i)) : Subgroup.pi Set.univ H ≃* ∀ i, H i :=
  { Equiv.Set.univPi fun i ↦ (H i : Set (G i)) with
    map_mul' := fun _ _ ↦ rfl }

/-- The `i`-th coordinate of `Subgroup.piEquiv H x` coerces to `(x : ∀ i, G i) i`. -/
@[to_additive (attr := simp)
/-- The `i`-th coordinate of `AddSubgroup.piEquiv H x` coerces to `(x : ∀ i, G i) i`. -/]
theorem coe_piEquiv_apply (H : ∀ i, Subgroup (G i)) (x : Subgroup.pi Set.univ H) (i : ι) :
    (piEquiv H x i : G i) = (x : ∀ i, G i) i :=
  (rfl)

/-- `(Subgroup.piEquiv H).symm x` coerces to the function `fun i ↦ (x i : G i)`. -/
@[to_additive (attr := simp)
/-- `(AddSubgroup.piEquiv H).symm x` coerces to the function `fun i ↦ (x i : G i)`. -/]
theorem coe_piEquiv_symm_apply (H : ∀ i, Subgroup (G i)) (x : ∀ i, H i) :
    ((piEquiv H).symm x : ∀ i, G i) = fun i ↦ (x i : G i) :=
  (rfl)

end PiEquiv

section Card

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

/-- The product of a finite family of subgroups has the product of their orders. -/
@[to_additive /-- The product of a finite family of additive subgroups has the product of their
orders. -/]
theorem card_pi [Fintype η] (H : ∀ i, Subgroup (f i)) :
    Nat.card (Subgroup.pi Set.univ H) = ∏ i, Nat.card (H i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr (piEquiv H).toEquiv

end Card

end Subgroup
