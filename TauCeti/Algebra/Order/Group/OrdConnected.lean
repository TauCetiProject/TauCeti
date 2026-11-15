/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import TauCeti.Order.Interval.Set.OrdConnected

/-!
# Order-connected subgroups

In a group with a right-invariant preorder (`[MulRightMono G]` / `[AddRightMono G]`), translation
reduces every interval `Set.Icc x y` to `Set.Icc 1 (y / x)` (additively, `Set.Icc 0 (y - x)`), so a
subgroup is order-connected if and only if it contains every element between the identity and one of
its members. This connects Mathlib's `Set.OrdConnected` typeclass to the positive-element heredity
condition used for ideals and star subalgebras of ordered rings.

## Main results

* `SubgroupClass.ordConnected_iff` and `AddSubgroupClass.ordConnected_iff`: a subgroup is
  order-connected if and only if `1 ≤ a ≤ b` (additively, `0 ≤ a ≤ b`) and `b ∈ s` imply `a ∈ s`.
-/

public section

/-- In a group with right-monotone multiplication, a subgroup is order-connected if and only if
`1 ≤ a ≤ b` and `b ∈ s` imply `a ∈ s`. -/
@[to_additive /-- In an additive group with right-monotone addition, an additive subgroup is
order-connected if and only if `0 ≤ a ≤ b` and `b ∈ s` imply `a ∈ s`. -/]
theorem SubgroupClass.ordConnected_iff {G S : Type*} [Group G] [Preorder G] [MulRightMono G]
    [SetLike S G] [SubgroupClass S G] {s : S} :
    (s : Set G).OrdConnected ↔ ∀ ⦃a b : G⦄, 1 ≤ a → a ≤ b → b ∈ s → a ∈ s := by
  refine ⟨fun h a b ha hab hb ↦ h.out (one_mem s) hb ⟨ha, hab⟩, fun h ↦ ⟨fun x hx y hy z hz ↦ ?_⟩⟩
  have hzx : z / x ∈ s :=
    h (one_le_div'.mpr hz.1) (div_le_div_right' hz.2 x) (div_mem hy hx)
  exact SetLike.mem_coe.mpr (div_mul_cancel z x ▸ mul_mem hzx hx)
