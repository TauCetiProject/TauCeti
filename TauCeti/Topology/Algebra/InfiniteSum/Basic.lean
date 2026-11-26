/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Products and sums over subtypes and cosets

Mathlib's `tprod_subtype` rewrites a product over a subtype `{b // p b}` as a product over the
whole type of the multiplicative indicator. Two products over different subtypes therefore agree
as soon as the two indicators agree pointwise, which reduces such comparisons to a case split on
the defining predicates.

## Main results

* `tprod_subtype_eq_of_mulIndicator_eq`, `tsum_subtype_eq_of_indicator_eq`: products (sums)
  over two subtypes agree when the factors (summands), extended by one (zero), agree.
* `hasProd_union_leftCoset`, `hasSum_union_leftAddCoset`: a product (sum) over the union of a
  subgroup `s` and a left coset `g • s` (`g +ᵥ s`) with `g ∉ s`, computed coset by coset.
-/

public section

namespace TauCeti

/-- Two products over subtypes agree when their factors, extended by one, agree. -/
@[to_additive /-- Two sums over subtypes agree when their summands, extended by zero, agree. -/]
theorem tprod_subtype_eq_of_mulIndicator_eq {α β : Type*} [CommMonoid α] [TopologicalSpace α]
    {p q : β → Prop} {g g' : β → α}
    (h : ∀ b, {b | p b}.mulIndicator g b = {b | q b}.mulIndicator g' b) :
    ∏' b : {b // p b}, g b = ∏' b : {b // q b}, g' b :=
  (tprod_subtype {b | p b} g).trans <| (tprod_congr h).trans (tprod_subtype {b | q b} g').symm

open scoped Pointwise in
/-- A product over the union of a subgroup `s` and its left coset `g • s`, for `g ∉ s`, is the
product over `s` times the product over the coset, the latter indexed by `s` through `x ↦ g * x`. -/
@[to_additive hasSum_union_leftAddCoset /-- A sum over the union of an additive subgroup `s` and
its left coset `g +ᵥ s`, for `g ∉ s`, is the sum over `s` plus the sum over the coset, the latter
indexed by `s` through `x ↦ g + x`. -/]
theorem hasProd_union_leftCoset {α G : Type*} [CommMonoid α] [TopologicalSpace α]
    [ContinuousMul α] [Group G] {s : Subgroup G} {g : G} (hg : g ∉ s) {f : G → α} {a b : α}
    (ha : HasProd (fun x : s ↦ f x) a) (hb : HasProd (fun x : s ↦ f (g * x)) b) :
    HasProd (fun x : ↥((s : Set G) ∪ g • (s : Set G)) ↦ f x) (a * b) := by
  have hdisj : Disjoint (s : Set G) (g • (s : Set G)) :=
    Set.disjoint_left.mpr fun x hx hgx ↦
      hg (by simpa using s.mul_mem hx (s.inv_mem ((mem_leftCoset_iff g).mp hgx)))
  -- the inverse of `Subgroup.leftCosetEquivSubgroup g` is by definition `x ↦ g * x`
  exact ha.mul_disjoint hdisj ((Subgroup.leftCosetEquivSubgroup g).symm.hasProd_iff.mp hb)

end TauCeti
