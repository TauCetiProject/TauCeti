/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Finitely supported products and sums in T1 spaces

Let `L` be a summation filter whose sets are eventually contained in `L.support`
(`SummationFilter.HasSupport`). A family that is `1` (or `0`) on `L.support` outside a finite set
`s` has the finite product (or sum) over `↑s ∩ L.support` as an `L`-product (or `L`-sum), by
`hasProd_prod_support_of_ne_finset_one`. Mathlib deduces that it is the only one from
`HasProd.unique`, which needs a Hausdorff target. A T1 target suffices when `L` is nontrivial
(`SummationFilter.NeBot`): the partial products are eventually constant, and in a T1 space a
constant net along a nontrivial filter converges only to that constant.

## Main results

* `HasProd.eq_prod_support_of_ne_finset_one`, `HasSum.eq_sum_support_of_ne_finset_zero`: in a
  T1 space, for a nontrivial summation filter `L` with `L.HasSupport`, an `L`-product (or `L`-sum)
  of a family that is `1` (or `0`) on `L.support` outside `s` equals the finite product (or sum)
  over `↑s ∩ L.support`.
* `HasProd.eq_prod_of_ne_finset_one`, `HasSum.eq_sum_of_ne_finset_zero`: the special case of a
  nontrivial summation filter that eventually contains every finite set (`SummationFilter.LeAtTop`),
  such as unconditional summation, where the finite product (or sum) is over `s`.
-/

public section

open Filter

variable {α β : Type*} [CommMonoid α] [TopologicalSpace α] [T1Space α] {f : β → α} {a : α}
  {s : Finset β} {L : SummationFilter β} [L.NeBot]

/-- In a T1 space, for a nontrivial summation filter `L` whose sets are eventually contained in
`L.support`, an `L`-product of a family that is `1` on `L.support` outside a finite set `s` equals
the finite product over `↑s ∩ L.support`. -/
@[to_additive /-- In a T1 space, for a nontrivial summation filter `L` whose sets are eventually
contained in `L.support`, an `L`-sum of a family that vanishes on `L.support` outside a finite set
`s` equals the finite sum over `↑s ∩ L.support`. -/]
theorem HasProd.eq_prod_support_of_ne_finset_one [L.HasSupport] [DecidablePred (· ∈ L.support)]
    (ha : HasProd f a L) (hf : ∀ b ∈ L.support, b ∉ s → f b = 1) :
    a = ∏ b ∈ (↑s ∩ L.support).toFinset, f b := by
  unfold HasProd at ha
  refine (tendsto_const_nhds_iff.1 (ha.congr' ?_)).symm
  filter_upwards [(L.filter.biInter_mem (Set.toFinite (↑s ∩ L.support))).2 fun b hb ↦ hb.2,
    L.eventually_le_support] with t ht ht'
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at ht
  exact Finset.prod_congr_of_eq_on_inter (by grind) (by grind) (by grind)

/-- In a T1 space, for a nontrivial summation filter that eventually contains every finite set, a
product of a family that is `1` outside a finite set `s` equals the finite product over `s`. -/
@[to_additive /-- In a T1 space, for a nontrivial summation filter that eventually contains every
finite set, a sum of a family that vanishes outside a finite set `s` equals the finite sum over
`s`. -/]
theorem HasProd.eq_prod_of_ne_finset_one [L.LeAtTop] (ha : HasProd f a L)
    (hf : ∀ b ∉ s, f b = 1) : a = ∏ b ∈ s, f b := by
  simpa using ha.eq_prod_support_of_ne_finset_one fun b _ ↦ hf b
