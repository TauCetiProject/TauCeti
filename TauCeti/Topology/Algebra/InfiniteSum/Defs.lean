/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Finitely supported products and sums in T1 spaces

A family that is `1` (or `0`) outside a finite set `s` has `∏ b ∈ s, f b` (or `∑ b ∈ s, f b`) as a
product (or sum), by `hasProd_prod_of_ne_finset_one`. Mathlib deduces that it is the only one from
`HasProd.unique`, which needs a Hausdorff target. A T1 target suffices: the partial products are
eventually constant, and in a T1 space a constant net converges only to that constant.

## Main results

* `HasProd.eq_prod_of_ne_finset_one`, `HasSum.eq_sum_of_ne_finset_zero`: in a T1 space, a product
  (or sum) of a family that is `1` (or `0`) outside `s` equals the finite product (or sum) over `s`.
-/

public section

open Filter

variable {α β : Type*} [CommMonoid α] [TopologicalSpace α] [T1Space α] {f : β → α} {a : α}
  {s : Finset β} {L : SummationFilter β} [L.LeAtTop] [L.NeBot]

/-- In a T1 space, a product of a family that is `1` outside a finite set `s` equals the finite
product over `s`. -/
@[to_additive /-- In a T1 space, a sum of a family that vanishes outside a finite set `s` equals
the finite sum over `s`. -/]
theorem HasProd.eq_prod_of_ne_finset_one (ha : HasProd f a L) (hf : ∀ b ∉ s, f b = 1) :
    a = ∏ b ∈ s, f b := by
  unfold HasProd at ha
  refine (tendsto_const_nhds_iff.1 (ha.congr' ?_)).symm
  filter_upwards [L.le_atTop (eventually_ge_atTop s)] with t ht
  exact (Finset.prod_subset ht fun b _ hb ↦ hf b hb).symm
