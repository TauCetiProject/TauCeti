/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Finite products of indicators of pairwise disjoint sets

At a point `x ∈ t i`, a finite product `∏ j ∈ s, (t j).mulIndicator (f j) x` over pairwise disjoint
sets `t j` reduces to its `i`-th factor `f i x`, since every other factor is `1`
(`Finset.prod_mulIndicator_apply_of_mem`). Additively, a sum of indicators of pairwise disjoint
sets takes at `x ∈ t i` the value of its `i`-th summand (`Finset.sum_indicator_apply_of_mem`).
This is how step functions `∑ i, 1_{t i} • c i` on a finite partition are evaluated.
-/

public section

open Set

namespace Finset

variable {ι κ β : Type*} [CommMonoid β]

/-- On a family of pairwise disjoint sets, a product of multiplicative indicators takes at
`x ∈ t i` the value of the `i`-th factor. -/
@[to_additive /-- On a family of pairwise disjoint sets, a sum of indicators takes at `x ∈ t i`
the value of the `i`-th summand. -/]
theorem prod_mulIndicator_apply_of_mem {s : Finset ι} {t : ι → Set κ}
    (hs : (s : Set ι).PairwiseDisjoint t) {i : ι} (hi : i ∈ s) {x : κ} (hx : x ∈ t i)
    (f : ι → κ → β) : ∏ j ∈ s, (t j).mulIndicator (f j) x = f i x := by
  rw [prod_eq_single_of_mem i hi fun j hj hji ↦ mulIndicator_of_notMem
    (Set.disjoint_left.1 (hs hi hj hji.symm) hx) _, mulIndicator_of_mem hx]

end Finset
