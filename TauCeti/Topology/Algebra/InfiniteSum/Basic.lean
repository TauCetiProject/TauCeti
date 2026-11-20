/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Infinite products of indicator functions

Restricting every factor of an infinite product of functions to a set restricts the product:
`∏' i, s.mulIndicator (g i) x = s.mulIndicator (fun y => ∏' i, g i y) x`, for any summation
filter and with no multipliability hypothesis. Off `s` both sides are `∏' i, 1 = 1`.

## Main results

* `Set.mulIndicator_tprod_apply`, `Set.indicator_tsum_apply`: the (multiplicative) indicator of an
  infinite product (sum) of functions is the product (sum) of the indicators.
-/

public section

namespace Set

/-- The multiplicative indicator of an infinite product of functions is the infinite product of
their multiplicative indicators. -/
@[to_additive /-- The indicator of an infinite sum of functions is the infinite sum of their
indicators. -/]
theorem mulIndicator_tprod_apply {α β κ : Type*} [CommMonoid β] [TopologicalSpace β]
    {L : SummationFilter κ} (s : Set α) (g : κ → α → β) (x : α) :
    s.mulIndicator (fun y => ∏'[L] i, g i y) x = ∏'[L] i, s.mulIndicator (g i) x := by
  by_cases hx : x ∈ s <;> simp [hx]

end Set
