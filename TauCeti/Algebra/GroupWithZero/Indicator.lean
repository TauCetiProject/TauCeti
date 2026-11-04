/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Logic.Pairwise

/-!
# Commutation of indicator functions in a monoid with zero

A family `x` commuting pairwise on a set `s` extends by zero outside `s`, via `Set.indicator`, to a
family commuting pairwise everywhere, since `0` commutes with every element.

## Main results

* `Set.Pairwise.pairwise_commute_indicator`: the family `s.indicator x` commutes pairwise.
-/

public section

open scoped Function

namespace Set

variable {ι M₀ : Type*} [MulZeroClass M₀]

/-- Extending a family commuting pairwise on `s` by zero outside `s` gives a family commuting
pairwise everywhere. -/
theorem Pairwise.pairwise_commute_indicator {s : Set ι} {x : ι → M₀}
    (hc : s.Pairwise (Commute on x)) : Pairwise (Commute on s.indicator x) := fun i j hij ↦ by
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · simpa [Function.onFun, hi, hj] using hc hi hj hij
    · simp [Function.onFun, hj]
  · simp [Function.onFun, hi]

end Set
