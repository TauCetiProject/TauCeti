/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Scaling weighted sums of natural numbers

In a commutative semiring, multiplying a weighted sum `∑ᵢ sᵢ cᵢ` of natural numbers `cᵢ` by a
natural number `d` gives the weighted sum `∑ᵢ sᵢ (cᵢ d)` of the products, computed in `ℕ`. This
turns inequalities for counts `cᵢ` weighted by a dimension `d`, such as the strong Morse
inequalities with coefficients in a `d`-dimensional space, into inequalities for the sequence
`cᵢ d` of natural numbers.
-/

public section

namespace TauCeti

/-- Scaling a weighted sum of natural numbers `cᵢ` by a natural number `d` gives the same weighted
sum of the products `cᵢ d`: `d ∑ᵢ sᵢ cᵢ = ∑ᵢ sᵢ (cᵢ d)`. This turns the strong inequalities for
counts `cᵢ` weighted by the dimension `d` of a coefficient space into strong inequalities for the
sequence `cᵢ d`. -/
theorem natCast_mul_sum_mul_natCast {ι R : Type*} [CommSemiring R] (d : ℕ) (s : ι → R)
    (c : ι → ℕ) (t : Finset ι) :
    (d : R) * ∑ i ∈ t, s i * c i = ∑ i ∈ t, s i * ((c i * d : ℕ) : R) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  ring

end TauCeti
