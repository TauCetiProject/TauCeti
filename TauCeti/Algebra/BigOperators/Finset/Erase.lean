/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Comparing finite sums after removing one index

Two functions on a finite type that agree away from one index and have the same sum agree
everywhere. The result applies to any additive cancellative commutative monoid.

## Main results

* `TauCeti.eq_of_sum_eq_of_forall_ne`: equality of functions from equality of their sums and
  equality away from one index.
-/

public section

namespace TauCeti

/-- **Two functions with equal sums that agree away from one index are equal.** -/
theorem eq_of_sum_eq_of_forall_ne {ι M : Type*} [Fintype ι] [AddCancelCommMonoid M]
    (x y : ι → M) (hsum : ∑ R, x R = ∑ R, y R) (P : ι)
    (h : ∀ R ≠ P, x R = y R) : x = y := by
  classical
  have herase : ∑ R ∈ Finset.univ.erase P, x R =
      ∑ R ∈ Finset.univ.erase P, y R :=
    Finset.sum_congr rfl fun R hR ↦ h R (Finset.mem_erase.mp hR).1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ P), herase] at hsum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ P)] at hsum
  have hP : x P = y P := add_left_cancel hsum
  funext R
  by_cases hR : R = P
  · simpa only [hR] using hP
  · exact h R hR

end TauCeti
