/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-!
# Sub-dp-ideals

This file supplements `Mathlib.RingTheory.DividedPowers.SubDPIdeal` with stability of positive
ordinary powers of a divided power ideal.

## Main results

* `DividedPowers.isSubDPIdeal_pow`: every positive power `I ^ e` (`e ≠ 0`) of a divided power
  ideal `(I, hI)` is a sub-dp-ideal of `(I, hI)`.
-/

public section

namespace DividedPowers

/-- Every positive power `I ^ e` (`e ≠ 0`) of a divided power ideal `(I, hI)` is a sub-dp-ideal
of `(I, hI)`. -/
theorem isSubDPIdeal_pow {A : Type*} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)
    {e : ℕ} (he : e ≠ 0) : hI.IsSubDPIdeal (I ^ e) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  simpa [SubDPIdeal.prod, smul_eq_mul, ← pow_succ'] using
    (SubDPIdeal.prod (hI := hI) (I ^ k)).toIsSubDPIdeal

end DividedPowers
