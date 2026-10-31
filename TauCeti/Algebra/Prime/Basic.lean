/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Prime.Defs

/-!
# Divisibility by a prime is unchanged by a power factor prime to it

If a prime `p` does not divide `u`, then multiplying `a` by any power of `u` does not change
whether `p` divides it. For example, replacing an integer radicand `a` by `a * u ^ 2` with
`p ∤ u` keeps it in the same square class without changing whether `p` divides it.

## Main results

* `Prime.dvd_mul_pow_iff`: for a prime `p` with `p ∤ u`, `p ∣ a * u ^ n ↔ p ∣ a`.
-/

public section

variable {M : Type*} [CommMonoidWithZero M] {p a u : M}

/-- If a prime `p` does not divide `u`, then `p` divides `a * u ^ n` exactly when it
divides `a`. -/
@[simp]
theorem Prime.dvd_mul_pow_iff (hp : Prime p) (hu : ¬ p ∣ u) {n : ℕ} :
    p ∣ a * u ^ n ↔ p ∣ a := by
  rw [hp.dvd_mul, or_iff_left (mt hp.dvd_of_dvd_pow hu)]
