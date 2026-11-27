/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Integer valuations in finite products

When a finite product is a perfect power and a prime divides only one factor, the exponent
divides the valuation of that factor.
-/

public section

/-- If only the factor at `i` can contribute to the valuation at a prime, that factor's
valuation is divisible by the exponent of the perfect-power product. -/
theorem Finset.dvd_padicValInt_of_prod_eq_pow {ι : Type*} {s : Finset ι} {i : ι}
    {f : ι → ℤ} {y : ℤ} {ℓ q : ℕ} (hi : i ∈ s) (hp : q.Prime)
    (hprod : ∏ j ∈ s, f j = y ^ ℓ)
    (huniq : (q : ℤ) ∣ f i → ∀ j ∈ s, (q : ℤ) ∣ f j → j = i) :
    ℓ ∣ padicValInt q (f i) := by
  classical
  by_cases hqi : (q : ℤ) ∣ f i
  · have hp' : Prime (q : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
    have hval := congrArg (emultiplicity (q : ℤ)) hprod
    rw [Finset.emultiplicity_prod hp', Finset.sum_eq_single_of_mem i hi] at hval
    · have hmul := multiplicity_eq_of_emultiplicity_eq hval
      rw [padicValInt.of_ne_one_ne_zero, hmul, multiplicity_pow hp']
      exact dvd_mul_right ..
    · exact fun j hj hji ↦ emultiplicity_eq_zero.mpr fun hqj ↦ hji (huniq hqi j hj hqj)
  · rw [padicValInt.eq_zero_of_not_dvd hqi]
    exact dvd_zero _
