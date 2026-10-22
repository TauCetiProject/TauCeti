/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
public import Mathlib.RingTheory.RootsOfUnity.Lemmas

/-!
# Basic facts about the Eisenstein integers

Let `K = ℚ(ζ₃)`, so that `𝓞 K = ℤ[ζ]` for a primitive cube root of unity `ζ`. This file records
elementary facts about `ℤ[ζ]` complementing Mathlib's `Cyclotomic.Three`:

* `TauCeti.finrank_ringOfIntegers_three`: `𝓞 K` has rank `2` over `ℤ`;
* `IsPrimitiveRoot.toInteger_sub_one_sq_dvd_three`: the square of `ζ - 1`, the prime above `3`,
  divides `3`.
-/

public section

open NumberField

namespace TauCeti

/-- The ring of integers of the third cyclotomic field has rank `2` over `ℤ`. -/
theorem finrank_ringOfIntegers_three {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] : Module.finrank ℤ (𝓞 K) = 2 := by
  rw [RingOfIntegers.rank, IsCyclotomicExtension.finrank (n := 3) K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num)), Nat.totient_prime Nat.prime_three]

end TauCeti

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- The square of `ζ - 1` divides `3` in `𝓞 K`. -/
theorem toInteger_sub_one_sq_dvd_three : (hζ.toInteger - 1) ^ 2 ∣ (3 : 𝓞 K) := by
  obtain ⟨z, _, hz⟩ := hζ.toInteger_isPrimitiveRoot.self_sub_one_pow_dvd_order (k := 2) (by decide)
  exact ⟨z, by simpa only [Nat.cast_ofNat, mul_comm] using hz⟩

end IsPrimitiveRoot
