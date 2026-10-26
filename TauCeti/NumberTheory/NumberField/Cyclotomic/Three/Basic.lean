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
  divides `3`;
* `Units.norm_eq_one_of_isCyclotomicExtension_three`: every unit of `ℤ[ζ]` has norm `1`.
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

namespace Units

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- In the third cyclotomic field, the norm of every unit of the ring of integers is `1`. -/
theorem norm_eq_one_of_isCyclotomicExtension_three (u : (𝓞 K)ˣ) :
    Algebra.norm ℤ (u : 𝓞 K) = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hη : Algebra.norm ℤ hζ.toInteger = 1 := by
    have h := congrArg (Algebra.norm ℤ) hζ.toInteger_cube_eq_one
    rw [map_pow, map_one, ← one_pow 3] at h
    exact (Odd.strictMono_pow (by decide : Odd 3)).injective h
  have hneg : Algebra.norm ℤ (-1 : 𝓞 K) = 1 := by
    have h := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (-1)
    rw [map_neg, map_one] at h
    simp [h, finrank_ringOfIntegers_three]
  have key (k : ℕ) : Algebra.norm ℤ (hζ.toInteger ^ k) = 1 ∧
      Algebra.norm ℤ (-hζ.toInteger ^ k) = 1 := by
    rw [neg_eq_neg_one_mul, map_mul, map_pow, hneg, hη]
    simp
  have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simpa using (key 0).2
  · simpa using (key 1).1
  · simpa using (key 1).2
  · simpa using (key 2).1
  · simpa using (key 2).2

end Units
