/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
public import TauCeti.RingTheory.Norm.Quadratic

/-!
# Basic facts about the Eisenstein integers

Let `K = ℚ(ζ₃)`, so that `𝓞 K = ℤ[ζ]` for a primitive cube root of unity `ζ`. This file records
elementary facts about `ℤ[ζ]` complementing Mathlib's `Cyclotomic.Three`:

* `TauCeti.finrank_ringOfIntegers_three`: `𝓞 K` has rank `2` over `ℤ`;
* `IsPrimitiveRoot.toInteger_sub_one_sq_dvd_three`: the square of `ζ - 1`, the prime above `3`,
  divides `3`;
* `IsPrimitiveRoot.minpoly_toInteger_eq_X_sq_add_X_add_one`: the minimal polynomial of `ζ` over
  `ℤ` is `X² + X + 1`;
* `IsPrimitiveRoot.trace_toInteger_of_three`, `IsPrimitiveRoot.norm_toInteger_of_three`: `ζ` has
  trace `-1` and norm `1`;
* `IsPrimitiveRoot.norm_intCast_add_intCast_mul_toInteger_of_three`: the norm of `a + b ζ` is
  `a² - ab + b²`;
* `Units.norm_eq_one_of_isCyclotomicExtension_three`: every unit of `ℤ[ζ]` has norm `1`.
-/

public section

open NumberField Polynomial

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

/-- The minimal polynomial over `ℤ` of a primitive cube root of unity `ζ ∈ 𝓞 K` is
`X² + X + 1`. -/
theorem minpoly_toInteger_eq_X_sq_add_X_add_one [NumberField K] :
    minpoly ℤ hζ.toInteger = X ^ 2 + X + 1 := by
  have h : minpoly ℤ ζ = X ^ 2 + X + 1 := by
    rw [← cyclotomic_eq_minpoly hζ (by norm_num), cyclotomic_prime ℤ 3]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
    ring
  -- The image of `hζ.toInteger` in `K` is `ζ` by definition (`IsPrimitiveRoot.coe_toInteger`).
  rw [← RingOfIntegers.minpoly_coe]
  exact h

/-- The trace of `ζ` over `ℤ` is `-1`, read off from its minimal polynomial `X² + X + 1`. -/
@[simp]
theorem trace_toInteger_of_three [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    Algebra.trace ℤ (𝓞 K) hζ.toInteger = -1 := by
  have hdeg : (X ^ 2 + X + 1 : ℤ[X]).natDegree = 2 := by compute_degree!
  rw [← hζ.integralPowerBasis_gen, Algebra.trace_eq_matrix_trace hζ.integralPowerBasis.basis,
    Matrix.trace_eq_neg_charpoly_nextCoeff, charpoly_leftMulMatrix, integralPowerBasis_gen,
    minpoly_toInteger_eq_X_sq_add_X_add_one, nextCoeff_of_natDegree_pos (by lia), hdeg]
  simp [coeff_one]

/-- The norm of `ζ` over `ℤ` is `1`, read off from its minimal polynomial `X² + X + 1`. -/
@[simp]
theorem norm_toInteger_of_three [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    Algebra.norm ℤ hζ.toInteger = 1 := by
  rw [← hζ.integralPowerBasis_gen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    integralPowerBasis_gen, integralPowerBasis_dim, minpoly_toInteger_eq_X_sq_add_X_add_one,
    Nat.totient_prime Nat.prime_three]
  simp

/-- The norm of `a + b ζ` in `𝓞 K = ℤ[ζ]` is `a² - ab + b²`. -/
@[simp]
theorem norm_intCast_add_intCast_mul_toInteger_of_three [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] (a b : ℤ) :
    Algebra.norm ℤ ((a : 𝓞 K) + b * hζ.toInteger) = a ^ 2 - a * b + b ^ 2 := by
  have : Algebra.IsQuadraticExtension ℤ (𝓞 K) := ⟨TauCeti.finrank_ringOfIntegers_three⟩
  rw [← eq_intCast (algebraMap ℤ (𝓞 K)) a, ← eq_intCast (algebraMap ℤ (𝓞 K)) b,
    Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul, trace_toInteger_of_three,
    norm_toInteger_of_three]
  ring

end IsPrimitiveRoot

namespace Units

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- In the third cyclotomic field, the norm of every unit of the ring of integers is `1`. -/
theorem norm_eq_one_of_isCyclotomicExtension_three (u : (𝓞 K)ˣ) :
    Algebra.norm ℤ (u : 𝓞 K) = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hneg : Algebra.norm ℤ (-1 : 𝓞 K) = 1 := by
    have h := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (-1)
    rw [map_neg, map_one] at h
    simp [h, finrank_ringOfIntegers_three]
  have key (k : ℕ) : Algebra.norm ℤ (hζ.toInteger ^ k) = 1 ∧
      Algebra.norm ℤ (-hζ.toInteger ^ k) = 1 := by
    rw [neg_eq_neg_one_mul, map_mul, map_pow, hneg, hζ.norm_toInteger_of_three]
    simp
  have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simpa using (key 0).2
  · simp
  · simpa using (key 1).2
  · simp
  · simpa using (key 2).2

end Units
