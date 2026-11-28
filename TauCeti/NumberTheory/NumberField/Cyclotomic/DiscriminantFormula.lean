/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Root discriminants of rational cyclotomic fields

The explicit cyclotomic discriminant formula gives the root discriminant as the level
with a correction factor depending only on its prime divisors. In particular, increasing
the level without introducing new primes scales the root discriminant by the same factor.

The formula uses `IsCyclotomicExtension.Rat.natAbs_discr`.
-/

public section

open NumberField Real

namespace IsCyclotomicExtension.Rat

/-- The root discriminant of a rational cyclotomic field is its level divided by a
product depending only on the primes dividing that level. -/
theorem rootDiscr_eq_div_prod (n : ℕ) [NeZero n] (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] :
    rootDiscr F = (n : ℝ) / ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((p - 1 : ℕ) : ℝ)⁻¹ := by
  have htot : n.totient ≠ 0 := (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p : ℝ) ^ (n.totient / (p - 1) : ℕ) =
        ((p : ℝ) ^ ((p - 1 : ℕ) : ℝ)⁻¹) ^ n.totient := by
    have hd : p - 1 ∣ n.totient := by
      rw [← Nat.totient_prime (Nat.prime_of_mem_primeFactors hp)]
      exact Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    have hne : (p - 1 : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
    calc
      _ = (p : ℝ) ^ ((n.totient : ℝ) * ((p - 1 : ℕ) : ℝ)⁻¹) := by
        rw [← Real.rpow_natCast, Nat.cast_div hd (Nat.cast_ne_zero.mpr hne), div_eq_mul_inv]
      _ = _ := by rw [mul_comm, Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]
  have hprod :
      ((∏ p ∈ n.primeFactors, p ^ (n.totient / (p - 1)) : ℕ) : ℝ) =
        (∏ p ∈ n.primeFactors, (p : ℝ) ^ ((p - 1 : ℕ) : ℝ)⁻¹) ^ n.totient := by
    push_cast
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl hfactor
  have hpos : 0 ≤ ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((p - 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hden : (∏ p ∈ n.primeFactors, p ^ (n.totient / (p - 1))) ≠ 0 :=
    (Finset.prod_pos fun p hp ↦ pow_pos (Nat.prime_of_mem_primeFactors hp).pos _).ne'
  rw [rootDiscr_def, finrank n F, ← Int.natCast_natAbs, natAbs_discr n F, Int.cast_natCast,
    Nat.cast_div (Nat.prod_primeFactors_pow_totient_ediv_dvd n) (Nat.cast_ne_zero.mpr hden),
    Nat.cast_pow, hprod,
    Real.div_rpow (by positivity) (pow_nonneg hpos _),
    pow_rpow_inv_natCast (Nat.cast_nonneg n) htot, pow_rpow_inv_natCast hpos htot]

/-- Multiplying a rational cyclotomic level by a factor supported on the same primes
multiplies the root discriminant by that factor. -/
theorem rootDiscr_mul_level_of_primeFactors_subset {n m : ℕ} [NeZero n] [NeZero m]
    (F G : Type*) [Field F] [Field G] [NumberField F] [NumberField G]
    [IsCyclotomicExtension {n} ℚ F] [IsCyclotomicExtension {n * m} ℚ G]
    (hm : m.primeFactors ⊆ n.primeFactors) : rootDiscr G = (m : ℝ) * rootDiscr F := by
  have hs : (n * m).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_mul (NeZero.ne n) (NeZero.ne m), Finset.union_eq_left.mpr hm]
  rw [rootDiscr_eq_div_prod (n * m) G, rootDiscr_eq_div_prod n F, hs,
    Nat.cast_mul, mul_comm (n : ℝ) (m : ℝ), mul_div_assoc]

end IsCyclotomicExtension.Rat
