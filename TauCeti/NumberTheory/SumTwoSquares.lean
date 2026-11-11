/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Rational sums of two squares

A rational number is a sum of two rational squares exactly when it is nonnegative and its
valuation at every prime congruent to `3` modulo `4` is even. This is the rational form of
Fermat's two-square criterion, and describes the norms from the Gaussian rational field.

The proof uses Mathlib's `Nat.eq_sq_add_sq_iff` after clearing denominators, and
`Rat.num_den_even_padicVal_of_even_padicVal` in the converse direction.
-/

public section

namespace Rat

/-- The sum of two rational squares has even valuation at every prime congruent to `3` modulo
`4`. -/
theorem even_padicValRat_sq_add_sq (x y : ℚ) {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    Even (padicValRat p (x ^ 2 + y ^ 2)) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hzero : x ^ 2 + y ^ 2 = 0
  · simp [hzero]
  -- Clear a common denominator, then use the integral two-square criterion.
  let d : ℕ := x.den * y.den
  let m : ℕ := x.num.natAbs * y.den
  let n : ℕ := y.num.natAbs * x.den
  have hd : (d : ℚ) ≠ 0 := by simp [d, x.den_ne_zero, y.den_ne_zero]
  have hxd : x * (d : ℚ) = x.num * y.den := by
    dsimp [d]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  have hyd : y * (d : ℚ) = y.num * x.den := by
    dsimp [d]
    push_cast
    rw [mul_comm (x.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]
  have hm : (m : ℚ) ^ 2 = (x.num : ℚ) ^ 2 * (y.den : ℚ) ^ 2 := by
    simp [m, mul_pow, sq_abs]
  have hn : (n : ℚ) ^ 2 = (y.num : ℚ) ^ 2 * (x.den : ℚ) ^ 2 := by
    simp [n, mul_pow, sq_abs]
  have hclear : (x ^ 2 + y ^ 2) * (d : ℚ) ^ 2 = (m ^ 2 + n ^ 2 : ℕ) := by
    push_cast
    rw [add_mul, ← mul_pow, ← mul_pow, hxd, hyd, hm, hn]
    ring
  have hN : m ^ 2 + n ^ 2 ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hclear
    exact (mul_ne_zero hzero (pow_ne_zero 2 hd)) hclear
  have heven : Even (multiplicity p (m ^ 2 + n ^ 2)) := by
    by_cases hdiv : p ∣ m ^ 2 + n ^ 2
    · simpa only [Nat.padicValNat_def] using Nat.eq_sq_add_sq_iff.1 ⟨m, n, rfl⟩ p
        (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hN⟩) hp4
    · simp [multiplicity_eq_zero_of_not_dvd hdiv]
  -- The square of the common denominator contributes an even valuation.
  have hv := congrArg (padicValRat p) hclear
  rw [padicValRat.mul hzero (pow_ne_zero 2 hd), padicValRat.pow] at hv
  simp only [padicValRat.of_nat] at hv
  have hevenZ : Even (multiplicity p (m ^ 2 + n ^ 2) : ℤ) := by exact_mod_cast heven
  obtain ⟨t, ht⟩ := hevenZ
  exact ⟨t - multiplicity p d, by omega⟩

/-- A nonnegative rational number with even valuation at every prime congruent to `3` modulo `4`
is a sum of two rational squares. -/
theorem exists_sq_add_sq_of_even_padicValRat {a : ℚ} (ha : 0 ≤ a)
    (h : ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p a)) :
    ∃ x y : ℚ, a = x ^ 2 + y ^ 2 := by
  -- Coprimality of numerator and denominator makes both sets of valuations even.
  have hnum : ∃ x y : ℕ, a.num.natAbs = x ^ 2 + y ^ 2 := by
    apply Nat.eq_sq_add_sq_iff.2
    intro p hp hp4
    simpa only [Nat.padicValNat_def, padicValInt] using
      (Rat.num_den_even_padicVal_of_even_padicVal
        (Nat.prime_of_mem_primeFactors hp) (h p (Nat.prime_of_mem_primeFactors hp) hp4)).1
  have hden : ∃ x y : ℕ, a.den = x ^ 2 + y ^ 2 := by
    apply Nat.eq_sq_add_sq_iff.2
    intro p hp hp4
    simpa only [Nat.padicValNat_def] using
      (Rat.num_den_even_padicVal_of_even_padicVal
        (Nat.prime_of_mem_primeFactors hp) (h p (Nat.prime_of_mem_primeFactors hp) hp4)).2
  obtain ⟨x, y, hxy⟩ := hnum
  obtain ⟨u, v, huv⟩ := hden
  -- Represent numerator times denominator, and divide the two coordinates by the denominator.
  obtain ⟨r, s, hrs⟩ := Nat.sq_add_sq_mul hxy huv
  refine ⟨(r : ℚ) / a.den, (s : ℚ) / a.den, ?_⟩
  have hnumcast : (a.num.natAbs : ℚ) = a.num := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.2 ha)]
  have hprod : a * (a.den : ℚ) ^ 2 = (r : ℚ) ^ 2 + (s : ℚ) ^ 2 := by
    have hh := congrArg (fun t : ℕ ↦ (t : ℚ)) hrs
    push_cast at hh
    rw [hnumcast, ← Rat.mul_den_eq_num] at hh
    nlinarith [hh]
  field_simp
  exact hprod

/-- A rational number is a sum of two squares if and only if it is nonnegative and has even
valuation at every prime congruent to `3` modulo `4`. -/
theorem eq_sq_add_sq_iff {a : ℚ} :
    (∃ x y : ℚ, a = x ^ 2 + y ^ 2) ↔
      0 ≤ a ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p a) :=
  ⟨fun ⟨x, y, hxy⟩ ↦ hxy ▸ ⟨add_nonneg (sq_nonneg x) (sq_nonneg y),
      fun _ hp hp4 ↦ even_padicValRat_sq_add_sq x y hp hp4⟩,
    fun ⟨ha, h⟩ ↦ exists_sq_add_sq_of_even_padicValRat ha h⟩

end Rat
