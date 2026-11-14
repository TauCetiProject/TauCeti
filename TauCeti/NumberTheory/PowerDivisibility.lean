/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.IntervalCases

/-!
# A power divisibility obstruction

The divisibility `2 ^ r ∣ 3 ^ r - 1` holds precisely for `r = 0, 1, 2, 4`.
We also deduce the positive-exponent restriction from the integer coefficient equation
`3 ^ r * (3 ^ r - 1) * b₂ = 2 ^ r * (2 ^ r - 1) * b₃` when `b₂` is odd.

This is the arithmetic step in the Adams–Atiyah exclusion of odd Hopf invariant:
commuting the second and third Adams operations produces the coefficient equation.
No K-theory or Hopf-invariant comparison is asserted here. The proof reuses Mathlib's
lifting-the-exponent theorem rather than constructing a separate valuation API.

## References

J. F. Adams and M. F. Atiyah, *K-theory and the Hopf invariant*,
Quart. J. Math. Oxford (2) 17 (1966), 31–38.
-/

public section

namespace TauCeti

/-- The only natural exponents satisfying `2 ^ r ∣ 3 ^ r - 1` are `0, 1, 2, 4`. -/
theorem two_pow_dvd_three_pow_sub_one_iff {r : ℕ} :
    2 ^ r ∣ 3 ^ r - 1 ↔ r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 4 := by
  constructor
  · intro h
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hpos : 0 < 3 ^ r - 1 := by
      have := Nat.one_lt_pow hr (by decide : 1 < (3 : ℕ))
      omega
    have hfin : FiniteMultiplicity 2 (3 ^ r - 1) :=
      Nat.finiteMultiplicity_iff.mpr ⟨by decide, hpos⟩
    have hle : r ≤ multiplicity 2 (3 ^ r - 1) :=
      hfin.pow_dvd_iff_le_multiplicity.mp h
    rcases Nat.even_or_odd r with heven | hodd
    · -- Lifting the exponent gives ν₂(3ʳ − 1) = 2 + ν₂(r).
      have hval := Nat.multiplicity_pow_two_sub_one
        (by decide : 1 < (3 : ℕ)) (by decide) hr heven
      have htwo : multiplicity (2 : ℕ) 2 = 1 :=
        multiplicity_eq_of_dvd_of_not_dvd (by norm_num) (by norm_num)
      have hfour : multiplicity (2 : ℕ) 4 = 2 :=
        multiplicity_eq_of_dvd_of_not_dvd (by norm_num) (by norm_num)
      norm_num [htwo, hfour] at hval
      -- The elementary bound 2ν₂(r) ≤ r now forces r ≤ 4.
      have hbound : 2 * multiplicity 2 r ≤ r := mul_multiplicity_le
      have hrle : r ≤ 4 := by omega
      interval_cases r <;> norm_num at *
    · -- For odd r, the coprime-exponent form of LTE gives valuation one.
      have hval : multiplicity 2 (3 ^ r - 1) = 1 := by
        have hodd' : ¬ (2 : ℤ) ∣ (r : ℤ) := by
          exact_mod_cast hodd.not_two_dvd_nat
        have h := emultiplicity_pow_sub_pow_of_prime Int.prime_two
          (x := 3) (y := 1) (by norm_num) (by norm_num) hodd'
        have hcast : ((3 ^ r - 1 : ℕ) : ℤ) = 3 ^ r - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 3 ^ r), Nat.cast_pow, Nat.cast_ofNat,
            Nat.cast_one]
        rw [one_pow] at h
        have htwo : emultiplicity (2 : ℤ) (3 - 1) = (1 : ℕ) :=
          emultiplicity_eq_coe.mpr ⟨by norm_num, by norm_num⟩
        have hnat := Int.natCast_emultiplicity 2 (3 ^ r - 1)
        rw [hcast] at hnat
        exact multiplicity_eq_of_emultiplicity_eq_some (hnat.symm.trans (h.trans htwo))
      omega
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

/-- An odd second coefficient in the Adams-operation equation forces
`2 ^ r ∣ 3 ^ r - 1`. The coefficients may be negative. -/
theorem two_pow_dvd_three_pow_sub_one_of_odd_mul_eq {r : ℕ} {b₂ b₃ : ℤ}
    (hb₂ : Odd b₂)
    (h : (3 : ℤ) ^ r * (3 ^ r - 1) * b₂ = 2 ^ r * (2 ^ r - 1) * b₃) :
    2 ^ r ∣ 3 ^ r - 1 := by
  have hcop : IsCoprime ((3 : ℤ) ^ r * b₂) (2 ^ r) :=
    ((by decide : Odd (3 : ℤ)).pow.mul hb₂).isCoprime_two.pow_right
  have hdvd : (2 : ℤ) ^ r ∣ (3 ^ r * b₂) * (3 ^ r - 1) := by
    rw [mul_right_comm, h]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hdvd' : (2 : ℤ) ^ r ∣ 3 ^ r - 1 := hcop.symm.dvd_of_dvd_mul_left hdvd
  have hle : 1 ≤ (3 : ℕ) ^ r := Nat.one_le_pow _ _ (by decide)
  exact_mod_cast hdvd'

/-- For a positive exponent, the Adams-operation coefficient equation with odd `b₂`
allows only `r = 1, 2, 4`. -/
theorem eq_one_or_eq_two_or_eq_four_of_odd_mul_eq {r : ℕ} {b₂ b₃ : ℤ}
    (hr : 0 < r) (hb₂ : Odd b₂)
    (h : (3 : ℤ) ^ r * (3 ^ r - 1) * b₂ = 2 ^ r * (2 ^ r - 1) * b₃) :
    r = 1 ∨ r = 2 ∨ r = 4 := by
  have := two_pow_dvd_three_pow_sub_one_iff.mp
    (two_pow_dvd_three_pow_sub_one_of_odd_mul_eq hb₂ h)
  omega

end TauCeti
