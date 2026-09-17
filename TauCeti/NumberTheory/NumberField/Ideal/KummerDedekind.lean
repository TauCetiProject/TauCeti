/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

/-!
# Counting the primes above a rational prime by Kummer–Dedekind

Mathlib's number-field Kummer–Dedekind theorem
(`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`) is a bijection between the primes of
`𝓞 K` above a rational prime `p` and the monic irreducible factors of `minpoly ℤ θ` modulo `p`,
valid whenever `p` does not divide the conductor exponent of the algebraic integer `θ`. This file
records its cardinality form: the number of primes above `p` is the number of those factors. This is
the shape in which splitting laws are read off a generator, for instance the quadratic laws of
`TauCeti.NumberTheory.NumberField.Quadratic.Splitting`.

The first instance is the prime `2` for a generator `ω` with minimal polynomial `X² - X + c` and
odd conductor exponent: the reduction `X² + X + c` mod `2` is `X (X + 1)` when `c` is even and the
third cyclotomic polynomial `X² + X + 1`, irreducible over `𝔽₂`, when `c` is odd, so there are two
primes above `2` in the first case and one in the second.

## Main results

* `RingOfIntegers.ncard_primesOver_eq_card_monicFactorsMod`: the number of primes of `𝓞 K` above
  `p` equals the number of monic irreducible factors of `minpoly ℤ θ` mod `p`, for
  `p ∤ exponent θ`.
* `NumberField.card_monicFactorsMod_two_of_minpoly_eq_X_sq_sub_X_add`: the reduction mod `2` of
  `X² - X + c` has `if 2 ∣ c then 2 else 1` monic irreducible factors.
* `NumberField.ncard_primesOver_two_of_minpoly_eq_X_sq_sub_X_add`: for a generator with minimal
  polynomial `X² - X + c` and odd conductor exponent, the number of primes above `2` is
  `if 2 ∣ c then 2 else 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §8, Proposition (8.3).
-/

public section

open Ideal Polynomial RingOfIntegers UniqueFactorizationMonoid
open scoped NumberField

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- **The Kummer–Dedekind count.** When `p` does not divide the conductor exponent of `θ`, the
primes of `𝓞 K` above `p` are counted by the monic irreducible factors of `minpoly ℤ θ` mod `p`. -/
theorem ncard_primesOver_eq_card_monicFactorsMod (θ : 𝓞 K) {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ exponent θ) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = (monicFactorsMod θ p).card := by
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp)]
  exact Nat.card_eq_finsetCard _

end RingOfIntegers

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- **The monic irreducible factors of `X² - X + c` modulo `2`.** For `ω` with minimal polynomial
`X² - X + c` over `ℤ`, the reduction of that polynomial modulo `2` has two monic irreducible
factors when `c` is even, since `X² + X = X (X + 1)` over `𝔽₂`, and one when `c` is odd, since
`X² + X + 1` has no root in `𝔽₂`. -/
theorem card_monicFactorsMod_two_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {c : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C c) :
    (monicFactorsMod ω 2).card = if 2 ∣ c then 2 else 1 := by
  classical
  have hmap : (minpoly ℤ ω).map (Int.castRingHom (ZMod 2)) = X ^ 2 + X + C (c : ZMod 2) := by
    rw [hmin, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, eq_intCast, sub_eq_add_neg, CharTwo.neg_eq]
  simp only [monicFactorsMod, hmap]
  by_cases hc : 2 ∣ c
  · -- `c` is even: `X² + X = (X - 0)(X - 1)`, two distinct linear factors.
    have hc0 : (c : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
    have hfac : (X ^ 2 + X + C (c : ZMod 2) : (ZMod 2)[X]) = (X - C 0) * (X - C 1) := by
      rw [hc0, C_0, add_zero, sub_zero, C_1, CharTwo.sub_eq_add]; ring
    have h0 : normalizedFactors (X - C (0 : ZMod 2)) = {X - C 0} := by
      rw [normalizedFactors_irreducible (irreducible_X_sub_C _),
        (monic_X_sub_C _).normalize_eq_self]
    have h1 : normalizedFactors (X - C (1 : ZMod 2)) = {X - C 1} := by
      rw [normalizedFactors_irreducible (irreducible_X_sub_C _),
        (monic_X_sub_C _).normalize_eq_self]
    have hne : (X - C (0 : ZMod 2) : (ZMod 2)[X]) ≠ X - C 1 := by
      rw [Ne, sub_right_inj, C_inj]; exact zero_ne_one
    rw [ite_eq_left hc, hfac, normalizedFactors_mul (X_sub_C_ne_zero 0) (X_sub_C_ne_zero 1),
      h0, h1]
    simp only [Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.singleton_union]
    exact Finset.card_pair hne
  · -- `c` is odd: `X² + X + 1` is the third cyclotomic polynomial, which is irreducible over
    -- `𝔽₂` because `2` has order `2` modulo `3`.
    have hc1 : (c : ZMod 2) = 1 := by
      rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff']; omega
    rw [ite_eq_right hc, hc1, C_1, ← cyclotomic_three,
      normalizedFactors_cyclotomic_card (p := 2) (f := 1) (by simp) (by norm_num),
      Nat.totient_prime Nat.prime_three]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : ∀ h : Nat.Coprime (2 ^ 1) 3, orderOf (ZMod.unitOfCoprime (2 ^ 1) h) = 2 := fun h =>
      orderOf_eq_prime (p := 2)
        (by
          ext
          simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one]
          decide)
        (by
          intro h1
          have := congrArg Units.val h1
          simp only [ZMod.coe_unitOfCoprime, Units.val_one] at this
          revert this
          decide)
    rw [h2]

/-- **The number of primes above `2` for a generator with minimal polynomial `X² - X + c`.** Let
`K` be generated over `ℚ` by an algebraic integer `ω` with minimal polynomial `X² - X + c` over
`ℤ`, and suppose `2` does not divide the conductor exponent of `ω`. Then there are two primes of
`𝓞 K` above `2` when `c` is even and one when `c` is odd. -/
theorem ncard_primesOver_two_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {c : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C c) (hexp : ¬ 2 ∣ exponent ω) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = if 2 ∣ c then 2 else 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := ncard_primesOver_eq_card_monicFactorsMod ω hexp
  rw [Nat.cast_ofNat] at h
  rw [h, card_monicFactorsMod_two_of_minpoly_eq_X_sq_sub_X_add hmin]

end NumberField
