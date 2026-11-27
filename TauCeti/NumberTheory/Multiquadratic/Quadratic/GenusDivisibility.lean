/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank
import TauCeti.NumberTheory.NumberField.ClassGroupElementaryTwoQuotient
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace

/-!
# Genus divisibility of the class number of an imaginary quadratic field

Let `K` be an imaginary quadratic field, given only as a number field of degree two over `ℚ` with
`NumberField.discr K < 0`, and let `t` be the number of distinct primes dividing `d = |disc K|`.
Genus theory makes the class number `h` of `K` divisible by `2 ^ (t - 1)`:

`2 ^ (t - 1) ∣ h`.

This is the imaginary `2`-rank formula `2-rank Cl(K) = t - 1`
(`TauCeti.Multiquadratic.twoRank_eq_ncard_ramifiedPrimes_sub_one`), applied to a squarefree
radicand presentation `K = ℚ(√d₀)` (`NumberField.exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top`)
whose radicand is negative because `K` is totally complex, together with the divisibility of `h`
by `2 ^ (2-rank)` (`NumberField.two_pow_classGroupTwoRank_dvd_classNumber`). The ramified primes
counted by the `2`-rank formula are the prime factors of `disc K`
(`NumberField.ncard_ramifiedPrimes`), so the statement is phrased with `t` read off the
discriminant alone. The Gaussian field `ℚ(i)`, radicand `-1`, is included: there `t = 1` and the
statement is `1 ∣ h`.

In particular an odd class number forces `t = 1`, and then the fundamental discriminant
`disc K` is `-4`, `-8` or `-p` for a prime `p ≡ 3 (mod 4)`
(`Int.IsFundamentalDiscr.eq_neg_four_or_eq_neg_eight_or_exists_prime_of_card_primeFactors_eq_one`).
The sign hypothesis is essential: the real quadratic field `ℚ(√3)` has discriminant `12`, so
`t = 2`, and class number `1`.

See D. A. Cox, *Primes of the Form x² + ny²*, §3.B and §6.A, for genus theory, and J. Oesterlé,
*Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki, exposé 631 (1984/85),
Astérisque 121–122, p. 310, for the form `2 ^ (t - 1) ∣ h` used in effective class-number bounds.

## Main results

* `TauCeti.Multiquadratic.two_pow_card_primeFactors_discr_sub_one_dvd_classNumber`: genus
  divisibility `2 ^ (t - 1) ∣ h` for every imaginary quadratic field.
* `TauCeti.Multiquadratic.card_primeFactors_discr_eq_one_of_odd_classNumber`: an imaginary
  quadratic field of odd class number has exactly one ramified prime.
* `TauCeti.Multiquadratic.discr_eq_neg_four_or_eq_neg_eight_or_exists_prime_of_odd_classNumber`:
  its discriminant is then `-4`, `-8` or `-p` with `p ≡ 3 (mod 4)` prime.
-/

public section

open NumberField

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K]

/-- **Genus divisibility for an imaginary quadratic field.** If `K` has degree two over `ℚ` and
negative discriminant, then `2 ^ (t - 1)` divides the class number of `K`, where `t` is the number
of distinct primes dividing `disc K`. -/
theorem two_pow_card_primeFactors_discr_sub_one_dvd_classNumber
    (hK : Module.finrank ℚ K = 2) (hD : discr K < 0) :
    2 ^ ((discr K).natAbs.primeFactors.card - 1) ∣ classNumber K := by
  obtain ⟨θ, d, hmin, hgen, hsf⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  have hd : d < 0 := (isTotallyComplex_iff_neg_of_minpoly_eq_X_sq_sub_C hmin hgen).mp
    (IsTotallyComplex.of_discr_lt_zero hD hK)
  rw [← ncard_ramifiedPrimes, ← twoRank_eq_ncard_ramifiedPrimes_sub_one hmin hgen hsf hd]
  exact two_pow_classGroupTwoRank_dvd_classNumber K

/-- **An odd class number leaves one ramified prime.** If `K` has degree two over `ℚ`, negative
discriminant and odd class number, then exactly one prime divides `disc K`: at least one does,
since `|disc K| > 2`, and two would make the class number even by genus divisibility. -/
theorem card_primeFactors_discr_eq_one_of_odd_classNumber
    (hK : Module.finrank ℚ K = 2) (hD : discr K < 0) (hh : Odd (classNumber K)) :
    (discr K).natAbs.primeFactors.card = 1 := by
  have hpos : 0 < (discr K).natAbs.primeFactors.card := by
    have := abs_discr_gt_two (K := K) (by omega)
    rw [← Int.natCast_natAbs] at this
    exact Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
  by_contra hne
  exact Nat.not_even_iff_odd.mpr hh (even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega)).trans
    (two_pow_card_primeFactors_discr_sub_one_dvd_classNumber hK hD)))

/-- **Discriminants of imaginary quadratic fields of odd class number.** If `K` has degree two
over `ℚ`, negative discriminant and odd class number, then `disc K` is `-4`, `-8`, or `-p` for a
prime `p ≡ 3 (mod 4)`. -/
theorem discr_eq_neg_four_or_eq_neg_eight_or_exists_prime_of_odd_classNumber
    (hK : Module.finrank ℚ K = 2) (hD : discr K < 0) (hh : Odd (classNumber K)) :
    discr K = -4 ∨ discr K = -8 ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ discr K = -p :=
  Int.IsFundamentalDiscr.eq_neg_four_or_eq_neg_eight_or_exists_prime_of_card_primeFactors_eq_one
    (isFundamentalDiscr_discr hK) hD (card_primeFactors_discr_eq_one_of_odd_classNumber hK hD hh)

end TauCeti.Multiquadratic
