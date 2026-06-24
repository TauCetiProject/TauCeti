/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.EvenPrimeDiscriminant
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Legendre symbols of even prime discriminants

The genus-field layer of the multiquadratic roadmap normalizes the radicands of a quadratic
discriminant to **prime discriminants**. The odd prime discriminants `p* = (-1)^((p-1)/2) p`
are handled in `TauCeti.NumberTheory.Multiquadratic.LegendrePrimeDiscriminant`, where the
splitting symbol is governed by quadratic reciprocity. This file records the complementary
**even** list `-4, 8, -8` (radicands `-1, 2, -2`), whose splitting at an odd prime `q` is
governed not by reciprocity but by the supplementary laws: the quadratic characters `χ₄`,
`χ₈`, and `χ₈'` on `q`.

Concretely, for an odd prime `q`,
* `(-1 / q) = χ₄ q`, the radicand of `-4`;
* `(2 / q) = χ₈ q`, the radicand of `8`;
* `(-2 / q) = χ₈' q`, the radicand of `-8`.

Since an even prime discriminant `D` is four times its radicand and `4` is a square, the
Legendre symbol of `D` itself agrees with that of its radicand at every odd prime; this is
what lets the genus field use the prime discriminant `D` as the splitting character.

## Main results

* `TauCeti.Multiquadratic.legendreSym_evenPrimeDiscriminantRadicand` expands the Legendre
  symbol of an even prime-discriminant radicand at an odd prime as the appropriate
  supplementary character.
* `TauCeti.Multiquadratic.legendreSym_evenPrimeDiscriminant` shows that an even prime
  discriminant and its radicand have the same Legendre symbol at every odd prime.
* `legendreSym_evenPrimeDiscriminantRadicand_neg_four_eq_one_iff`,
  `..._eight_eq_one_iff`, and `..._neg_eight_eq_one_iff` give the quadratic-residue
  (splitting) conditions as congruences on `q` modulo `4` or `8`.
-/

public section

namespace TauCeti.Multiquadratic

open ZMod

variable {q : ℕ} [Fact q.Prime]

/-- The Legendre symbol of an even prime-discriminant radicand at an odd prime `q` is the
supplementary character attached to that discriminant: `χ₄ q` for `-4` (radicand `-1`),
`χ₈ q` for `8` (radicand `2`), and `χ₈' q` for `-8` (radicand `-2`). -/
theorem legendreSym_evenPrimeDiscriminantRadicand {D : ℤ} (hD : IsEvenPrimeDiscriminant D)
    (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand D) =
      if D = -4 then χ₄ q else if D = 8 then χ₈ q else χ₈' q := by
  rcases hD with rfl | rfl | rfl
  · rw [evenPrimeDiscriminantRadicand_neg_four, if_pos rfl, legendreSym.at_neg_one hq]
  · rw [evenPrimeDiscriminantRadicand_eight, if_neg (by norm_num), if_pos rfl,
      legendreSym.at_two hq]
  · rw [evenPrimeDiscriminantRadicand_neg_eight, if_neg (by norm_num), if_neg (by norm_num),
      legendreSym.at_neg_two hq]

/-- An even prime discriminant `D` and its radicand `D / 4` have the same Legendre symbol at
every odd prime `q`: they differ by the square factor `4`, which contributes a trivial
symbol. This is the form used by the genus-field splitting law, where the prime discriminant
`D` itself is the splitting character. -/
theorem legendreSym_evenPrimeDiscriminant {D : ℤ} (hD : IsEvenPrimeDiscriminant D)
    (hq : q ≠ 2) :
    legendreSym q D = legendreSym q (evenPrimeDiscriminantRadicand D) := by
  have h2 : ((2 : ℤ) : ZMod q) ≠ 0 := by
    rw [show ((2 : ℤ) : ZMod q) = ((2 : ℕ) : ZMod q) by norm_cast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  conv_lhs => rw [evenPrimeDiscriminant_eq_four_mul_radicand hD, show (4 : ℤ) = 2 ^ 2 by norm_num]
  rw [legendreSym.mul, legendreSym.sq_one' q h2, one_mul]

/-- The radicand `-1` of the prime discriminant `-4` is a quadratic residue modulo an odd
prime `q` exactly when `q ≡ 1 (mod 4)`; equivalently `q` splits in `ℚ(√-1) = ℚ(i)`. -/
theorem legendreSym_evenPrimeDiscriminantRadicand_neg_four_eq_one_iff (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand (-4)) = 1 ↔ q % 4 = 1 := by
  have hne : ((-1 : ℤ) : ZMod q) ≠ 0 := by
    rw [show ((-1 : ℤ) : ZMod q) = -1 by push_cast; ring]
    exact neg_ne_zero.mpr one_ne_zero
  rw [evenPrimeDiscriminantRadicand_neg_four, legendreSym.eq_one_iff q hne,
    show ((-1 : ℤ) : ZMod q) = -1 by push_cast; ring, ZMod.exists_sq_eq_neg_one_iff]
  have hodd : q % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hq
  rcases Nat.odd_mod_four_iff.mp hodd with h | h <;> rw [h] <;> decide

/-- The radicand `2` of the prime discriminant `8` is a quadratic residue modulo an odd
prime `q` exactly when `q ≡ 1` or `7 (mod 8)`; equivalently `q` splits in `ℚ(√2)`. -/
theorem legendreSym_evenPrimeDiscriminantRadicand_eight_eq_one_iff (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand 8) = 1 ↔ q % 8 = 1 ∨ q % 8 = 7 := by
  have hne : ((2 : ℤ) : ZMod q) ≠ 0 := by
    rw [show ((2 : ℤ) : ZMod q) = ((2 : ℕ) : ZMod q) by norm_cast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  rw [evenPrimeDiscriminantRadicand_eight, legendreSym.eq_one_iff q hne,
    show ((2 : ℤ) : ZMod q) = (2 : ZMod q) by push_cast; ring, ZMod.exists_sq_eq_two_iff hq]

/-- The radicand `-2` of the prime discriminant `-8` is a quadratic residue modulo an odd
prime `q` exactly when `q ≡ 1` or `3 (mod 8)`; equivalently `q` splits in `ℚ(√-2)`. -/
theorem legendreSym_evenPrimeDiscriminantRadicand_neg_eight_eq_one_iff (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand (-8)) = 1 ↔ q % 8 = 1 ∨ q % 8 = 3 := by
  have hne : ((-2 : ℤ) : ZMod q) ≠ 0 := by
    rw [show ((-2 : ℤ) : ZMod q) = -((2 : ℕ) : ZMod q) by push_cast; ring, neg_ne_zero, Ne,
      ZMod.natCast_eq_zero_iff]
    exact fun hdvd => hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  rw [evenPrimeDiscriminantRadicand_neg_eight, legendreSym.eq_one_iff q hne,
    show ((-2 : ℤ) : ZMod q) = (-2 : ZMod q) by push_cast; ring, ZMod.exists_sq_eq_neg_two_iff hq]

/-- **Worked example.** The radicand `-2` of `-8` is a quadratic residue modulo `3`
(since `3 ≡ 3 (mod 8)`): the prime `3` splits in `ℚ(√-2)`. -/
theorem legendreSym_three_evenPrimeDiscriminantRadicand_neg_eight :
    legendreSym 3 (evenPrimeDiscriminantRadicand (-8)) = 1 :=
  (legendreSym_evenPrimeDiscriminantRadicand_neg_eight_eq_one_iff (by norm_num)).mpr (by norm_num)

/-- **Worked example.** The radicand `2` of `8` is *not* a quadratic residue modulo `3`
(since `3 ∉ {1, 7} (mod 8)`): the prime `3` is inert or ramified, not split, in `ℚ(√2)`. -/
theorem legendreSym_three_evenPrimeDiscriminantRadicand_eight_ne_one :
    legendreSym 3 (evenPrimeDiscriminantRadicand 8) ≠ 1 := by
  intro h
  rw [legendreSym_evenPrimeDiscriminantRadicand_eight_eq_one_iff (q := 3) (by norm_num)] at h
  exact absurd h (by decide)

end TauCeti.Multiquadratic
