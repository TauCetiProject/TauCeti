/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.ChineseRemainder
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.OddPart

/-!
# Legendre twists of Dirichlet characters

The *Legendre twist* `DirichletCharacter.legendreTwist χ d` of a character `χ` modulo `N` by a
prime `d` is the character `n ↦ χ(n) (n / d)` modulo `N * d`, the product of `χ` and the Legendre
symbol modulo `d`, both lifted to level `N * d`. For an odd prime `d` not dividing `N` it is not
principal, whatever `χ` is.

## Main definitions

* `DirichletCharacter.legendreTwist`: the Legendre twist of a character.

## Main results

* `DirichletCharacter.legendreTwist_apply`, `DirichletCharacter.legendreTwist_apply_natCast`: its
  values.
* `DirichletCharacter.legendreTwist_apply_natCast_eq_mul_jacobiSym`: the coefficients for
  primes congruent to `7` modulo `8`, expressed with the prime in the Jacobi numerator.
* `DirichletCharacter.even_legendreTwist_iff`, `DirichletCharacter.odd_legendreTwist_iff`:
  twisting by a prime congruent to `3` modulo `4` reverses parity.
* `DirichletCharacter.legendreTwist_ne_one`: for an odd prime `d` not dividing `N`, the Legendre
  twist is not principal.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC): `New.quadTwist` in `src/Lib/General/NumberTheory/ImaginaryQuadraticField.lean`, and
`New.quadTwist_apply` and `New.quadTwist_ne_one` in `src/Lib/Analytic/EntireLFunction.lean`.
-/

public section

open scoped Nat

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

/-- The *Legendre twist* of a character `χ` modulo `N` by a prime `d`: the character
`n ↦ χ(n) (n / d)` modulo `N * d`. -/
noncomputable def legendreTwist : DirichletCharacter ℂ (N * d) :=
  χ.changeLevel (dvd_mul_right N d) *
    changeLevel (dvd_mul_left d N) ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))

/-- The Legendre twist takes the value `χ(n) (n / d)` at an integer `n`. -/
@[simp]
theorem legendreTwist_apply (n : ℤ) : χ.legendreTwist d n = χ n * legendreSym d n := by
  have h_sym : (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) n = legendreSym d n := by
    simp [legendreSym, MulChar.ringHomComp_apply]
  rw [← h_sym]
  -- Both sides vanish unless `n` is prime to `N` and to `d`; then the change of level keeps values.
  by_cases h_cop : IsCoprime n (N * d : ℕ)
  · rw [legendreTwist, MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ h_cop,
      changeLevel_eq_cast_of_dvd' _ _ h_cop]
  · rw [(apply_eq_zero_iff (χ.legendreTwist d) n).2 h_cop, zero_eq_mul, apply_eq_zero_iff,
      apply_eq_zero_iff]
    rwa [Nat.cast_mul, IsCoprime.mul_right_iff, not_and_or] at h_cop

/-- The Legendre twist takes the value `χ(n) (n / d)` at a natural number `n`. -/
@[simp]
theorem legendreTwist_apply_natCast (n : ℕ) : χ.legendreTwist d n = χ n * legendreSym d n := by
  simpa using χ.legendreTwist_apply d n

/-- On positive indices, a Legendre twist by a prime `d ≡ 7 mod 8` has coefficients
`χ(n) J(-d | n°)`, where `n°` is the odd part of `n`. -/
theorem legendreTwist_apply_natCast_eq_mul_jacobiSym {n : ℕ} (hd : d % 8 = 7) (hn : n ≠ 0) :
    χ.legendreTwist d n = χ n * jacobiSym (-(d : ℤ)) (ordCompl[2] n) := by
  rw [legendreTwist_apply_natCast, jacobiSym.legendreSym.to_jacobiSym,
    TauCeti.jacobiSym_eq_jacobiSym_neg_ordCompl_two hd hn]

/-- A Legendre twist by a prime congruent to `3` modulo `4` negates the value at `-1`. -/
theorem legendreTwist_apply_neg_one (hd : d % 4 = 3) : χ.legendreTwist d (-1) = -χ (-1) := by
  have hsym := (legendreSym.at_neg_one (p := d) (by omega)).trans
    (ZMod.χ₄_nat_three_mod_four hd)
  simpa only [Int.cast_neg, Int.cast_one, hsym, mul_neg, mul_one] using
    χ.legendreTwist_apply d (-1)

/-- Twisting by a prime congruent to `3` modulo `4` gives an even character exactly when the
original character is odd. -/
@[simp]
theorem even_legendreTwist_iff (hd : d % 4 = 3) : (χ.legendreTwist d).Even ↔ χ.Odd := by
  simp [Even, Odd, legendreTwist_apply_neg_one χ d hd, neg_eq_iff_eq_neg]

/-- Twisting by a prime congruent to `3` modulo `4` gives an odd character exactly when the
original character is even. -/
@[simp]
theorem odd_legendreTwist_iff (hd : d % 4 = 3) : (χ.legendreTwist d).Odd ↔ χ.Even := by
  simp [Even, Odd, legendreTwist_apply_neg_one χ d hd]

/-- For an odd prime `d` not dividing `N`, the Legendre twist of any character modulo `N` by `d`
is not principal. -/
theorem legendreTwist_ne_one (hd : d ≠ 2) (hN : N.Coprime d) : χ.legendreTwist d ≠ 1 := by
  -- At an integer that is `1` modulo `N` and a non-residue modulo `d`, the twist is `-1`.
  intro h_one
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod d) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨n, (hn_N : n ≡ 1 [MOD N]), (hn_d : n ≡ a.val [MOD d])⟩ := Nat.chineseRemainder hN 1 a.val
  have hn_one : (n : ZMod N) = 1 := by simpa [← ZMod.natCast_eq_natCast_iff] using hn_N
  have hn_a : (n : ZMod d) = a := by simpa [← ZMod.natCast_eq_natCast_iff] using hn_d
  have h_sym : legendreSym d n = -1 := by rw [legendreSym, Int.cast_natCast, hn_a, ha]
  have h_val : χ.legendreTwist d n = -1 := by
    rw [legendreTwist_apply_natCast, hn_one, map_one, h_sym, Int.cast_neg, Int.cast_one, one_mul]
  have h_sq : χ.legendreTwist d n * χ.legendreTwist d n = χ.legendreTwist d n := by
    rw [← MulChar.mul_apply, h_one, one_mul]
  norm_num [h_val] at h_sq

end DirichletCharacter
