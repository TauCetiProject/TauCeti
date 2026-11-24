/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.Coprime

/-!
# Integers of the shape `(x² - D y²) / 4` modulo a divisor of `D`

If `4n = x² - D y²` and a prime `p` divides `D` but not `n`, then, for odd `p`, reducing modulo `p`
leaves `4n ≡ x²`, so `n` is a nonzero quadratic residue modulo `p`; this also holds for `p = 2`.
By multiplicativity of the Jacobi symbol in its lower argument, `J(n | b) = 1` for every natural
number `b` dividing `D` and coprime to `n`. This is the shape in which the norm of an algebraic
integer of a quadratic field is used arithmetically, and it is shared by the genus-character
relation and by the norm obstructions of quadratic fields.

## Main results

* `TauCeti.jacobiSym_eq_one_of_dvd_of_four_mul_eq_sq_sub_mul_sq`: `jacobiSym n b = 1` for such
  `n` and `b`.
-/

public section

namespace TauCeti

/-- **An integer of the shape `(x² - D y²) / 4` has Jacobi symbol `1` modulo every divisor of `D`
coprime to it.** If a natural number `b` divides `D`, `n` is coprime to `b`, and
`4n = x² - D y²`, then `J(n | b) = 1`. For a prime `b` this says that `n` is a nonzero quadratic
residue modulo `b`. -/
theorem jacobiSym_eq_one_of_dvd_of_four_mul_eq_sq_sub_mul_sq {b : ℕ} {D n x y : ℤ}
    (hbD : (b : ℤ) ∣ D) (hbn : n.gcd b = 1) (h : 4 * n = x ^ 2 - D * y ^ 2) :
    jacobiSym n b = 1 := by
  have key : ∀ z : ZMod 2, z ≠ 0 → IsSquare z := by decide
  -- the Jacobi symbol is multiplicative in `b`, so it suffices to treat a prime factor `p`
  induction b using induction_on_primes with
  | zero => exact jacobiSym.zero_right n
  | one => exact jacobiSym.one_right n
  | prime_mul p a hp ih =>
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rw [Nat.cast_mul] at hbD hbn
    rw [jacobiSym.mul_right' n hp.ne_zero ha,
      ih (dvd_of_mul_left_dvd hbD) (Int.gcd_eq_one_of_gcd_mul_right_eq_one_right hbn), mul_one]
    have : Fact p.Prime := ⟨hp⟩
    have hn0 : (n : ZMod p) ≠ 0 :=
      ZMod.ne_zero_of_gcd_eq_one hp (Int.gcd_eq_one_of_gcd_mul_right_eq_one_left hbn)
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    rcases eq_or_ne p 2 with rfl | hp2
    · exact (legendreSym.eq_one_iff 2 hn0).mpr (key _ hn0)
    have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have hD0 : (D : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_of_mul_right_dvd hbD)
    have h4 : (4 : ZMod p) * n = x ^ 2 := by
      simpa [hD0] using congrArg (Int.cast : ℤ → ZMod p) h
    -- `x² - n · 2² = 0` modulo `p`, so `n` is the square of `x / 2`
    exact legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero hn0 (x := (x : ZMod p)) h2
      (by linear_combination -h4)

end TauCeti
