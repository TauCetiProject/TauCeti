/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The quadratic symbol with a prime denominator, in the convention of Skorobogatov–Sofos

For an integer `a` and a natural number `p`, the symbol `primeDenominatorSymbol a p` is the Jacobi
symbol `J(a | p)` when `p ≠ 2`, and at `p = 2` it is `0` for even `a` and `1` for odd `a`. For a
prime `p` it is therefore `0` exactly when `p ∣ a`, including at `p = 2`, and it is completely
multiplicative in `a`. At `p = 2` this is not the Kronecker symbol, which takes the value `-1` at
`a ≡ ±3 (mod 8)`.

Mathlib's `jacobiSym a 2` already has the same values, so the symbol defined here is equal to
`jacobiSym a p` for every `a` and `p` (`primeDenominatorSymbol_eq_jacobiSym`). The definition
records the convention with its parity branch explicit, under the name the sieve roadmap uses;
every law below is the corresponding law of the Jacobi symbol.

## Main definitions

* `TauCeti.SieveQuadratic.primeDenominatorSymbol a p`.

## Main results

* `TauCeti.SieveQuadratic.primeDenominatorSymbol_eq_jacobiSym`,
  `TauCeti.SieveQuadratic.primeDenominatorSymbol_eq_legendreSym`: it is the Jacobi symbol at every
  denominator, and the Legendre symbol at every prime.
* `TauCeti.SieveQuadratic.primeDenominatorSymbol_two`: at `2` it is the indicator of odd `a`.
* `TauCeti.SieveQuadratic.abs_primeDenominatorSymbol_le_one`: its absolute value is at most `1`.
* `TauCeti.SieveQuadratic.primeDenominatorSymbol_mul`: it is multiplicative in the numerator.
* `TauCeti.SieveQuadratic.primeDenominatorSymbol_eq_zero_iff`: at a prime `p` it vanishes exactly
  when `p ∣ a`.

## References

* A. N. Skorobogatov and E. Sofos, *Schinzel Hypothesis on average and rational points*,
  Invent. Math. 231 (2023), §6, the convention preceding Lemma 6.3, pp. 725–726.
-/

public section

namespace TauCeti.SieveQuadratic

variable {a b : ℤ} {p : ℕ}

/-- The quadratic symbol with denominator `p` in the convention of Skorobogatov–Sofos: the Jacobi
symbol `J(a | p)` for `p ≠ 2`, and at `p = 2` the value `0` for even `a` and `1` for odd `a`. -/
def primeDenominatorSymbol (a : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then (if Even a then 0 else 1) else jacobiSym a p

/-- At `2` the symbol is `0` for even `a` and `1` for odd `a`. -/
theorem primeDenominatorSymbol_two (a : ℤ) :
    primeDenominatorSymbol a 2 = if Even a then 0 else 1 :=
  ite_eq_left rfl

/-- **The symbol is Mathlib's Jacobi symbol at every denominator.** The parity branch at `2` in
the definition agrees with `jacobiSym a 2`, by `TauCeti.jacobiSym_two_right`. -/
theorem primeDenominatorSymbol_eq_jacobiSym (a : ℤ) (p : ℕ) :
    primeDenominatorSymbol a p = jacobiSym a p := by
  rcases eq_or_ne p 2 with rfl | hp
  · rw [primeDenominatorSymbol_two, jacobiSym_two_right]
  · exact ite_eq_right hp

/-- At a prime, odd or not, the symbol is the Legendre symbol. -/
theorem primeDenominatorSymbol_eq_legendreSym [Fact p.Prime] (a : ℤ) :
    primeDenominatorSymbol a p = legendreSym p a := by
  rw [primeDenominatorSymbol_eq_jacobiSym, jacobiSym.legendreSym.to_jacobiSym]

/-- At `2` the symbol of an even integer is `0`. -/
theorem primeDenominatorSymbol_two_of_even (ha : Even a) : primeDenominatorSymbol a 2 = 0 := by
  rw [primeDenominatorSymbol_two, ite_eq_left ha]

/-- At `2` the symbol of an odd integer is `1`. -/
theorem primeDenominatorSymbol_two_of_odd (ha : Odd a) : primeDenominatorSymbol a 2 = 1 := by
  rw [primeDenominatorSymbol_two, ite_eq_right (Int.not_even_iff_odd.2 ha)]

/-- The symbol takes only the values `0`, `1` and `-1`. -/
theorem primeDenominatorSymbol_trichotomy (a : ℤ) (p : ℕ) :
    primeDenominatorSymbol a p = 0 ∨ primeDenominatorSymbol a p = 1 ∨
      primeDenominatorSymbol a p = -1 := by
  rw [primeDenominatorSymbol_eq_jacobiSym]
  exact jacobiSym.trichotomy a p

/-- The absolute value of the symbol is at most `1`. -/
theorem abs_primeDenominatorSymbol_le_one (a : ℤ) (p : ℕ) : |primeDenominatorSymbol a p| ≤ 1 := by
  rcases primeDenominatorSymbol_trichotomy a p with h | h | h <;> rw [h] <;> decide

/-- The symbol is multiplicative in the numerator, for every denominator. -/
theorem primeDenominatorSymbol_mul (a b : ℤ) (p : ℕ) :
    primeDenominatorSymbol (a * b) p = primeDenominatorSymbol a p * primeDenominatorSymbol b p := by
  simp only [primeDenominatorSymbol_eq_jacobiSym, jacobiSym.mul_left]

/-- At a prime `p`, the symbol of `a` vanishes exactly when `p` divides `a`, including at
`p = 2`. -/
theorem primeDenominatorSymbol_eq_zero_iff (hp : p.Prime) :
    primeDenominatorSymbol a p = 0 ↔ (p : ℤ) ∣ a := by
  have := Fact.mk hp
  rw [primeDenominatorSymbol_eq_legendreSym, legendreSym.eq_zero_iff,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-! ### Examples -/

/-- `3` is odd, so its symbol at `2` is `1`; the Kronecker symbol of `3` at `2` is `-1`. -/
example : primeDenominatorSymbol 3 2 = 1 := primeDenominatorSymbol_two_of_odd (by decide)

/-- `6` is even, so its symbol at `2` is `0`. -/
example : primeDenominatorSymbol 6 2 = 0 := primeDenominatorSymbol_two_of_even (by decide)

/-- `2` is a nonresidue modulo `3`. -/
example : primeDenominatorSymbol 2 3 = -1 := by
  rw [primeDenominatorSymbol_eq_jacobiSym]
  norm_num

/-- `3 ∣ 9`, so the symbol of `9` at `3` is `0`. -/
example : primeDenominatorSymbol 9 3 = 0 :=
  (primeDenominatorSymbol_eq_zero_iff Nat.prime_three).2 (by norm_num)

end TauCeti.SieveQuadratic
