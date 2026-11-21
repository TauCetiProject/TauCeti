/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiplicity
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The Adams–Atiyah coefficient equation

The integer coefficient equation
`3 ^ r * (3 ^ r - 1) * b₂ = 2 ^ r * (2 ^ r - 1) * b₃` with odd `b₂` forces
`2 ^ r ∣ 3 ^ r - 1`, hence `r = 1, 2, 4` for positive `r`.

This is the arithmetic step in the Adams–Atiyah exclusion of odd Hopf invariant:
commuting the second and third Adams operations produces the coefficient equation.
No K-theory or Hopf-invariant comparison is asserted here.

## References

J. F. Adams and M. F. Atiyah, *K-theory and the Hopf invariant*,
Quart. J. Math. Oxford (2) 17 (1966), 31–38.
-/

public section

namespace TauCeti

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
  -- `exact_mod_cast` needs this bound to transport truncated natural subtraction.
  have hle : 1 ≤ (3 : ℕ) ^ r := Nat.one_le_pow _ _ (by decide)
  exact_mod_cast hdvd'

/-- For a positive exponent, the Adams-operation coefficient equation with odd `b₂`
allows only `r = 1, 2, 4`. -/
theorem eq_one_or_eq_two_or_eq_four_of_odd_mul_eq {r : ℕ} {b₂ b₃ : ℤ}
    (hr : 0 < r) (hb₂ : Odd b₂)
    (h : (3 : ℤ) ^ r * (3 ^ r - 1) * b₂ = 2 ^ r * (2 ^ r - 1) * b₃) :
    r = 1 ∨ r = 2 ∨ r = 4 := by
  have := Nat.two_pow_dvd_three_pow_sub_one_iff.mp
    (two_pow_dvd_three_pow_sub_one_of_odd_mul_eq hb₂ h)
  omega

end TauCeti
