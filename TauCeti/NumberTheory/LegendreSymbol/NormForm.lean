/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Integers of the shape `(x² - D y²) / 4` modulo a prime dividing `D`

If `4n = x² - D y²` and an odd prime `p` divides `D` but not `n`, then reducing modulo `p` leaves
`4n ≡ x²`, so `n` is a nonzero quadratic residue modulo `p`. This is the shape in which the norm of
an algebraic integer of a quadratic field is used arithmetically, and it is shared by the
genus-character relation and by the norm obstructions of quadratic fields.

## Main results

* `TauCeti.jacobiSym_eq_one_of_dvd_of_four_mul_eq_sq_sub_mul_sq`: `jacobiSym n p = 1` for such
  `n` and `p`.
-/

public section

namespace TauCeti

/-- **An integer of the shape `(x² - D y²) / 4` is a residue modulo an odd prime dividing `D`.**
If an odd prime `p` divides `D` but not `n`, and `4n = x² - D y²`, then `n` is a nonzero quadratic
residue modulo `p`: reducing the hypothesis modulo `p` kills the `D y²` term and leaves `4n ≡ x²`,
so `n` is the square of `x / 2`. -/
theorem jacobiSym_eq_one_of_dvd_of_four_mul_eq_sq_sub_mul_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D n x y : ℤ} (hpD : (p : ℤ) ∣ D) (hpn : ¬ (p : ℤ) ∣ n)
    (h : 4 * n = x ^ 2 - D * y ^ 2) : jacobiSym n p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hdvd : ¬ ((p : ℤ) ∣ 2) := fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast hdvd))
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).not.mpr hdvd
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  refine (legendreSym.eq_one_iff p hn0).mpr ⟨(x : ZMod p) * 2⁻¹, ?_⟩
  have hD0 : (D : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpD
  have h4 : (4 : ZMod p) * (n : ZMod p) = (x : ZMod p) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod p)) h
    push_cast at hcast
    rw [hD0] at hcast
    simpa using hcast
  field_simp
  linear_combination h4

end TauCeti
