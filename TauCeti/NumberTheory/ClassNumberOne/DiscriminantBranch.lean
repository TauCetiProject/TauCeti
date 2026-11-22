/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character

/-!
# Inert-at-two, ramified-at-three discriminant branch for class number one

In Heegner's and Stark's proof of the imaginary quadratic class number one theorem, the remaining
branch concerns fundamental discriminants `D` for which `2` is inert (`χ_D(2) = -1`) and `3`
ramifies (`χ_D(3) = 0`), namely `D ≡ 21 (mod 24)`.

## Main results

* `TauCeti.Multiquadratic.fundamentalDiscriminantChar_two_eq_neg_one_and_three_eq_zero_iff`:
  `fundamentalDiscriminantChar D hD 2 = -1 ∧ fundamentalDiscriminantChar D hD 3 = 0 ↔ D % 24 = 21`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §§3.B, 7, 12.
* H. M. Stark, *A complete determination of the complex quadratic fields of class number one*,
  Michigan Math. J. 14 (1967), 1–27.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§4–5.
-/

public section

namespace TauCeti.Multiquadratic

/-- The fundamental-discriminant character satisfies `χ_D(2) = -1` and `χ_D(3) = 0` iff
`D ≡ 21 (mod 24)` (the inert-two, ramified-three CM branch). -/
theorem fundamentalDiscriminantChar_two_eq_neg_one_and_three_eq_zero_iff {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantChar D hD 2 = -1 ∧ fundamentalDiscriminantChar D hD 3 = 0 ↔
      D % 24 = 21 := by
  have h2 := fundamentalDiscriminantChar_two_eq_neg_one_iff hD
  have h3 : fundamentalDiscriminantChar D hD 3 = 0 ↔ D % 3 = 0 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := fundamentalDiscriminantChar_natCast_eq_legendreSym hD (q := 3) (by decide)
    rw [show ((3 : ℕ) : ℤ) = 3 by rfl, Int.cast_ofNat] at h
    rw [h, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    norm_cast
  rw [h2, h3]
  omega

end TauCeti.Multiquadratic
