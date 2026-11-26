/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Jacobi reciprocity at denominators congruent to `7` modulo `8`

For `d ≡ 7 (mod 8)`, the Jacobi symbol `J(n | d)` is `J(-d | n°)`, where `n°` is the odd part
of the positive integer `n`. In particular this rewrites the Legendre coefficients of a
quadratic twist with prime `d`, so that averaging over the twisting primes varies the
*numerator* of a Jacobi symbol with fixed odd denominator.

The prime case is `New.legendreSym_eq_jacobiSym_ordCompl` in
`Lib/Analytic/QuadraticTwist.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

namespace TauCeti

/-- For `d ≡ 7 (mod 8)` and `n ≠ 0`, the symbol `J(n | d)` equals `J(-d | ordCompl[2] n)`.
The equality includes the case where `n` and `d` are not coprime. -/
theorem jacobiSym_eq_jacobiSym_neg_ordCompl_of_mod_eight {d n : ℕ} (hd : d % 8 = 7)
    (hn : n ≠ 0) : jacobiSym n d = jacobiSym (-(d : ℤ)) (ordCompl[2] n) := by
  have hdOdd : Odd d := Nat.odd_iff.mpr (by omega)
  have htwo : jacobiSym 2 d = 1 := by
    rw [jacobiSym.at_two hdOdd, ZMod.χ₈_nat_mod_eight, hd]
    decide
  have hOdd : Odd (ordCompl[2] n) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))
  have hneg : (-(d : ℤ)) % 4 = 1 := by omega
  calc
    jacobiSym n d = jacobiSym (↑(ordCompl[2] n) : ℤ) d := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n 2]
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, jacobiSym.mul_left, jacobiSym.pow_left,
        htwo, one_pow, one_mul]
    _ = jacobiSym (-(d : ℤ)) (ordCompl[2] n) := by
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
        (jacobiSym_eq_jacobiSym_natAbs_of_emod_four_eq_one hneg hOdd).symm

end TauCeti
