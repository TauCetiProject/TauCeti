/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol

/-!
# Quadratic reciprocity at a denominator congruent to seven modulo eight

For `d ≡ 7 mod 8`, the twist coefficient `J(n | d)` at positive `n` can be viewed as the
Jacobi symbol with numerator `-d` and the odd part of `n` as denominator. This is the
form in which one can apply character-sum bounds over the twist parameter `d`.

For prime `d` this is `New.legendreSym_eq_jacobiSym_ordCompl` in
`Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open scoped Nat

namespace TauCeti

/-- At a denominator `d ≡ 7 mod 8`, removing the two-part of a nonzero numerator and
applying quadratic reciprocity exchanges the arguments with a sign on `d`. -/
theorem jacobiSym_eq_jacobiSym_neg_ordCompl_two {d n : ℕ}
    (hd : d % 8 = 7) (hn : n ≠ 0) :
    jacobiSym n d = jacobiSym (-(d : ℤ)) (ordCompl[2] n) := by
  have hfour : -(d : ℤ) ≡ 1 [ZMOD 4] := by
    simpa [Int.ModEq] using (by omega : (-(d : ℤ)) % 4 = 1)
  have htwo : ZMod.χ₈ (Int.cast (R := ZMod 8) (-(d : ℤ))) = 1 := by
    rw [ZMod.χ₈_int_eq_if_mod_eight]
    omega
  calc
    _ = kroneckerSym (-(d : ℤ)) n := by
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
        (kroneckerSym_eq_jacobiSym_natAbs hfour (n : ℤ)).symm
    _ = _ := by
      rw [kroneckerSym_of_ne_zero _ (Int.natCast_ne_zero.mpr hn), htwo]
      simp

end TauCeti
