/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Factorial

/-!
# Paying for the factorial cost of long theta rows

Let `A` be the mean of the logarithms of the place weights, `B = log(M rd_E / (2π))`, and `c`
the constant term of the signed prime sum at modulus one. The logarithmic cost of a row of
length `a` is `log(a!) + a (B + 1 + c)`, whereas the expected prime sum is
`a (log a - A + c)`. Their difference does not depend on `c`. Stirling's bound leaves a leading
cost of `a (A + B)` and a half-logarithmic error. For `m` lifts, the character at the level prime
pays `a log N`, with `log N` chosen above `m A + (m - 1) B - (15/2) log b`.

The normalization and constants are those of `New.Data.jetSize_sub_mainPrimeSum_le` and
`New.Data.mul_jetSize_sub_mainPrimeSum_sub_le` in lsernau/grh-lean (`72fead1`,
`grh/src/New/UpperBound/Size/ArchimedeanSize.lean`).
-/

public section

namespace TauCeti.OneSidedBound

open Real

/-- The excess of the logarithmic row cost over the expected prime sum is at most
`a (A + B) + 1 + log a / 2`, independently of the common constant `c`. -/
theorem jetSize_sub_mainPrimeSum_le (a : ℕ) (A B c : ℝ) :
    (log (a.factorial : ℝ) + a * (B + 1 + c)) - a * (log a - A + c) ≤
      a * (A + B) + 1 + log a / 2 := by
  linarith [log_factorial_le a]

/-- After subtracting the level contribution `a * logN`, the excess for `m` rows is at most
`32 * a * L`, where `L = log b`. Only the lower endpoint of the window for `logN` is needed. -/
theorem mul_jetSize_sub_mainPrimeSum_sub_le {a m : ℕ} {A B c L logN : ℝ}
    (hm : m ≤ a) (hL : 2 ≤ L) (ha : log a ≤ 2 * L) (hB : B ≤ 23 * L)
    (hN : (m : ℝ) * A + ((m : ℝ) - 1) * B - 15 / 2 * L ≤ logN) :
    m * ((log (a.factorial : ℝ) + a * (B + 1 + c)) - a * (log a - A + c)) - a * logN ≤
      32 * a * L := by
  have hm' : (m : ℝ) ≤ a := by exact_mod_cast hm
  have herror : (m : ℝ) * (1 + log a / 2) ≤ a * (3 / 2 * L) :=
    (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg m)).trans
      (mul_le_mul_of_nonneg_right hm' (by linarith))
  have hexcess := mul_le_mul_of_nonneg_left (jetSize_sub_mainPrimeSum_le a A B c)
    (Nat.cast_nonneg m : 0 ≤ (m : ℝ))
  have hlevel := mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg a)
  have hfactor := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg a)
  -- The mean log weight cancels altogether; only one copy of the level factor remains.
  linarith only [hexcess, hlevel, hfactor, herror]

end TauCeti.OneSidedBound
