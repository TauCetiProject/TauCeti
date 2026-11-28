/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.Data.ZMod.DyadicOrder

/-!
# Orders of exceptional prime labels

When the chain length is `2^e`, an exceptional prime avoids both `1` and `-1` modulo `2^e`.
At the cyclotomic tower level `q₁(22e)`, its signed label then has order divisible by the
chain length. This divisibility persists when taking the odd power that defines the step
of the Frobenius cycle over a marked prime.

The order bound is the one used in `New.Data.IsExceptional.m_dvd_orderOf` in lsernau/grh-lean
(`grh/src/New/UpperBound/Divisibility/MarkedPrimes.lean`, revision `72fead1`).
-/

public section

namespace TauCeti.OneSidedBound.Parameters

/-- If `p` avoids both signs of `1` modulo the chain length `2^e`, then the order of the
signed residue at `q₁(22e)`, even after raising to any odd power, is divisible by `2^e`.
For an exceptional prime this applies to the signed label itself and to the odd step
exponent of its orbit inside the residue class `1` modulo `q₀`. -/
theorem two_pow_dvd_orderOf_neg_natCast_pow_q₁ (P : Parameters) {p e r : ℕ}
    (hminus : ¬ 2 ^ e ∣ p - 1) (hplus : ¬ 2 ^ e ∣ p + 1) (hr : Odd r) :
    2 ^ e ∣ orderOf ((-(p : ZMod (P.q₁ (22 * e)))) ^ r) := by
  let u := -(p : ZMod (P.q₁ (22 * e)))
  have hlevel : 2 ^ (e + e) ∣ P.q₁ (22 * e) :=
    (pow_dvd_pow 2 (by omega)).trans (P.two_pow_succ_dvd_q₁ (22 * e))
  have hord : 2 ^ e ∣ orderOf u :=
    (pow_dvd_pow 2 (Nat.le_succ e)).trans
      (ZMod.two_pow_succ_dvd_orderOf_neg_natCast hlevel hminus hplus)
  have hprod : orderOf u ∣ r * orderOf (u ^ r) :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
  exact (hr.coprime_two_left.pow_left e).dvd_of_dvd_mul_left (hord.trans hprod)

end TauCeti.OneSidedBound.Parameters
