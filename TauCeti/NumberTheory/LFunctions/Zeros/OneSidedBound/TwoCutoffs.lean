/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# One-sided prime remainder bound from the two-cutoff identity

The total remainder for a prime sum with two cutoffs combines the short-cutoff remainder `R`
with the two remainders `Rq` and `R₁` at the large cutoff. An upper bound on the total gives
an upper bound on `R`. The ratio of the two place counts costs one power of `log b`, so a
fifth power of `log b` in the total bound gives a sixth power in the individual bound.

The identity and normalization are those of `New.Data.primeRemainder_le` in lsernau/grh-lean,
`grh/src/New/Reduction/OneSidedBound.lean` at `72fead1`.
-/

public section

namespace TauCeti

/-- Extract the short-cutoff bound from the two-cutoff identity and an upper bound for the total
remainder. Here `A` and `B` are the two place counts, `C` is the totient of the modulus, and `L`
is `log b`. The large-cutoff terms may have either sign. -/
theorem primeRemainder_le_of_two_cutoff_identity {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {a m A B C L R Rq R₁ rem : 𝕜} (ha : 0 < a) (hm : 0 < m) (hA : 0 ≤ A)
    (hB : 0 < B) (hC : 0 ≤ C) (hshare : A ≤ B * L)
    (hrem : rem = a * (B * (R - Rq) + A * R₁)) (hmain : m * rem ≤ C * A * a * L ^ 5) :
    R ≤ C * L ^ 6 / m + |Rq| + L * |R₁| := by
  have hratio : A / B ≤ L := (div_le_iff₀ hB).mpr (by simpa [mul_comm] using hshare)
  have hL : 0 ≤ L := (div_nonneg hA hB.le).trans hratio
  have htotal : rem / (a * B) ≤ C * L ^ 6 / m := calc
    _ ≤ (C * A * a * L ^ 5 / m) / (a * B) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hm).mpr (by simpa [mul_comm] using hmain))
        (mul_nonneg ha.le hB.le)
    _ = C * (A / B) * L ^ 5 / m := by
      field_simp [ha.ne', hB.ne', hm.ne']
    _ ≤ C * L ^ 6 / m := by
      rw [pow_succ' L 5, ← mul_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) (pow_nonneg hL _)) hm.le
  have hR : R = rem / (a * B) + Rq + (A / B) * (-R₁) := by
    rw [hrem]
    field_simp [ha.ne', hB.ne']
    ring
  rw [hR]
  exact add_le_add (add_le_add htotal (le_abs_self _))
    ((mul_le_mul_of_nonneg_left (neg_le_abs _) (div_nonneg hA hB.le)).trans
      (mul_le_mul_of_nonneg_right hratio (abs_nonneg _)))

end TauCeti
