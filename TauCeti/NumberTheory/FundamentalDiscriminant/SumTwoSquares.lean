/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.FundamentalDiscriminant.Basic
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Positive fundamental discriminants as sums of two squares

The absence of prime divisors congruent to `3` modulo `4` characterizes the positive
fundamental discriminants that are sums of two integer squares.
-/

public section

namespace Int

/-- A positive fundamental discriminant is a sum of two integer squares exactly when it has no
prime divisor congruent to `3` modulo `4`. This follows from Mathlib's valuation criterion
`Nat.eq_sq_add_sq_iff` and is used in Duke, Imamoglu and Toth,
*Geometric invariants for real quadratic fields*, §4, p. 960. -/
theorem IsFundamentalDiscr.exists_sq_add_sq_iff {D : ℤ} (hD : IsFundamentalDiscr D)
    (hpos : 0 < D) :
    (∃ x y : ℤ, D = x ^ 2 + y ^ 2) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ D → p % 4 ≠ 3 := by
  have hcast : (D.natAbs : ℤ) = D := Int.natAbs_of_nonneg hpos.le
  have hD0 : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hpos.ne'
  have hrepr : (∃ x y : ℤ, D = x ^ 2 + y ^ 2) ↔ (∃ x y : ℕ, D.natAbs = x ^ 2 + y ^ 2) := by
    constructor
    · rintro ⟨x, y, h⟩
      refine ⟨x.natAbs, y.natAbs, ?_⟩
      exact_mod_cast (by simpa only [Int.natCast_natAbs, sq_abs, hcast] using h :
        (D.natAbs : ℤ) = (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2)
    · rintro ⟨x, y, h⟩
      exact ⟨x, y, hcast.symm.trans (by exact_mod_cast h)⟩
  rw [hrepr, Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp hpD hp3
    have hpD' : p ∣ D.natAbs := Int.natCast_dvd.mp hpD
    have heven := h p (Nat.mem_primeFactors.mpr ⟨hp, hpD', hD0⟩) hp3
    have hge : 1 ≤ multiplicity p D.natAbs :=
      (Nat.pow_dvd_iff_le_multiplicity (k := 1) hp.ne_one hD0).mp (by simpa using hpD')
    -- A positive even valuation would make the square of this odd prime divide the discriminant.
    rw [Nat.padicValNat_def, Nat.even_iff] at heven
    have hsq : p ^ 2 ∣ D.natAbs :=
      (Nat.pow_dvd_iff_le_multiplicity hp.ne_one hD0).mpr (by omega)
    have hsqD : (p : ℤ) ^ 2 ∣ D := by
      rw [← hcast]
      exact_mod_cast hsq
    exact (isFundamentalDiscr_def.mp hD).2.2 p hp (Nat.odd_iff.mpr (by omega)) hsqD
  · intro h p hp hp3
    obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
    exact (h p hprime (Int.natCast_dvd.mpr hdvd) hp3).elim

end Int
