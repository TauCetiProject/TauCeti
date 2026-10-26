/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Vanishing of the `p`-adic valuation of a rational number

This file characterises when the `p`-adic valuation of a nonzero rational number vanishes.

## Main results

* `TauCeti.padicValRat_eq_zero_iff`: a nonzero rational number has `p`-adic valuation zero
  exactly when `p` divides neither its numerator nor its denominator.
-/

public section

namespace TauCeti

/-- A nonzero rational number has `p`-adic valuation zero exactly when the prime `p` divides
neither its numerator nor its denominator. -/
theorem padicValRat_eq_zero_iff {p : ℕ} [hp : Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    padicValRat p q = 0 ↔ ¬ p ∣ q.num.natAbs ∧ ¬ p ∣ q.den := by
  have hnum : padicValInt p q.num = 0 ↔ ¬ p ∣ q.num.natAbs := by
    simp [padicValInt, padicValNat.eq_zero_iff, hp.out.ne_one, hq]
  have hden : padicValNat p q.den = 0 ↔ ¬ p ∣ q.den := by
    simp [padicValNat.eq_zero_iff, hp.out.ne_one]
  rw [padicValRat_def, ← hnum, ← hden]
  rcases Rat.num_or_den_zero_padicVal q hp.out with h | h <;> simp [h]

end TauCeti
