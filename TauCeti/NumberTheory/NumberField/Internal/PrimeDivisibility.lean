/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Internal prime divisibility helpers

This module collects small divisibility facts used to verify coprimality hypotheses in
number-field splitting examples.
-/

public section

namespace TauCeti.NumberField.Internal

/-- A rational prime `p` different from a natural prime `l` does not divide `l`, viewed as an
integer. -/
theorem not_intCast_prime_dvd_natPrime {p l : ℕ} [Fact p.Prime]
    (hl : l.Prime) (hne : p ≠ l) : ¬ (p : ℤ) ∣ (l : ℤ) := by
  intro h
  have hp_dvd_l : p ∣ l := by exact_mod_cast h
  exact hne ((Nat.prime_dvd_prime_iff_eq Fact.out hl).mp hp_dvd_l)

end TauCeti.NumberField.Internal
