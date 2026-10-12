/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# The Legendre symbol `(5 | p)`

Since `5 ≡ 1 (mod 4)`, quadratic reciprocity gives `(5 | p) = (p | 5)` for every odd prime `p`,
and the nonzero squares modulo `5` are `1` and `4`. Hence `5` is a nonzero square modulo an odd
prime `p` exactly when `p ≡ ±1 (mod 5)`; at `p = 5` the symbol is `0`.

## Main results

* `TauCeti.ZMod.isSquare_natCast_mod_five_iff_eq_one_or_eq_four`: the nonzero squares in
  `ZMod 5` are `1` and `4`.
* `TauCeti.legendreSym_five_eq_one_iff`: for an odd prime `p`, `legendreSym p 5 = 1` if and
  only if `p % 5 = 1 ∨ p % 5 = 4`.
-/

public section

namespace TauCeti

/-- The nonzero squares in `ZMod 5` are `1` and `4`. -/
theorem ZMod.isSquare_natCast_mod_five_iff_eq_one_or_eq_four {r : ℕ} (hlt : r < 5) (hr0 : r ≠ 0) :
    IsSquare ((r : ℕ) : ZMod 5) ↔ r = 1 ∨ r = 4 := by
  interval_cases r
  · exact absurd rfl hr0
  · exact ⟨fun _ => by simp, fun _ => ⟨1, by decide⟩⟩
  · refine ⟨fun ⟨a, ha⟩ => ?_, by simp⟩
    fin_cases a <;> exact absurd ha (by decide)
  · refine ⟨fun ⟨a, ha⟩ => ?_, by simp⟩
    fin_cases a <;> exact absurd ha (by decide)
  · exact ⟨fun _ => by simp, fun _ => ⟨2, by decide⟩⟩

/-- **`5` is a nonzero square modulo an odd prime `p` exactly when `p ≡ ±1 (mod 5)`**, by
quadratic reciprocity; at `p = 5` the Legendre symbol is `0`. -/
@[simp]
theorem legendreSym_five_eq_one_iff {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    legendreSym p 5 = 1 ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  by_cases hp5 : p = 5
  · subst hp5
    rw [(legendreSym.eq_zero_iff 5 5).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd 5 5).mpr (by norm_num))]
    norm_num
  have hF : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  -- Quadratic reciprocity for `5 ≡ 1 (mod 4)`: `(5 | p) = (p | 5)`.
  have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) hodd
  push_cast at hrec
  have hr0 : p % 5 ≠ 0 := by
    intro h
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h) with h1 | h1
    · exact absurd h1 (by norm_num)
    · exact hp5 h1.symm
  have hp0 : ((p : ℤ) : ZMod 5) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hr0 (Nat.mod_eq_zero_of_dvd h)
  rw [hrec, legendreSym.eq_one_iff _ hp0, Int.cast_natCast, ← ZMod.natCast_mod p 5]
  exact ZMod.isSquare_natCast_mod_five_iff_eq_one_or_eq_four (Nat.mod_lt _ (by norm_num)) hr0

end TauCeti
