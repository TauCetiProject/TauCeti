/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.IntervalCases

/-!
# The Legendre symbol `(5 | p)`

Since `5 ≡ 1 (mod 4)`, quadratic reciprocity gives `(5 | p) = (p | 5)` for every odd prime `p`,
and the nonzero squares modulo `5` are `1` and `4`. Hence `5` is a nonzero square modulo an odd
prime `p` exactly when `p ≡ ±1 (mod 5)`; at `p = 5` the symbol is `0`.

## Main results

* `TauCeti.ZMod.isSquare_natCast_iff_mod_five`: the squares in `ZMod 5` are `0`, `1` and `4`.
* `TauCeti.legendreSym_five_eq_one_iff`: for an odd prime `p`, `legendreSym p 5 = 1` if and
  only if `p % 5 = 1 ∨ p % 5 = 4`.
-/

public section

namespace TauCeti

/-- The squares in `ZMod 5` are `0`, `1` and `4`: a natural number `r` is a square modulo `5`
exactly when `r % 5` is `0`, `1` or `4`. -/
theorem ZMod.isSquare_natCast_iff_mod_five (r : ℕ) :
    IsSquare (r : ZMod 5) ↔ r % 5 = 0 ∨ r % 5 = 1 ∨ r % 5 = 4 := by
  rw [← ZMod.natCast_mod]
  have := Nat.mod_lt r (by norm_num : 0 < 5)
  interval_cases r % 5 <;> decide

/-- **`5` is a nonzero square modulo an odd prime `p` exactly when `p ≡ ±1 (mod 5)`**, by
quadratic reciprocity; at `p = 5` the Legendre symbol is `0`. -/
@[simp]
theorem legendreSym_five_eq_one_iff {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    legendreSym p 5 = 1 ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  -- Quadratic reciprocity for `5 ≡ 1 (mod 4)`: `(5 | p) = (p | 5)`.
  have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) hodd
  push_cast at hrec
  rw [hrec]
  by_cases h0 : (p : ZMod 5) = 0
  · rw [(legendreSym.eq_zero_iff _ _).mpr (mod_cast h0)]
    rw [ZMod.natCast_eq_zero_iff] at h0
    omega
  · rw [legendreSym.eq_one_iff' _ h0, ZMod.isSquare_natCast_iff_mod_five]
    rw [ZMod.natCast_eq_zero_iff] at h0
    omega

end TauCeti
