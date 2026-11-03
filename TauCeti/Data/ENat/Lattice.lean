/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice

/-!
# Suprema of downward-closed sets of natural numbers in `ℕ∞`

A graph invariant such as edge connectivity is often defined as the supremum in `ℕ∞` of the
natural thresholds `n` at which some property `P n` holds. When `P` is antitone (a property at `n`
implies it at every smaller threshold) and holds at `0`, the supremum recovers the property:
`(k : ℕ∞) ≤ ⨆ (n : ℕ) (_ : P n), (n : ℕ∞)` exactly when `P k`.
-/

public section

namespace Antitone

/-- For an antitone predicate on `ℕ` holding at `0`, a natural number is at most the supremum in
`ℕ∞` of the natural numbers satisfying the predicate exactly when it satisfies the predicate. -/
theorem natCast_le_iSup_iff {P : ℕ → Prop} (hP : Antitone P) (h0 : P 0) {k : ℕ} :
    (k : ℕ∞) ≤ ⨆ (n : ℕ) (_ : P n), (n : ℕ∞) ↔ P k := by
  refine ⟨fun hk ↦ ?_, fun hk ↦ le_iSup₂_of_le k hk le_rfl⟩
  cases k with
  | zero => exact h0
  | succ k =>
    have hlt : (k : ℕ∞) < ⨆ (n : ℕ) (_ : P n), (n : ℕ∞) :=
      (ENat.natCast_lt_natCast.mpr k.lt_succ_self).trans_le hk
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hPn, hkn⟩ := lt_iSup_iff.mp hn
    exact hP (Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp hkn)) hPn

end Antitone
