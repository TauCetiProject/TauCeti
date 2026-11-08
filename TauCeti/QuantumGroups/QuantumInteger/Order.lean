/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Basic
public import TauCeti.QuantumGroups.QuantumInteger.Chebyshev
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Positive quantum integers

For positive parameters with nonzero defining denominator, positive-index symmetric quantum
integers are positive. This ensures positivity of the diagonal metrics on ladder modules.
For loop parameters at least two, the recurrence-defined quantum integers are positive as well.
-/

public section

namespace TauCeti

/-- Positive-index quantum integers are positive at positive parameters with nonzero
quantum-integer denominator. -/
theorem quantumInteger_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : K} (hq : 0 < q) (hd : q - q⁻¹ ≠ 0) {n : ℕ} (hn : 0 < n) :
    0 < quantumInteger q n := by
  rw [quantumInteger_natCast_eq_sum hd]
  exact Finset.sum_pos (fun _ _ => zpow_pos hq _) (by simpa using Nat.ne_of_gt hn)

/-- At loop parameters at least two, all positive-index quantum integers are positive. -/
theorem qInt_pos_of_two_le {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {δ : R} (hδ : 2 ≤ δ) {n : ℕ} (hn : 0 < n) : 0 < qInt R δ n := by
  have h : ∀ k : ℕ, 0 ≤ qInt R δ k ∧ qInt R δ k < qInt R δ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hp : 0 < qInt R δ (k + 1) := lt_of_le_of_lt ih.1 ih.2
      constructor
      · exact hp.le
      · rw [Nat.add_assoc, one_add_one_eq_two, qInt_add_two]
        nlinarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact lt_of_le_of_lt (h k).1 (h k).2

end TauCeti
