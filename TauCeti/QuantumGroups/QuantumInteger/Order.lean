/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Positive quantum integers

For positive parameters with nonzero defining denominator, positive-index symmetric quantum
integers are positive. This ensures positivity of the diagonal metrics on ladder modules.
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

end TauCeti
