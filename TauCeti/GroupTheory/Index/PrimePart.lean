/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime parts of subgroup indices

If the order of a subgroup is prime to `p`, its index has the same `p`-part as the order of
the ambient group. This arithmetic constraint on indices gives dimension constraints on
induced representations.
-/

public section

namespace Subgroup

/-- The index of a subgroup of order prime to `p` has the same `p`-part as the order of the
ambient group. No primality of `p` or finiteness of the group is needed. -/
theorem ordProj_index_eq_ordProj_natCard {G : Type*} [Group G]
    (S : Subgroup G) {p : ℕ} (hS : ¬ p ∣ Nat.card S) :
    ordProj[p] S.index = ordProj[p] (Nat.card G) := by
  have hS₀ : Nat.card S ≠ 0 := fun h ↦ hS (h ▸ dvd_zero p)
  rcases eq_or_ne S.index 0 with h | h
  · simp [← S.card_mul_index, h]
  rw [← S.card_mul_index, Nat.factorization_mul hS₀ h, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hS, zero_add]

end Subgroup
