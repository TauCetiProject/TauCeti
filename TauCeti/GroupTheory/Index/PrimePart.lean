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

If the order of a subgroup is prime to `p`, its index contains the entire `p`-part of
the order of the ambient finite group. This arithmetic constraint on indices gives
dimension constraints on induced representations.
-/

public section

namespace Subgroup

/-- The index of a subgroup of order prime to `p` is divisible by the entire `p`-part
of the order of the ambient finite group. -/
theorem ordProj_natCard_dvd_index {G : Type*} [Group G]
    (S : Subgroup G) {p : ℕ} (hp : p.Prime) (hS : ¬ p ∣ Nat.card S) :
    ordProj[p] (Nat.card G) ∣ S.index := by
  have hcop := (hp.coprime_iff_not_dvd.mpr hS).pow_left ((Nat.card G).factorization p)
  apply hcop.dvd_of_dvd_mul_left
  rw [S.card_mul_index]
  exact Nat.ordProj_dvd _ _

end Subgroup
