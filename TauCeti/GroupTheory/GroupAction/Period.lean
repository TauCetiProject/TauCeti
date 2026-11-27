/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# The period of a group element along its orbit

For a group `G` acting on `α`, the period of `g : G` at a point (the least `n > 0` with
`g ^ n • a = a`) is constant along the orbit of `a` under the powers of `g`
(`MulAction.minimalPeriod_zpow_smul`). Mathlib has `MulAction.period` and its divisibility API
(`MulAction.pow_smul_eq_iff_minimalPeriod_dvd`) but not this invariance.
-/

public section

namespace MulAction

/-- **The period of `g` is constant along the orbit of `⟨g⟩`**: translating a point by a power of
`g` does not change the period of `g` there. -/
@[simp]
theorem minimalPeriod_zpow_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (j : ℤ)
    (a : α) : Function.minimalPeriod (g • ·) (g ^ j • a) = Function.minimalPeriod (g • ·) a := by
  have key : ∀ (b : α) (i : ℤ),
      Function.minimalPeriod (g • ·) (g ^ i • b) ∣ Function.minimalPeriod (g • ·) b :=
    fun b i ↦ pow_smul_eq_iff_minimalPeriod_dvd.mp (by
      rw [← mul_smul, ← zpow_natCast, ← zpow_add, add_comm, zpow_add, zpow_natCast, mul_smul,
        pow_smul_eq_iff_minimalPeriod_dvd.mpr dvd_rfl])
  refine Nat.dvd_antisymm (key a j) ?_
  have h := key (g ^ j • a) (-j)
  rwa [← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul] at h

end MulAction
