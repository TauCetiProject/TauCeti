/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Orbit invariance of action periods

In a group action, translating a point by an integer power of `g` preserves its minimal period
under `g • ·` (`MulAction.minimalPeriod_zpow_smul`).
-/

public section

namespace MulAction

/-- **Orbit invariance of minimal periods.** In a group action, translating a point by an integer
power of `g` preserves its minimal period under `g • ·`. -/
@[to_additive
/-- **Orbit invariance of minimal periods.** In an additive group action, translating a point by
an integer multiple of `g` preserves its minimal period under `g +ᵥ ·`. -/]
theorem minimalPeriod_zpow_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (j : ℤ)
    (a : α) : Function.minimalPeriod (g • ·) (g ^ j • a) = Function.minimalPeriod (g • ·) a := by
  have key (b : α) (i : ℤ) :
      Function.minimalPeriod (g • ·) (g ^ i • b) ∣ Function.minimalPeriod (g • ·) b :=
    pow_smul_eq_iff_minimalPeriod_dvd.mp (by
      rw [← mul_smul, ← zpow_natCast, ← zpow_add, add_comm, zpow_add, zpow_natCast, mul_smul,
        pow_smul_eq_iff_minimalPeriod_dvd.mpr dvd_rfl])
  refine Nat.dvd_antisymm (key a j) ?_
  have h := key (g ^ j • a) (-j)
  rwa [← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul] at h

end MulAction
