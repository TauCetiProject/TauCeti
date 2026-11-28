/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# The period of a group element along its orbit

For a group `G` acting on `α`, the period of `g : G` at a point (the least `n > 0` with
`g ^ n • a = a`) is constant along the orbit of `a` under the powers of `g`
(`MulAction.minimalPeriod_zpow_smul`).
For a point fixed by `g ^ 2`, `MulAction.zpow_smul_eq_ite_of_sq_smul_eq` reads the translated
point off the parity of the exponent. It uses Mathlib's `MulAction.zpow_smul_eq_iff_period_dvd`.
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

/-- If `g ^ 2` fixes `a`, then an even power of `g` fixes `a` and an odd power of `g` sends
it to `g • a`. -/
theorem zpow_smul_eq_ite_of_sq_smul_eq {G α : Type*} [Group G] [MulAction G α] (g : G)
    {a : α} (ha : g ^ 2 • a = a) (n : ℤ) : g ^ n • a = if Even n then a else g • a := by
  have hperiod : (period g a : ℤ) ∣ 2 :=
    zpow_smul_eq_iff_period_dvd.mp (by simpa only [zpow_ofNat] using ha)
  have hfix (k : ℤ) : g ^ (2 * k) • a = a :=
    zpow_smul_eq_iff_period_dvd.mpr (hperiod.trans (dvd_mul_right _ _))
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [ite_eq_left (even_two_mul k), hfix]
  · have hk : Odd (2 * k + 1) := ⟨k, rfl⟩
    have hpow : g ^ (2 * k + 1) = g * g ^ (2 * k) := by
      rw [add_comm (2 * k) 1, zpow_add, zpow_one]
    rw [ite_eq_right (Int.not_even_iff_odd.mpr hk), hpow, mul_smul, hfix]

end MulAction
