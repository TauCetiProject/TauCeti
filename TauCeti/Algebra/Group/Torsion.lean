/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Group.Conj

/-!
# Commuting with nonzero powers in groups with unique roots

Commuting with a nonzero integer or natural power is equivalent to commuting with its base.
-/

public section

namespace Commute

variable {G : Type*} [Group G] [HasUniqueRoots G] {x y : G}

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_left_iff {n : ℤ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.zpow_left n⟩
  -- Conjugation by `y` fixes `x ^ n`, hence also its unique `n`-th root `x`.
  have hconj : y * x * y⁻¹ = x :=
    zpow_left_injective hn <| conj_zpow.trans h.symm.mul_inv_cancel
  exact (commute_iff_eq x y).2 (mul_inv_eq_iff_eq_mul.1 hconj).symm

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_right_iff {n : ℤ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x :=
  Commute.symm_iff.trans ((zpow_left_iff hn).trans Commute.symm_iff)

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_left_iff {n : ℕ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  rw [← zpow_natCast]
  exact zpow_left_iff (mod_cast hn)

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_right_iff {n : ℕ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x := by
  rw [← zpow_natCast]
  exact zpow_right_iff (mod_cast hn)

end Commute
