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
import Mathlib.Tactic.Group

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
  constructor
  · intro h
    have hconj : y⁻¹ * x * y = x := by
      apply zpow_left_injective hn
      calc
        (y⁻¹ * x * y) ^ n = y⁻¹ * x ^ n * y := by
          simpa only [inv_inv] using (conj_zpow (a := y⁻¹) (b := x) (i := n))
        _ = x ^ n := h.symm.inv_mul_cancel
    exact calc
      x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by rw [hconj]
  · intro h
    exact h.zpow_left n

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_right_iff {n : ℤ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x :=
  Commute.symm_iff.trans ((zpow_left_iff hn).trans Commute.symm_iff)

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_left_iff {n : ℕ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using (zpow_left_iff (x := x) (y := y) hn')

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_right_iff {n : ℕ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using (zpow_right_iff (x := x) (y := y) hn')

end Commute
