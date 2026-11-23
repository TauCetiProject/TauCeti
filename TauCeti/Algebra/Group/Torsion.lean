/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Units

/-!
# Commuting with nonzero powers in monoids with unique roots

In a monoid with unique roots, a unit commutes with a nonzero natural power of `x` exactly when
it commutes with `x`. In a group with unique roots, the same holds for nonzero integer powers.

`Group.isUnit` is registered as a simp lemma, so that `simp` discharges the unit hypothesis of
the natural-power lemmas in a group.
-/

public section

attribute [simp] Group.isUnit

namespace Commute

section Monoid

variable {M : Type*} [Monoid M] [HasUniqueRoots M] {x y : M}

/-- In a monoid with unique roots, a unit commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_right_iff {n : ℕ} (hn : n ≠ 0) (hy : IsUnit y) :
    Commute y (x ^ n) ↔ Commute y x := by
  obtain ⟨u, rfl⟩ := hy
  rw [u.commute_iff_mul_inv_cancel, u.commute_iff_mul_inv_cancel, ← u.conj_pow,
    (pow_left_injective hn).eq_iff]

/-- In a monoid with unique roots, a unit commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_left_iff {n : ℕ} (hn : n ≠ 0) (hy : IsUnit y) :
    Commute (x ^ n) y ↔ Commute x y :=
  Commute.symm_iff.trans ((pow_right_iff hn hy).trans Commute.symm_iff)

end Monoid

section Group

variable {G : Type*} [Group G] [HasUniqueRoots G] {x y : G}

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_left_iff {n : ℤ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]
    exact pow_left_iff (by omega) (Group.isUnit y)
  · rw [zpow_neg, zpow_natCast, inv_left_iff]
    exact pow_left_iff (by omega) (Group.isUnit y)

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_right_iff {n : ℤ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x :=
  Commute.symm_iff.trans ((zpow_left_iff hn).trans Commute.symm_iff)

end Group

end Commute
