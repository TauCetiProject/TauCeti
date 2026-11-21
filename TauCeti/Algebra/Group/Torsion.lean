/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Commuting with nonzero powers in monoids with unique roots

In a monoid with unique roots, a unit commutes with a nonzero natural power of `x` exactly when
it commutes with `x`. In a group with unique roots, the same holds for nonzero integer powers.
-/

public section

namespace Commute

section Monoid

variable {M : Type*} [Monoid M] [HasUniqueRoots M] {x y : M}

/-- In a monoid with unique roots, a unit commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_left_iff {n : ℕ} (hn : n ≠ 0) (hy : IsUnit y) :
    Commute (x ^ n) y ↔ Commute x y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pow_left n⟩
  obtain ⟨u, rfl⟩ := hy
  -- Conjugation by `u` fixes `x ^ n`, hence also its unique `n`-th root `x`.
  have hconj : ↑u * x * ↑u⁻¹ = x :=
    pow_left_injective hn <| (u.conj_pow x n).trans (u.mul_inv_eq_iff_eq_mul.2 h.eq.symm)
  exact (u.mul_inv_eq_iff_eq_mul.1 hconj).symm

/-- In a monoid with unique roots, a unit commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_right_iff {n : ℕ} (hn : n ≠ 0) (hy : IsUnit y) :
    Commute y (x ^ n) ↔ Commute y x :=
  Commute.symm_iff.trans ((pow_left_iff hn hy).trans Commute.symm_iff)

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
