/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Center
import TauCeti.Algebra.Group.Even

/-!
# Commuting elements of a free group

Two elements of a free group commute exactly when they are integer powers of a common element
(Mathlib's `IsFreeGroup.commute_iff_exists_zpow`). Consequently, for commuting elements `x` and
`y`, one of `x`, `y` and `x * y` is a square (`IsFreeGroup.exists_eq_sq_of_commute`), by the
parity argument `isSquare_zpow_or_isSquare_zpow_or_isSquare_zpow_mul_zpow` for powers of a common
element.
-/

public section

namespace IsFreeGroup

variable {G : Type*} [Group G] [IsFreeGroup G]

/-- For commuting elements `x` and `y` of a free group, one of `x`, `y` and `x * y` is a
square. -/
theorem exists_eq_sq_of_commute {x y : G} (h : Commute x y) :
    ∃ z : G, x = z ^ 2 ∨ y = z ^ 2 ∨ x * y = z ^ 2 := by
  obtain ⟨r, m, n, rfl, rfl⟩ := commute_iff_exists_zpow.1 h
  simpa only [exists_or, ← isSquare_iff_exists_sq] using
    isSquare_zpow_or_isSquare_zpow_or_isSquare_zpow_mul_zpow r m n

end IsFreeGroup
