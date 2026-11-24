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
parity argument `TauCeti.isSquare_zpow_or_isSquare_zpow_or_isSquare_zpow_mul_zpow` for powers of
a common element.

Lifting a free basis gives a test for commutativity of a free group by homomorphisms: if every
homomorphism to a group `Q` with two noncommuting elements has commutative range, the free group
is commutative (`IsFreeGroup.isMulCommutative_of_forall_isMulCommutative_range`). Lyndon's theorem
`IsFreeGroup.isVaught` applies this test with `Q` the dihedral group of order `8`.
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
    TauCeti.isSquare_zpow_or_isSquare_zpow_or_isSquare_zpow_mul_zpow r m n

/-- A free group is commutative as soon as every homomorphism from it to a fixed group `Q`
containing two noncommuting elements has commutative range. -/
theorem isMulCommutative_of_forall_isMulCommutative_range {Q : Type*} [Group Q] {x y : Q}
    (hxy : ¬Commute x y) (h : ∀ π : G →* Q, IsMulCommutative π.range) : IsMulCommutative G := by
  classical
  rcases subsingleton_or_nontrivial (Generators G) with hι | ⟨u, v, huv⟩
  · have := FreeGroup.isMulCommutative_iff_subsingleton.2 hι
    exact (toFreeGroup G).symm.surjective.isMulCommutative
  let π : G →* Q := lift fun i => if i = u then x else if i = v then y else 1
  have := h π
  refine absurd ((commute_iff_eq x y).2 ?_) hxy
  simpa [π, huv.symm] using
    setLike_mul_comm (π.mem_range.2 ⟨of u, rfl⟩) (π.mem_range.2 ⟨of v, rfl⟩)

end IsFreeGroup
