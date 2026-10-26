/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Generator

/-!
# Positions of directions in an ordered plumbing cube

Order the vertices of a plumbing graph linearly. The position of a direction `v` of a cube `C`,
counted from one in the increasing listing of the directions of `C`, fixes the sign of the faces
of `C` in direction `v` in Némethi's oriented cubical differential.

Removing two distinct directions in the two possible orders produces opposite products of
position signs: removing the smaller one first lowers the position of the larger one by one,
while removing the larger one first leaves the position of the smaller one unchanged. This is the
sign rule behind the vanishing of the square of the oriented lattice differential.

## Main definitions

* `TauCeti.PlumbingCube.directionIndex`: the position of a direction in the direction set of a cube.

## Main results

* `TauCeti.PlumbingCube.neg_one_pow_directionIndex_add_eraseDirection_eq_neg`: the sign rule for
  removing two directions in either order.

## References

The cubical sign convention is that of A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

namespace PlumbingCube

variable {V : Type*} [LinearOrder V]

/-- The position of `v` among the directions of `C` listed in increasing order, counted from one
when `v` is a direction: the number of directions of `C` that are at most `v`. It fixes the sign of
the face of `C` in direction `v` in the oriented lattice differential. -/
def directionIndex (C : PlumbingCube V) (v : V) : ℕ :=
  (C.directions.filter (· ≤ v)).card

/-- The position of a direction is the number of directions at most it. -/
theorem directionIndex_def (C : PlumbingCube V) (v : V) :
    C.directionIndex v = (C.directions.filter (· ≤ v)).card :=
  (rfl)

/-- The position of a direction in an explicit cube. -/
@[simp]
theorem directionIndex_mk (x : V → ℤ) (S : Finset V) (v : V) :
    directionIndex ({ base := x, directions := S } : PlumbingCube V) v =
      (S.filter (· ≤ v)).card :=
  (rfl)

/-- The position of a direction depends only on the direction set, so it is the same in the lower
face and in the raw lower cube. -/
@[simp]
theorem directionIndex_lowerFace (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) (w : V) :
    (C.lowerFace v hv).directionIndex w = (C.eraseDirection v).directionIndex w := by
  simp [directionIndex_def]

/-- The position of a direction depends only on the direction set, so it is the same in the upper
face and in the raw lower cube. -/
@[simp]
theorem directionIndex_upperFace (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) (w : V) :
    (C.upperFace v hv).directionIndex w = (C.eraseDirection v).directionIndex w := by
  simp [directionIndex_def]

/-- Removing a smaller direction lowers the position of a larger direction by one. -/
theorem directionIndex_eraseDirection_add_one_of_lt (C : PlumbingCube V) {v w : V}
    (hv : v ∈ C.directions) (hvw : v < w) :
    (C.eraseDirection v).directionIndex w + 1 = C.directionIndex w := by
  rw [directionIndex_def, directionIndex_def, eraseDirection_directions, Finset.filter_erase,
    Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hv, hvw.le⟩)]

/-- Removing a larger direction leaves the position of a smaller direction unchanged. -/
theorem directionIndex_eraseDirection_of_lt (C : PlumbingCube V) {v w : V} (hvw : v < w) :
    (C.eraseDirection w).directionIndex v = C.directionIndex v := by
  rw [directionIndex_def, directionIndex_def, eraseDirection_directions, Finset.filter_erase,
    Finset.erase_eq_of_notMem (by simp [hvw])]

/-- The sign rule behind `∂² = 0`: removing two distinct directions in the two possible orders
produces opposite products of position signs. -/
theorem neg_one_pow_directionIndex_add_eraseDirection_eq_neg (R : Type*) [Ring R]
    (C : PlumbingCube V) {v w : V} (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    (-1 : R) ^ (C.directionIndex v + (C.eraseDirection v).directionIndex w) =
      -(-1 : R) ^ (C.directionIndex w + (C.eraseDirection w).directionIndex v) := by
  have hswap : ∀ a b : ℕ, b + 1 + a = a + b + 1 := fun a b => by omega
  rcases hne.lt_or_gt with hvw | hwv
  · rw [← C.directionIndex_eraseDirection_add_one_of_lt hv hvw,
      C.directionIndex_eraseDirection_of_lt hvw, hswap, pow_succ]
    simp
  · rw [← C.directionIndex_eraseDirection_add_one_of_lt hw hwv,
      C.directionIndex_eraseDirection_of_lt hwv, hswap, pow_succ]
    simp

end PlumbingCube

end TauCeti
