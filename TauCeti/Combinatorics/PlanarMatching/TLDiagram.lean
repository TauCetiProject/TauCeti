/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Basic

/-!
# Temperley–Lieb diagrams

A **Temperley–Lieb diagram** `n → m` is drawn in a rectangle with `n` boundary points along the
bottom and `m` along the top, read from bottom to top. It consists of a planar matching of its
`n + m` boundary points together with a number of closed circles. The boundary points are numbered
counterclockwise around the rectangle: `0, …, n - 1` along the bottom from left to right, then
`n, …, n + m - 1` along the top from right to left. With this numbering the matching is a
`TauCeti.PlanarMatching (n + m)`, and the operations that move boundary points around the
rectangle become relabellings along the cyclic order of `Fin (n + m)`:

* **rotation** moves every boundary point one step counterclockwise, `a ↦ a + 1` modulo `n + m`;
* **corner-dragging** moves a bottom corner point to the top. Dragging the bottom-right point to
  the top-right corner changes no label at all, while dragging the bottom-left point to the top-left
  corner shifts every label down by one;
* **vertical reflection** turns a diagram `n → m` upside down into a diagram `m → n`; it reverses
  the cyclic order, `a ↦ n + m - 1 - a`, and is `TauCeti.PlanarMatching.reflect`;
* **horizontal reflection** mirrors a diagram `n → m` left to right; it is the reversal of the
  cyclic order `a ↦ n - 1 - a` modulo `n + m`, which fixes the bottom and the top as sets.

All of them keep the circles. They are the diagram-level shadows of the pivotal structure
(rotation), Frobenius reciprocity for the self-duality of one strand (corner-dragging), and the
two reflection involutions of the Temperley–Lieb category; composition of diagrams, which glues
along a middle boundary and counts the circles closed there, is not defined here.

## Main definitions

* `TauCeti.TLDiagram n m`: Temperley–Lieb diagrams `n → m`.
* `TauCeti.TLDiagram.rotate n m`: rotation, a permutation of `TLDiagram n m`.
* `TauCeti.TLDiagram.dragRight n m`, `TauCeti.TLDiagram.dragLeft n m`: dragging the bottom-right
  or bottom-left corner point to the top, `TLDiagram (n + 1) m ≃ TLDiagram n (m + 1)`.
* `TauCeti.TLDiagram.verticalReflect n m`: vertical reflection, `TLDiagram n m ≃ TLDiagram m n`.
* `TauCeti.TLDiagram.reflect n m`: horizontal reflection, a permutation of `TLDiagram n m`.
* `TauCeti.TLDiagram.id n`, `TauCeti.TLDiagram.cup`, `TauCeti.TLDiagram.cap`: the identity
  diagram on `n` strands, the cup `0 → 2` and the cap `2 → 0`.

## Main results

* `TauCeti.TLDiagram.rotate_pow`: rotating `n + m` times is the identity.
* `TauCeti.TLDiagram.dragLeft_rotate`: one rotation followed by dragging the bottom-left corner
  up is dragging the bottom-right corner up.
* `TauCeti.TLDiagram.reflect_reflect`, `TauCeti.TLDiagram.verticalReflect_verticalReflect`: both
  reflections are involutions, and `TauCeti.TLDiagram.reflect_verticalReflect` says they commute.
* `TauCeti.TLDiagram.reflect_rotate`, `TauCeti.TLDiagram.verticalReflect_rotate`: each reflection
  conjugates the rotation to its inverse.
* `TauCeti.TLDiagram.reflect_dragRight`: horizontal reflection exchanges the two corner drags;
  `TauCeti.TLDiagram.verticalReflect_dragRight` and `TauCeti.TLDiagram.verticalReflect_dragLeft`:
  vertical reflection turns dragging a bottom corner up into dragging a top corner down.
* `TauCeti.TLDiagram.dragRight_id_one`, `TauCeti.TLDiagram.dragLeft_id_one`,
  `TauCeti.TLDiagram.dragRight_symm_id_one`: dragging a corner of the identity on one strand
  gives the cup or the cap.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

open Equiv

namespace TauCeti

/-- A **Temperley–Lieb diagram** `n → m`: a planar matching of the `n + m` boundary points of a
rectangle with `n` points on the bottom and `m` on the top, together with a number of closed
circles. The boundary points are numbered counterclockwise: `0, …, n - 1` along the bottom from
left to right, then `n, …, n + m - 1` along the top from right to left. -/
@[ext]
structure TLDiagram (n m : ℕ) where
  /-- The planar matching of the boundary points, numbered counterclockwise around the
  rectangle. -/
  matching : PlanarMatching (n + m)
  /-- The number of closed circles of the diagram. -/
  circles : ℕ
  deriving DecidableEq

namespace TLDiagram

variable {n m n' m' : ℕ}

/-- Relabelling the matching of a diagram along an equivalence of planar matchings, keeping the
circles. Every operation of this file is of this form. -/
private def congrMatching (e : PlanarMatching (n + m) ≃ PlanarMatching (n' + m')) :
    TLDiagram n m ≃ TLDiagram n' m' where
  toFun x := ⟨e x.matching, x.circles⟩
  invFun x := ⟨e.symm x.matching, x.circles⟩
  left_inv x := by simp
  right_inv x := by simp

@[simp]
private theorem matching_congrMatching (e : PlanarMatching (n + m) ≃ PlanarMatching (n' + m'))
    (x : TLDiagram n m) : (congrMatching e x).matching = e x.matching := (rfl)

@[simp]
private theorem circles_congrMatching (e : PlanarMatching (n + m) ≃ PlanarMatching (n' + m'))
    (x : TLDiagram n m) : (congrMatching e x).circles = x.circles := (rfl)

@[simp]
private theorem congrMatching_symm (e : PlanarMatching (n + m) ≃ PlanarMatching (n' + m')) :
    (congrMatching e).symm = congrMatching e.symm := (rfl)

/-! ### Rotation -/

/-- **Rotation** of a diagram `n → m`: every boundary point moves one step counterclockwise
around the rectangle, `a ↦ a + 1` modulo `n + m`. The bottom-right point moves to the top-right
corner and the top-left point to the bottom-left corner. -/
def rotate (n m : ℕ) : Perm (TLDiagram n m) :=
  congrMatching (PlanarMatching.rotate (n + m))

@[simp]
theorem matching_rotate (x : TLDiagram n m) :
    (rotate n m x).matching = PlanarMatching.rotate (n + m) x.matching := (rfl)

@[simp]
theorem circles_rotate (x : TLDiagram n m) : (rotate n m x).circles = x.circles := (rfl)

@[simp]
theorem matching_rotate_symm (x : TLDiagram n m) :
    ((rotate n m).symm x).matching = (PlanarMatching.rotate (n + m)).symm x.matching := (rfl)

@[simp]
theorem circles_rotate_symm (x : TLDiagram n m) : ((rotate n m).symm x).circles = x.circles :=
  (rfl)

@[simp]
theorem matching_rotate_pow (j : ℕ) (x : TLDiagram n m) :
    ((rotate n m ^ j) x).matching = (PlanarMatching.rotate (n + m) ^ j) x.matching := by
  induction j with
  | zero => rfl
  | succ j ih => simp [pow_succ', ih]

@[simp]
theorem circles_rotate_pow (j : ℕ) (x : TLDiagram n m) :
    ((rotate n m ^ j) x).circles = x.circles := by
  induction j with
  | zero => rfl
  | succ j ih => simp [pow_succ', ih]

/-- Rotating a diagram `n → m` once for each of its `n + m` boundary points is the identity. -/
@[simp]
theorem rotate_pow (n m : ℕ) : rotate n m ^ (n + m) = 1 :=
  Equiv.ext fun x => TLDiagram.ext (by simp) (by simp)

/-! ### Corner-dragging -/

/-- **Dragging the bottom-right corner up**: the last bottom point of a diagram `n + 1 → m`
becomes the first (rightmost) top point of a diagram `n → m + 1`. In the counterclockwise
numbering no label changes. -/
def dragRight (n m : ℕ) : TLDiagram (n + 1) m ≃ TLDiagram n (m + 1) :=
  congrMatching (PlanarMatching.cast (Nat.add_right_comm n 1 m))

@[simp]
theorem matching_dragRight (x : TLDiagram (n + 1) m) :
    (dragRight n m x).matching = PlanarMatching.cast (Nat.add_right_comm n 1 m) x.matching :=
  (rfl)

@[simp]
theorem circles_dragRight (x : TLDiagram (n + 1) m) : (dragRight n m x).circles = x.circles :=
  (rfl)

@[simp]
theorem matching_dragRight_symm (x : TLDiagram n (m + 1)) :
    ((dragRight n m).symm x).matching =
      PlanarMatching.cast (Nat.add_right_comm n 1 m).symm x.matching := by
  simp [dragRight]

@[simp]
theorem circles_dragRight_symm (x : TLDiagram n (m + 1)) :
    ((dragRight n m).symm x).circles = x.circles := (rfl)

/-- **Dragging the bottom-left corner up**: the first bottom point of a diagram `n + 1 → m`
becomes the last (leftmost) top point of a diagram `n → m + 1`. In the counterclockwise numbering
every label decreases by one modulo `n + m + 1`. -/
def dragLeft (n m : ℕ) : TLDiagram (n + 1) m ≃ TLDiagram n (m + 1) :=
  congrMatching ((PlanarMatching.rotate (n + 1 + m)).symm.trans
    (PlanarMatching.cast (Nat.add_right_comm n 1 m)))

@[simp]
theorem matching_dragLeft (x : TLDiagram (n + 1) m) :
    (dragLeft n m x).matching = PlanarMatching.cast (Nat.add_right_comm n 1 m)
      ((PlanarMatching.rotate (n + 1 + m)).symm x.matching) := (rfl)

@[simp]
theorem circles_dragLeft (x : TLDiagram (n + 1) m) : (dragLeft n m x).circles = x.circles :=
  (rfl)

@[simp]
theorem matching_dragLeft_symm (x : TLDiagram n (m + 1)) :
    ((dragLeft n m).symm x).matching = PlanarMatching.rotate (n + 1 + m)
      (PlanarMatching.cast (Nat.add_right_comm n 1 m).symm x.matching) := by
  simp [dragLeft]

@[simp]
theorem circles_dragLeft_symm (x : TLDiagram n (m + 1)) :
    ((dragLeft n m).symm x).circles = x.circles := (rfl)

/-- **Rotation through the corners**: rotating a diagram `n + 1 → m` once and then dragging its
bottom-left corner up is the same as dragging its bottom-right corner up. -/
@[simp]
theorem dragLeft_rotate (x : TLDiagram (n + 1) m) :
    dragLeft n m (rotate (n + 1) m x) = dragRight n m x := by
  ext <;> simp

/-! ### Reflections -/

/-- **Vertical reflection** of a diagram `n → m`: the diagram turned upside down, a diagram
`m → n`. It reverses the counterclockwise numbering, `a ↦ n + m - 1 - a`, so its matching is the
reflection `TauCeti.PlanarMatching.reflect` of the original one. -/
def verticalReflect (n m : ℕ) : TLDiagram n m ≃ TLDiagram m n :=
  congrMatching ((PlanarMatching.reflect (n + m)).trans (PlanarMatching.cast (Nat.add_comm n m)))

@[simp]
theorem matching_verticalReflect (x : TLDiagram n m) :
    (verticalReflect n m x).matching =
      PlanarMatching.cast (Nat.add_comm n m) (PlanarMatching.reflect (n + m) x.matching) := (rfl)

@[simp]
theorem circles_verticalReflect (x : TLDiagram n m) :
    (verticalReflect n m x).circles = x.circles := (rfl)

/-- Vertical reflection is an involution. -/
@[simp]
theorem verticalReflect_verticalReflect (x : TLDiagram n m) :
    verticalReflect m n (verticalReflect n m x) = x := by
  ext : 1
  · simp [← PlanarMatching.cast_reflect]
  · simp

/-- Vertical reflection is its own inverse. -/
@[simp]
theorem verticalReflect_symm (n m : ℕ) : (verticalReflect n m).symm = verticalReflect m n :=
  Equiv.ext fun x => (Equiv.symm_apply_eq _).mpr (verticalReflect_verticalReflect x).symm

/-- **Horizontal reflection** of a diagram `n → m`: the diagram mirrored left to right. It
reverses the counterclockwise numbering by `a ↦ n - 1 - a` modulo `n + m`, which maps the bottom
points `0, …, n - 1` and the top points `n, …, n + m - 1` to themselves; so its matching is the
reflection `TauCeti.PlanarMatching.reflect` of the original one, rotated `n` times. -/
def reflect (n m : ℕ) : Perm (TLDiagram n m) :=
  congrMatching ((PlanarMatching.reflect (n + m)).trans (PlanarMatching.rotate (n + m) ^ n))

@[simp]
theorem matching_reflect (x : TLDiagram n m) :
    (reflect n m x).matching =
      (PlanarMatching.rotate (n + m) ^ n) (PlanarMatching.reflect (n + m) x.matching) := (rfl)

@[simp]
theorem circles_reflect (x : TLDiagram n m) : (reflect n m x).circles = x.circles := (rfl)

/-- Horizontal reflection is an involution. -/
@[simp]
theorem reflect_reflect (x : TLDiagram n m) : reflect n m (reflect n m x) = x := by
  ext : 1
  · simp [PlanarMatching.reflect_rotate_pow]
  · simp

/-- Horizontal reflection is its own inverse. -/
@[simp]
theorem reflect_symm (n m : ℕ) : (reflect n m).symm = reflect n m :=
  Equiv.ext fun x => (Equiv.symm_apply_eq _).mpr (reflect_reflect x).symm

/-- The two reflections commute: mirroring a diagram left to right and turning it upside down
can be done in either order. -/
theorem reflect_verticalReflect (x : TLDiagram n m) :
    reflect m n (verticalReflect n m x) = verticalReflect n m (reflect n m x) := by
  ext : 1
  · -- Both matchings are the original one rotated, by `m` steps and by `-n` steps respectively,
    -- and these agree because rotating `n + m` times is the identity.
    have h : (PlanarMatching.rotate (n + m) ^ m) =
        (PlanarMatching.rotate (n + m) ^ n)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add, add_comm, PlanarMatching.rotate_pow_self]
    simp [← PlanarMatching.cast_reflect, ← PlanarMatching.cast_rotate_pow,
      PlanarMatching.reflect_rotate_pow, h]
  · simp

/-- Horizontal reflection conjugates the rotation to its inverse. -/
theorem reflect_rotate (x : TLDiagram n m) :
    reflect n m (rotate n m x) = (rotate n m).symm (reflect n m x) := by
  ext : 1
  · simp only [matching_reflect, matching_rotate, matching_rotate_symm,
      PlanarMatching.reflect_rotate]
    rw [← Perm.inv_def, ← Perm.mul_apply, ← Perm.mul_apply,
      ((Commute.refl _).pow_left n).inv_right.eq]
    simp only [Perm.mul_apply, Perm.inv_def]
  · simp

/-- Vertical reflection conjugates the rotation to its inverse. -/
theorem verticalReflect_rotate (x : TLDiagram n m) :
    verticalReflect n m (rotate n m x) = (rotate m n).symm (verticalReflect n m x) := by
  ext : 1
  · simp [PlanarMatching.reflect_rotate, PlanarMatching.cast_rotate_symm]
  · simp

/-- Horizontal reflection exchanges the two corner drags: mirroring a diagram after dragging its
bottom-right corner up is dragging the bottom-left corner of the mirrored diagram up. -/
theorem reflect_dragRight (x : TLDiagram (n + 1) m) :
    reflect n (m + 1) (dragRight n m x) = dragLeft n m (reflect (n + 1) m x) := by
  ext : 1
  · simp only [matching_reflect, matching_dragRight, matching_dragLeft]
    rw [pow_succ', Perm.mul_apply, Equiv.symm_apply_apply, PlanarMatching.cast_rotate_pow,
      PlanarMatching.cast_reflect]
    -- The two sides differ only in writing the number of points as `n + (m + 1)` or `n + m + 1`.
    rfl
  · simp

/-- Vertical reflection turns dragging the bottom-right corner up into dragging the top-right
corner down. -/
theorem verticalReflect_dragRight (x : TLDiagram (n + 1) m) :
    verticalReflect n (m + 1) (dragRight n m x) =
      (dragRight m n).symm (verticalReflect (n + 1) m x) := by
  ext : 1
  · simp [← PlanarMatching.cast_reflect]
  · simp

/-- Vertical reflection turns dragging the bottom-left corner up into dragging the top-left
corner down. -/
theorem verticalReflect_dragLeft (x : TLDiagram (n + 1) m) :
    verticalReflect n (m + 1) (dragLeft n m x) =
      (dragLeft m n).symm (verticalReflect (n + 1) m x) := by
  ext : 1
  · simp [← PlanarMatching.cast_reflect, PlanarMatching.reflect_rotate_symm,
      PlanarMatching.cast_rotate]
  · simp

/-! ### The identity, the cup and the cap -/

/-- The **identity diagram** on `n` strands: each bottom point is joined to the top point straight
above it, with no circles. In the counterclockwise numbering the bottom point `i` is joined to the
top point `2n - 1 - i`, so the matching is the fully nested `TauCeti.PlanarMatching.nested`. -/
def id (n : ℕ) : TLDiagram n n :=
  ⟨PlanarMatching.nested n, 0⟩

@[simp]
theorem id_matching_val (n : ℕ) : (id n).matching.1.val = Fin.revPerm :=
  PlanarMatching.nested_val n

@[simp]
theorem circles_id (n : ℕ) : (id n).circles = 0 := (rfl)

/-- The identity diagram is symmetric under vertical reflection. -/
@[simp]
theorem verticalReflect_id (n : ℕ) : verticalReflect n n (id n) = id n := by
  ext : 1
  · ext a
    simp
  · simp

/-- The **cup** `0 → 2`, joining the two top points, with no circles. -/
def cup : TLDiagram 0 2 :=
  ⟨⟨⟨swap 0 1, by decide⟩, by decide⟩, 0⟩

@[simp]
theorem cup_matching_val : cup.matching.1.val = swap 0 1 := (rfl)

@[simp]
theorem circles_cup : cup.circles = 0 := (rfl)

/-- The **cap** `2 → 0`, joining the two bottom points, with no circles. -/
def cap : TLDiagram 2 0 :=
  ⟨⟨⟨swap 0 1, by decide⟩, by decide⟩, 0⟩

@[simp]
theorem cap_matching_val : cap.matching.1.val = swap 0 1 := (rfl)

@[simp]
theorem circles_cap : cap.circles = 0 := (rfl)

/-- Turning the cup upside down gives the cap. -/
@[simp]
theorem verticalReflect_cup : verticalReflect 0 2 cup = cap := by
  ext : 1
  · refine Subtype.ext (Subtype.ext ?_)
    simp only [matching_verticalReflect, PlanarMatching.coe_cast_apply,
      PlanarMatching.coe_reflect_apply, PerfectMatching.congr_trans, PerfectMatching.congr_val,
      cup_matching_val, cap_matching_val]
    decide
  · simp

/-- Turning the cap upside down gives the cup. -/
@[simp]
theorem verticalReflect_cap : verticalReflect 2 0 cap = cup := by
  ext : 1
  · refine Subtype.ext (Subtype.ext ?_)
    simp only [matching_verticalReflect, PlanarMatching.coe_cast_apply,
      PlanarMatching.coe_reflect_apply, PerfectMatching.congr_trans, PerfectMatching.congr_val,
      cup_matching_val, cap_matching_val]
    decide
  · simp

/-- Dragging the bottom-right corner of the identity on one strand up gives the cup. -/
theorem dragRight_id_one : dragRight 0 1 (id 1) = cup := by
  ext : 1
  · refine Subtype.ext (Subtype.ext ?_)
    simp only [matching_dragRight, PlanarMatching.coe_cast_apply, PerfectMatching.congr_val,
      cup_matching_val, id_matching_val]
    decide
  · simp

/-- Dragging the bottom-left corner of the identity on one strand up gives the cup. -/
theorem dragLeft_id_one : dragLeft 0 1 (id 1) = cup := by
  ext : 1
  · refine Subtype.ext (Subtype.ext ?_)
    simp only [matching_dragLeft, PlanarMatching.coe_cast_apply,
      PlanarMatching.coe_rotate_symm_apply, PerfectMatching.congr_trans, PerfectMatching.congr_val,
      cup_matching_val, id_matching_val]
    decide
  · simp

/-- Dragging the top-right corner of the identity on one strand down gives the cap. -/
theorem dragRight_symm_id_one : (dragRight 1 0).symm (id 1) = cap := by
  ext : 1
  · refine Subtype.ext (Subtype.ext ?_)
    simp only [matching_dragRight_symm, PlanarMatching.coe_cast_apply, PerfectMatching.congr_val,
      cap_matching_val, id_matching_val]
    decide
  · simp

end TLDiagram

/-- Horizontal reflection exchanges the two distinct diagrams `3 → 1` built from a cap and a
strand: it sends the cap on the two left points, `{0, 1}, {2, 3}`, to the cap on the two right
points, `{0, 3}, {1, 2}`. So it does not fix every diagram built from cups, caps and strands. -/
example (x y : TLDiagram 3 1) (hx : x.matching.1.val = swap 0 1 * swap 2 3)
    (hy : y.matching.1.val = swap 0 3 * swap 1 2) (hc : x.circles = y.circles) :
    TLDiagram.reflect 3 1 x = y ∧ x ≠ y := by
  refine ⟨TLDiagram.ext (PlanarMatching.ext fun a => ?_) hc, fun h => ?_⟩
  · simp only [TLDiagram.matching_reflect, PlanarMatching.coe_rotate_pow_apply,
      PlanarMatching.coe_reflect_apply, PerfectMatching.congr_trans, PerfectMatching.congr_val,
      hx, hy]
    revert a
    decide
  · have := congrArg (fun z : TLDiagram 3 1 => z.matching.1.val 0) h
    simp only [hx, hy] at this
    exact absurd this (by decide)

/-- The rotation of the identity diagram on two strands, `{0, 3}, {1, 2}`, is the diagram
`{1, 0}, {2, 3}`: a cap on the bottom points followed by a cup on the top points. -/
example : (TLDiagram.rotate 2 2 (TLDiagram.id 2)).matching.1.val = swap 0 1 * swap 2 3 := by
  simp only [TLDiagram.matching_rotate, PlanarMatching.coe_rotate_apply, PerfectMatching.congr_val,
    TLDiagram.id_matching_val]
  decide

end TauCeti
