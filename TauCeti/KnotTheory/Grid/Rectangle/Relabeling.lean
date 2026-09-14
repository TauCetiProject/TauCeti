/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Squares

/-!
# Relabeling oriented grid rectangles

An oriented rectangle between two grid states only records where the two states exchange rows,
so it survives an arbitrary relabeling of the rows or of the columns: relabeling the rows keeps
its side columns, while relabeling the columns renames them. This file packages these two
transports as equivalences between the rectangles joining two states and the rectangles joining
their relabelings.

Emptiness and the covered squares are a different matter, because they are defined by cyclic
intervals and an arbitrary permutation of `Fin n` does not preserve the cyclic order. The cyclic
permutation `finRotate n` does, by `Grid.mem_cIoo_finRotate_finRotate` and
`Grid.mem_cIco_finRotate_finRotate`, so for it the transported rectangle is empty exactly when
the original one is, and covers the correspondingly rotated squares. These are the rectangle-level
facts behind the invariance of the grid differentials under the cyclic permutation moves of a
grid diagram.

## Main definitions

* `TauCeti.GridRectangleBetween.relabelRowsEquiv`: rectangles from `x` to `y` correspond to
  rectangles from `x.relabelRows ρ` to `y.relabelRows ρ`, with the same side columns.
* `TauCeti.GridRectangleBetween.relabelColumnsEquiv`: rectangles from `x` to `y` correspond to
  rectangles from `x.relabelColumns κ` to `y.relabelColumns κ`, with side columns renamed by `κ`.

## Main results

* `TauCeti.GridRectangleBetween.isEmpty_relabelRowsEquiv_finRotate`,
  `TauCeti.GridRectangleBetween.isEmpty_relabelColumnsEquiv_finRotate`: a cyclic permutation
  preserves and reflects emptiness.
* `TauCeti.GridRectangleBetween.mem_coveredSquares_relabelRowsEquiv_finRotate`,
  `TauCeti.GridRectangleBetween.mem_coveredSquares_relabelColumnsEquiv_finRotate`: a cyclic
  permutation rotates the covered squares.

## References

Cyclic permutations of a toroidal grid diagram and their effect on rectangles follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ}

/-! ### Row relabeling -/

/-- Relabeling the rows of two grid states transports the oriented rectangles between them: the
relabeled states still exchange rows at the same two side columns. -/
def relabelRowsEquiv (ρ : Equiv.Perm (Fin n)) (x y : GridState n) :
    GridRectangleBetween x y ≃ GridRectangleBetween (x.relabelRows ρ) (y.relabelRows ρ) where
  toFun R :=
    { left := R.left
      right := R.right
      left_ne_right := R.left_ne_right
      map_left := by simp [R.map_left]
      map_right := by simp [R.map_right]
      map_of_ne := fun c hl hr => by simp [R.map_of_ne c hl hr] }
  invFun S :=
    { left := S.left
      right := S.right
      left_ne_right := S.left_ne_right
      map_left := ρ.injective (by simpa using S.map_left)
      map_right := ρ.injective (by simpa using S.map_right)
      map_of_ne := fun c hl hr => ρ.injective (by simpa using S.map_of_ne c hl hr) }
  left_inv _ := eq_of_sides rfl rfl
  right_inv _ := eq_of_sides rfl rfl

variable {x y : GridState n}

/-- Row relabeling keeps the initial side column. -/
@[simp]
theorem relabelRowsEquiv_apply_left (ρ : Equiv.Perm (Fin n)) (R : GridRectangleBetween x y) :
    (relabelRowsEquiv ρ x y R).left = R.left :=
  (rfl)

/-- Row relabeling keeps the terminal side column. -/
@[simp]
theorem relabelRowsEquiv_apply_right (ρ : Equiv.Perm (Fin n)) (R : GridRectangleBetween x y) :
    (relabelRowsEquiv ρ x y R).right = R.right :=
  (rfl)

/-- The inverse of row relabeling keeps the initial side column. -/
@[simp]
theorem relabelRowsEquiv_symm_apply_left (ρ : Equiv.Perm (Fin n))
    (S : GridRectangleBetween (x.relabelRows ρ) (y.relabelRows ρ)) :
    ((relabelRowsEquiv ρ x y).symm S).left = S.left :=
  (rfl)

/-- The inverse of row relabeling keeps the terminal side column. -/
@[simp]
theorem relabelRowsEquiv_symm_apply_right (ρ : Equiv.Perm (Fin n))
    (S : GridRectangleBetween (x.relabelRows ρ) (y.relabelRows ρ)) :
    ((relabelRowsEquiv ρ x y).symm S).right = S.right :=
  (rfl)

/-- Row relabeling renames the initial side row. -/
@[simp]
theorem relabelRowsEquiv_apply_bottom (ρ : Equiv.Perm (Fin n)) (R : GridRectangleBetween x y) :
    (relabelRowsEquiv ρ x y R).bottom = ρ R.bottom :=
  (rfl)

/-- Row relabeling renames the terminal side row. -/
@[simp]
theorem relabelRowsEquiv_apply_top (ρ : Equiv.Perm (Fin n)) (R : GridRectangleBetween x y) :
    (relabelRowsEquiv ρ x y R).top = ρ R.top :=
  (rfl)

/-- A cyclic permutation of the rows preserves and reflects emptiness of a rectangle. -/
@[simp]
theorem isEmpty_relabelRowsEquiv_finRotate (R : GridRectangleBetween x y) :
    (relabelRowsEquiv (finRotate n) x y R).IsEmpty ↔ R.IsEmpty := by
  simp only [isEmpty_iff_forall_notMem_cIoo, relabelRowsEquiv_apply_left,
    relabelRowsEquiv_apply_right, relabelRowsEquiv_apply_bottom, relabelRowsEquiv_apply_top,
    GridState.relabelRows_apply, Grid.mem_cIoo_finRotate_finRotate]

/-- A cyclic permutation of the rows rotates the squares a rectangle covers in the row
direction. -/
theorem mem_coveredSquares_relabelRowsEquiv_finRotate (R : GridRectangleBetween x y)
    (p : Fin n × Fin n) :
    p ∈ (relabelRowsEquiv (finRotate n) x y R).toGridRectangle.coveredSquares ↔
      (p.1, (finRotate n).symm p.2) ∈ R.toGridRectangle.coveredSquares := by
  obtain ⟨c, r⟩ := p
  obtain ⟨r, rfl⟩ := (finRotate n).surjective r
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, relabelRowsEquiv_apply_left,
    relabelRowsEquiv_apply_right, relabelRowsEquiv_apply_bottom, relabelRowsEquiv_apply_top,
    Equiv.symm_apply_apply, Grid.mem_cIco_finRotate_finRotate]

/-! ### Column relabeling -/

/-- Relabeling the columns of two grid states transports the oriented rectangles between them:
the relabeled states exchange rows at the renamed side columns. -/
def relabelColumnsEquiv (κ : Equiv.Perm (Fin n)) (x y : GridState n) :
    GridRectangleBetween x y ≃
      GridRectangleBetween (x.relabelColumns κ) (y.relabelColumns κ) where
  toFun R :=
    { left := κ R.left
      right := κ R.right
      left_ne_right := κ.injective.ne R.left_ne_right
      map_left := by simp [R.map_left]
      map_right := by simp [R.map_right]
      map_of_ne := fun c hl hr => by
        simpa using R.map_of_ne (κ.symm c) (fun h => hl (by simp [← h]))
          (fun h => hr (by simp [← h])) }
  invFun S :=
    { left := κ.symm S.left
      right := κ.symm S.right
      left_ne_right := κ.symm.injective.ne S.left_ne_right
      map_left := by simpa using S.map_left
      map_right := by simpa using S.map_right
      map_of_ne := fun c hl hr => by
        simpa using S.map_of_ne (κ c) (fun h => hl (by simp [← h]))
          (fun h => hr (by simp [← h])) }
  left_inv _ := eq_of_sides (κ.symm_apply_apply _) (κ.symm_apply_apply _)
  right_inv _ := eq_of_sides (κ.apply_symm_apply _) (κ.apply_symm_apply _)

/-- Column relabeling renames the initial side column. -/
@[simp]
theorem relabelColumnsEquiv_apply_left (κ : Equiv.Perm (Fin n)) (R : GridRectangleBetween x y) :
    (relabelColumnsEquiv κ x y R).left = κ R.left :=
  (rfl)

/-- Column relabeling renames the terminal side column. -/
@[simp]
theorem relabelColumnsEquiv_apply_right (κ : Equiv.Perm (Fin n))
    (R : GridRectangleBetween x y) :
    (relabelColumnsEquiv κ x y R).right = κ R.right :=
  (rfl)

/-- The inverse of column relabeling renames the initial side column back. -/
@[simp]
theorem relabelColumnsEquiv_symm_apply_left (κ : Equiv.Perm (Fin n))
    (S : GridRectangleBetween (x.relabelColumns κ) (y.relabelColumns κ)) :
    ((relabelColumnsEquiv κ x y).symm S).left = κ.symm S.left :=
  (rfl)

/-- The inverse of column relabeling renames the terminal side column back. -/
@[simp]
theorem relabelColumnsEquiv_symm_apply_right (κ : Equiv.Perm (Fin n))
    (S : GridRectangleBetween (x.relabelColumns κ) (y.relabelColumns κ)) :
    ((relabelColumnsEquiv κ x y).symm S).right = κ.symm S.right :=
  (rfl)

/-- Column relabeling keeps the initial side row. -/
@[simp]
theorem relabelColumnsEquiv_apply_bottom (κ : Equiv.Perm (Fin n))
    (R : GridRectangleBetween x y) :
    (relabelColumnsEquiv κ x y R).bottom = R.bottom := by
  simp [bottom_def]

/-- Column relabeling keeps the terminal side row. -/
@[simp]
theorem relabelColumnsEquiv_apply_top (κ : Equiv.Perm (Fin n)) (R : GridRectangleBetween x y) :
    (relabelColumnsEquiv κ x y R).top = R.top := by
  simp [top_def]

/-- A cyclic permutation of the columns preserves and reflects emptiness of a rectangle. -/
@[simp]
theorem isEmpty_relabelColumnsEquiv_finRotate (R : GridRectangleBetween x y) :
    (relabelColumnsEquiv (finRotate n) x y R).IsEmpty ↔ R.IsEmpty := by
  simp only [isEmpty_iff_forall_notMem_cIoo, relabelColumnsEquiv_apply_left,
    relabelColumnsEquiv_apply_right, relabelColumnsEquiv_apply_bottom,
    relabelColumnsEquiv_apply_top, GridState.relabelColumns_apply]
  refine ⟨fun h c hc => ?_, fun h c hc => ?_⟩
  · have := h (finRotate n c) ((Grid.mem_cIoo_finRotate_finRotate _ _ _).mpr hc)
    rwa [Equiv.symm_apply_apply] at this
  · obtain ⟨c, rfl⟩ := (finRotate n).surjective c
    rw [Equiv.symm_apply_apply]
    exact h c ((Grid.mem_cIoo_finRotate_finRotate _ _ _).mp hc)

/-- A cyclic permutation of the columns rotates the squares a rectangle covers in the column
direction. -/
theorem mem_coveredSquares_relabelColumnsEquiv_finRotate (R : GridRectangleBetween x y)
    (p : Fin n × Fin n) :
    p ∈ (relabelColumnsEquiv (finRotate n) x y R).toGridRectangle.coveredSquares ↔
      ((finRotate n).symm p.1, p.2) ∈ R.toGridRectangle.coveredSquares := by
  obtain ⟨c, r⟩ := p
  obtain ⟨c, rfl⟩ := (finRotate n).surjective c
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, relabelColumnsEquiv_apply_left,
    relabelColumnsEquiv_apply_right, relabelColumnsEquiv_apply_bottom,
    relabelColumnsEquiv_apply_top, Equiv.symm_apply_apply, Grid.mem_cIco_finRotate_finRotate]

end GridRectangleBetween

end TauCeti
