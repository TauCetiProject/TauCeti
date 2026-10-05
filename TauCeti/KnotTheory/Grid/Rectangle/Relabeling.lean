/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Squares
public import TauCeti.KnotTheory.Grid.Rotation

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

The half-turn `GridState.halfTurn` relabels both the rows and the columns by negation modulo `n`,
which reverses the cyclic order. Composed with exchanging the two side columns
(`GridRectangleBetween.swapSides`), it transports rectangles again, and the transported rectangle
is empty exactly when the original one is; it covers the squares obtained by reversing both
coordinates with `Fin.rev`, which are where `GridDiagram.rotate` moves the markings.

## Main definitions

* `TauCeti.GridRectangleBetween.relabelRowsEquiv`: rectangles from `x` to `y` correspond to
  rectangles from `x.relabelRows ρ` to `y.relabelRows ρ`, with the same side columns.
* `TauCeti.GridRectangleBetween.relabelColumnsEquiv`: rectangles from `x` to `y` correspond to
  rectangles from `x.relabelColumns κ` to `y.relabelColumns κ`, with side columns renamed by `κ`.
* `TauCeti.GridRectangleBetween.halfTurnEquiv`: rectangles from `x` to `y` correspond to
  rectangles from `x.halfTurn` to `y.halfTurn`.

## Main results

* `TauCeti.GridRectangleBetween.isEmpty_relabelRowsEquiv_finRotate`,
  `TauCeti.GridRectangleBetween.isEmpty_relabelColumnsEquiv_finRotate`: a cyclic permutation
  preserves and reflects emptiness.
* `TauCeti.GridRectangleBetween.mem_coveredSquares_relabelRowsEquiv_finRotate`,
  `TauCeti.GridRectangleBetween.mem_coveredSquares_relabelColumnsEquiv_finRotate`: a cyclic
  permutation rotates the covered squares.
* `TauCeti.GridRectangleBetween.isEmpty_halfTurnEquiv`,
  `TauCeti.GridRectangleBetween.mem_coveredSquares_halfTurnEquiv`: the half-turn preserves and
  reflects emptiness, and reverses the covered squares.

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
  left_inv _ := GridRectangleBetween.ext rfl rfl
  right_inv _ := GridRectangleBetween.ext rfl rfl

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

/-- The inverse of row relabeling renames the initial side row back. -/
@[simp]
theorem relabelRowsEquiv_symm_apply_bottom (ρ : Equiv.Perm (Fin n))
    (S : GridRectangleBetween (x.relabelRows ρ) (y.relabelRows ρ)) :
    ((relabelRowsEquiv ρ x y).symm S).bottom = ρ.symm S.bottom := by
  simp [bottom_def]

/-- The inverse of row relabeling renames the terminal side row back. -/
@[simp]
theorem relabelRowsEquiv_symm_apply_top (ρ : Equiv.Perm (Fin n))
    (S : GridRectangleBetween (x.relabelRows ρ) (y.relabelRows ρ)) :
    ((relabelRowsEquiv ρ x y).symm S).top = ρ.symm S.top := by
  simp [top_def]

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
  left_inv _ := GridRectangleBetween.ext (κ.symm_apply_apply _) (κ.symm_apply_apply _)
  right_inv _ := GridRectangleBetween.ext (κ.apply_symm_apply _) (κ.apply_symm_apply _)

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

/-- The inverse of column relabeling keeps the initial side row. -/
@[simp]
theorem relabelColumnsEquiv_symm_apply_bottom (κ : Equiv.Perm (Fin n))
    (S : GridRectangleBetween (x.relabelColumns κ) (y.relabelColumns κ)) :
    ((relabelColumnsEquiv κ x y).symm S).bottom = S.bottom := by
  simp [bottom_def]

/-- The inverse of column relabeling keeps the terminal side row. -/
@[simp]
theorem relabelColumnsEquiv_symm_apply_top (κ : Equiv.Perm (Fin n))
    (S : GridRectangleBetween (x.relabelColumns κ) (y.relabelColumns κ)) :
    ((relabelColumnsEquiv κ x y).symm S).top = S.top := by
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

/-! ### Half-turn -/

/-- The half-turn `GridState.halfTurn` transports the oriented rectangles between two grid
states. It negates the side columns modulo `n`, which reverses their cyclic order, so the image
of the terminal side column becomes the initial one: the rectangle is relabeled in its columns
and rows by negation and then has its two sides exchanged. -/
def halfTurnEquiv (x y : GridState n) :
    GridRectangleBetween x y ≃ GridRectangleBetween x.halfTurn y.halfTurn where
  toFun R :=
    { left := finRotate n R.right.rev
      right := finRotate n R.left.rev
      left_ne_right := fun h => R.left_ne_right (Fin.rev_injective ((finRotate n).injective h)).symm
      map_left := by
        rw [GridState.halfTurn_apply_finRotate_rev, GridState.halfTurn_apply_finRotate_rev,
          R.map_right]
      map_right := by
        rw [GridState.halfTurn_apply_finRotate_rev, GridState.halfTurn_apply_finRotate_rev,
          R.map_left]
      map_of_ne := fun c hl hr => by
        have hc := Fin.finRotate_rev_finRotate_rev c
        rw [← hc, GridState.halfTurn_apply_finRotate_rev, GridState.halfTurn_apply_finRotate_rev,
          R.map_of_ne]
        · exact fun h => hr (by rw [← hc, h])
        · exact fun h => hl (by rw [← hc, h]) }
  invFun S :=
    { left := finRotate n S.right.rev
      right := finRotate n S.left.rev
      left_ne_right := fun h => S.left_ne_right (Fin.rev_injective ((finRotate n).injective h)).symm
      map_left := by
        have h := S.map_right
        rw [← Fin.finRotate_rev_finRotate_rev S.right, ← Fin.finRotate_rev_finRotate_rev S.left,
          GridState.halfTurn_apply_finRotate_rev, GridState.halfTurn_apply_finRotate_rev] at h
        exact Fin.rev_injective ((finRotate n).injective h)
      map_right := by
        have h := S.map_left
        rw [← Fin.finRotate_rev_finRotate_rev S.right, ← Fin.finRotate_rev_finRotate_rev S.left,
          GridState.halfTurn_apply_finRotate_rev, GridState.halfTurn_apply_finRotate_rev] at h
        exact Fin.rev_injective ((finRotate n).injective h)
      map_of_ne := fun c hl hr => by
        have h := S.map_of_ne (finRotate n c.rev)
          (fun h => hr (by rw [← h, Fin.finRotate_rev_finRotate_rev]))
          (fun h => hl (by rw [← h, Fin.finRotate_rev_finRotate_rev]))
        rw [GridState.halfTurn_apply_finRotate_rev, GridState.halfTurn_apply_finRotate_rev] at h
        exact Fin.rev_injective ((finRotate n).injective h) }
  left_inv R :=
    GridRectangleBetween.ext (Fin.finRotate_rev_finRotate_rev _) (Fin.finRotate_rev_finRotate_rev _)
  right_inv S :=
    GridRectangleBetween.ext (Fin.finRotate_rev_finRotate_rev _) (Fin.finRotate_rev_finRotate_rev _)

/-- The initial side column of the half-turned rectangle is the negated terminal side column. -/
@[simp]
theorem halfTurnEquiv_apply_left (R : GridRectangleBetween x y) :
    (halfTurnEquiv x y R).left = finRotate n R.right.rev :=
  (rfl)

/-- The terminal side column of the half-turned rectangle is the negated initial side column. -/
@[simp]
theorem halfTurnEquiv_apply_right (R : GridRectangleBetween x y) :
    (halfTurnEquiv x y R).right = finRotate n R.left.rev :=
  (rfl)

/-- The inverse half-turn negates the terminal side column into the initial one. -/
@[simp]
theorem halfTurnEquiv_symm_apply_left (S : GridRectangleBetween x.halfTurn y.halfTurn) :
    ((halfTurnEquiv x y).symm S).left = finRotate n S.right.rev :=
  (rfl)

/-- The inverse half-turn negates the initial side column into the terminal one. -/
@[simp]
theorem halfTurnEquiv_symm_apply_right (S : GridRectangleBetween x.halfTurn y.halfTurn) :
    ((halfTurnEquiv x y).symm S).right = finRotate n S.left.rev :=
  (rfl)

/-- The initial side row of the half-turned rectangle is the negated terminal side row. -/
@[simp]
theorem halfTurnEquiv_apply_bottom (R : GridRectangleBetween x y) :
    (halfTurnEquiv x y R).bottom = finRotate n R.top.rev := by
  rw [bottom_def, halfTurnEquiv_apply_left, GridState.halfTurn_apply_finRotate_rev, top_def]

/-- The terminal side row of the half-turned rectangle is the negated initial side row. -/
@[simp]
theorem halfTurnEquiv_apply_top (R : GridRectangleBetween x y) :
    (halfTurnEquiv x y R).top = finRotate n R.bottom.rev := by
  rw [top_def, halfTurnEquiv_apply_right, GridState.halfTurn_apply_finRotate_rev, bottom_def]

/-- The half-turn preserves and reflects emptiness of a rectangle. -/
@[simp]
theorem isEmpty_halfTurnEquiv (R : GridRectangleBetween x y) :
    (halfTurnEquiv x y R).IsEmpty ↔ R.IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo, isEmpty_iff_forall_notMem_cIoo, halfTurnEquiv_apply_left,
    halfTurnEquiv_apply_right, halfTurnEquiv_apply_bottom, halfTurnEquiv_apply_top]
  constructor
  · intro h c hc
    have := h (finRotate n c.rev) ((Grid.mem_cIoo_finRotate_rev _ _ _).mpr hc)
    rwa [GridState.halfTurn_apply_finRotate_rev, Grid.mem_cIoo_finRotate_rev] at this
  · intro h c hc
    rw [← Fin.finRotate_rev_finRotate_rev c, Grid.mem_cIoo_finRotate_rev] at hc
    rw [← Fin.finRotate_rev_finRotate_rev c, GridState.halfTurn_apply_finRotate_rev,
      Grid.mem_cIoo_finRotate_rev]
    exact h _ hc

/-- The half-turn reverses both coordinates of the squares a rectangle covers. -/
theorem mem_coveredSquares_halfTurnEquiv (R : GridRectangleBetween x y) (p : Fin n × Fin n) :
    p ∈ (halfTurnEquiv x y R).toGridRectangle.coveredSquares ↔
      (p.1.rev, p.2.rev) ∈ R.toGridRectangle.coveredSquares := by
  obtain ⟨c, r⟩ := p
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, halfTurnEquiv_apply_left,
    halfTurnEquiv_apply_right, halfTurnEquiv_apply_bottom, halfTurnEquiv_apply_top]
  rw [← Grid.rev_mem_cIco_finRotate_rev R.left R.right c.rev,
    ← Grid.rev_mem_cIco_finRotate_rev R.bottom R.top r.rev, Fin.rev_rev, Fin.rev_rev]

end GridRectangleBetween

end TauCeti
