/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Grid

/-!
# Divisions with a hole and with disconnected components

The eight squares surrounding an omitted central square form an actual rectangular frame.
Their common boundary cancels to the positively oriented outer contour minus the inner contour.
Two separated squares provide a disconnected witness for the same finite-division API.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.Examples

/-- The eight unit squares of the three-by-three frame with its central square omitted. -/
def frameSquares : Finset (ℤ × ℤ) :=
  {(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)}

/-- The frame is the outer closed square with the open central square removed. -/
theorem latticeRegion_frameSquares : latticeRegion frameSquares =
    verticalRegion 0 3 (fun _ ↦ 0) (fun _ ↦ 3) \
      {z : ℂ | z.re ∈ Ioo 1 2 ∧ z.im ∈ Ioo 1 2} := by
  ext z
  simp only [mem_latticeRegion, frameSquares, Finset.mem_insert, Finset.mem_singleton]
  simp only [exists_eq_or_imp, exists_eq_left, mem_latticeSquare, Int.cast_zero, Int.cast_one,
    Int.cast_ofNat, zero_add, mem_sdiff, mem_verticalRegion, mem_Icc, mem_ofPred_eq, mem_Ioo]
  grind

/-- The twelve-edge counterclockwise outer contour, subdivided at the integer lattice points. -/
def frameOuterBoundary : BoundaryChain :=
  (∑ i : Fin 3, BoundaryChain.ofPath (Path.segment (⟨i, 0⟩ : ℂ) ⟨(i : ℝ) + 1, 0⟩)) +
  (∑ i : Fin 3, BoundaryChain.ofPath (Path.segment (⟨3, i⟩ : ℂ) ⟨3, (i : ℝ) + 1⟩)) -
  (∑ i : Fin 3, BoundaryChain.ofPath (Path.segment (⟨i, 3⟩ : ℂ) ⟨(i : ℝ) + 1, 3⟩)) -
  (∑ i : Fin 3, BoundaryChain.ofPath (Path.segment (⟨0, i⟩ : ℂ) ⟨0, (i : ℝ) + 1⟩))

/-- All interior grid edges cancel, leaving the outer contour minus the central-square contour. -/
theorem boundary_frame (d : Coordinate) : (Division.lattice d frameSquares).boundary =
    frameOuterBoundary - (GraphCell.lattice .re (1, 1)).boundary .re := by
  rw [Division.boundary_lattice]
  let edge (p q : ℂ) : BoundaryChain := BoundaryChain.ofPath (Path.segment p q)
  have hedge (p q : ℂ) : BoundaryChain.ofPath (Path.segment p q) = edge p q := rfl
  simp only [frameSquares, GraphCell.boundary_lattice, frameOuterBoundary, hedge]
  norm_num [Fin.sum_univ_succ]
  abel

/-- The literal outer-minus-inner contour is a cycle and supports both geometric comparison
certificates for the two independently oriented divisions of the frame. -/
theorem frame_common_boundary (U : Set ℂ) :
    let C := frameOuterBoundary - (GraphCell.lattice .re (1, 1)).boundary .re
    BoundaryChain.boundary C = 0 ∧
      BoundaryChain.NullChain .re U ((Division.lattice .re frameSquares).boundary - C) ∧
      BoundaryChain.NullChain .im U ((Division.lattice .im frameSquares).boundary - C) := by
  dsimp only
  rw [← boundary_frame .re]
  refine ⟨Division.boundary_boundary _, ?_, ?_⟩
  · simpa only [sub_self] using (BoundaryChain.NullChain.zero : BoundaryChain.NullChain .re U 0)
  · rw [boundary_frame, boundary_frame, sub_self]
    exact .zero

/-- Two square components with a positive gap between them. -/
def separatedSquares : Finset (ℤ × ℤ) := {(0, 0), (3, 0)}

/-- The two-component region is the literal union of the two closed unit squares. -/
theorem latticeRegion_separatedSquares : latticeRegion separatedSquares =
    latticeSquare (0, 0) ∪ latticeSquare (3, 0) := by
  ext z
  simp [mem_latticeRegion, separatedSquares]

/-- The separated-square witness is genuinely disconnected. -/
theorem not_isPreconnected_latticeRegion_separatedSquares :
    ¬IsPreconnected (latticeRegion separatedSquares) := by
  intro h
  let L : Set ℂ := {z | z.re < 2}
  let R : Set ℂ := {z | 2 < z.re}
  have hL : IsOpen L := isOpen_lt Complex.continuous_re continuous_const
  have hR : IsOpen R := isOpen_lt continuous_const Complex.continuous_re
  have hLR : Disjoint L R := by
    apply Set.disjoint_left.mpr
    intro z hl hr
    have hl' : z.re < 2 := hl
    exact hl'.not_gt hr
  have hcover : latticeRegion separatedSquares ⊆ L ∪ R := by
    rw [latticeRegion_separatedSquares]
    intro z hz
    rcases hz with hz | hz
    · left
      have hz' := mem_latticeSquare.mp hz
      dsimp [L]
      norm_num at hz'
      linarith [hz'.1.2]
    · right
      have hz' := mem_latticeSquare.mp hz
      dsimp [R]
      norm_num at hz'
      linarith [hz'.1.1]
  rcases h.subset_or_subset hL hR hLR hcover with h | h
  · have hz : (⟨3, 0⟩ : ℂ) ∈ latticeRegion separatedSquares := by
      rw [latticeRegion_separatedSquares]
      right
      norm_num [mem_latticeSquare]
    have := h hz
    norm_num [L] at this
  · have hz : (0 : ℂ) ∈ latticeRegion separatedSquares := by
      rw [latticeRegion_separatedSquares]
      left
      norm_num [mem_latticeSquare]
    have := h hz
    norm_num [R] at this

/-- The disconnected example has two actual contour cycles and both directional comparison
certificates, with no connection inserted between its components. -/
theorem separatedSquares_common_boundary (U : Set ℂ) :
    let C := (GraphCell.lattice .re (0, 0)).boundary .re +
      (GraphCell.lattice .re (3, 0)).boundary .re
    BoundaryChain.boundary C = 0 ∧
      BoundaryChain.NullChain .re U ((Division.lattice .re separatedSquares).boundary - C) ∧
      BoundaryChain.NullChain .im U ((Division.lattice .im separatedSquares).boundary - C) := by
  have heq (d : Coordinate) : (Division.lattice d separatedSquares).boundary =
      (GraphCell.lattice .re (0, 0)).boundary .re +
        (GraphCell.lattice .re (3, 0)).boundary .re := by
    rw [Division.boundary_lattice]
    simp [separatedSquares]
  dsimp only
  rw [← heq .re]
  refine ⟨Division.boundary_boundary _, ?_, ?_⟩
  · simpa only [sub_self] using (BoundaryChain.NullChain.zero : BoundaryChain.NullChain .re U 0)
  · rw [heq, heq, sub_self]
    exact .zero

end TauCeti.Green.Examples
