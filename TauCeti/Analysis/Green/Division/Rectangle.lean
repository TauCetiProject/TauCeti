/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Green

/-!
# Rectangular divisions and their common boundary

The vertical and horizontal one-cell divisions of a rectangle are constructed independently.
Their boundary chains are proved equal as sums of existing paths, giving geometric comparison
certificates without mentioning a field or an integral. Positive side lengths give concrete
nondegenerate witnesses for the finite-division Green theorem.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.Division

/-- The one-cell type-I division of a rectangle. -/
def rectangle_re (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    Division .re (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e)) where
  cells := {GraphCell.rectangle a b c e hab hce.le}
  covers := by simp
  aedisjoint := by simp

/-- The independently constructed one-cell type-II division of the same rectangle. -/
def rectangle_im (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    Division .im (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e)) where
  cells := {GraphCell.rectangle c e a b hce hab.le}
  covers := by
    ext z
    simp [mem_verticalRegion, mem_horizontalRegion, and_comm]
  aedisjoint := by simp

@[simp]
theorem rectangle_re_cells (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangle_re a b c e hab hce).cells = {GraphCell.rectangle a b c e hab hce.le} := (rfl)

@[simp]
theorem rectangle_im_cells (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangle_im a b c e hab hce).cells = {GraphCell.rectangle c e a b hce hab.le} := (rfl)

/-- The type-I rectangle division has the canonical four-edge rectangle boundary. -/
@[simp]
theorem boundary_rectangle_re (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangle_re a b c e hab hce).boundary =
      BoundaryChain.cellBoundary .re a b (fun _ ↦ c) (fun _ ↦ e)
        continuousOn_const continuousOn_const := by
  simp [boundary_def, GraphCell.boundary_def]

/-- The type-II rectangle division has the canonical four-edge rectangle boundary. -/
@[simp]
theorem boundary_rectangle_im (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangle_im a b c e hab hce).boundary =
      BoundaryChain.cellBoundary .im c e (fun _ ↦ a) (fun _ ↦ b)
        continuousOn_const continuousOn_const := by
  simp [boundary_def, GraphCell.boundary_def]

/-- The two independent rectangle divisions have the same actual boundary chain. -/
theorem boundary_rectangle_re_eq_im (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangle_re a b c e hab hce).boundary = (rectangle_im a b c e hab hce).boundary := by
  rw [boundary_rectangle_re, boundary_rectangle_im]
  exact BoundaryChain.cellBoundary_rectangle_re_eq_im a b c e

/-- The type-I and type-II rectangular divisions have a common cycle and both geometric
comparison certificates, for every ambient comparison set. -/
theorem exists_rectangle_common_boundary (a b c e : ℝ) (hab : a < b) (hce : c < e)
    (U : Set ℂ) : ∃ C : BoundaryChain, BoundaryChain.boundary C = 0 ∧
      BoundaryChain.NullChain .re U ((rectangle_re a b c e hab hce).boundary - C) ∧
      BoundaryChain.NullChain .im U ((rectangle_im a b c e hab hce).boundary - C) := by
  refine ⟨(rectangle_re a b c e hab hce).boundary, boundary_boundary _, ?_, ?_⟩
  · simpa only [sub_self] using (BoundaryChain.NullChain.zero : BoundaryChain.NullChain .re U 0)
  · rw [← boundary_rectangle_re_eq_im, sub_self]
    exact .zero

end TauCeti.Green.Division
