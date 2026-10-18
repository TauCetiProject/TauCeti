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
def rectangleRe (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    Division .re (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e)) :=
  { single .re (GraphCell.rectangle a b c e hab hce.le) with
    covers := by simp }

/-- The independently constructed one-cell type-II division of the same rectangle. -/
def rectangleIm (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    Division .im (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e)) :=
  { single .im (GraphCell.rectangle c e a b hce hab.le) with
    covers := by
      rw [(single .im (GraphCell.rectangle c e a b hce hab.le)).covers]
      ext z
      simp [GraphCell.region_im, mem_verticalRegion, mem_horizontalRegion, and_comm] }

@[simp]
theorem rectangleRe_cells (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangleRe a b c e hab hce).cells = {GraphCell.rectangle a b c e hab hce.le} :=
  single_cells .re _

@[simp]
theorem rectangleIm_cells (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangleIm a b c e hab hce).cells = {GraphCell.rectangle c e a b hce hab.le} :=
  single_cells .im _

/-- The type-I rectangle division has the canonical four-edge rectangle boundary. -/
@[simp]
theorem boundary_rectangleRe (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangleRe a b c e hab hce).boundary =
      BoundaryChain.cellBoundary .re a b (fun _ ↦ c) (fun _ ↦ e)
        continuousOn_const continuousOn_const := by
  rw [boundary_def, rectangleRe_cells, ← single_cells .re _, ← boundary_def, boundary_single]
  simp [GraphCell.boundary_def]

/-- The type-II rectangle division has the canonical four-edge rectangle boundary. -/
@[simp]
theorem boundary_rectangleIm (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangleIm a b c e hab hce).boundary =
      BoundaryChain.cellBoundary .im c e (fun _ ↦ a) (fun _ ↦ b)
        continuousOn_const continuousOn_const := by
  rw [boundary_def, rectangleIm_cells, ← single_cells .im _, ← boundary_def, boundary_single]
  simp [GraphCell.boundary_def]

/-- The two independent rectangle divisions have the same actual boundary chain. -/
theorem boundary_rectangleRe_eq_rectangleIm (a b c e : ℝ) (hab : a < b) (hce : c < e) :
    (rectangleRe a b c e hab hce).boundary = (rectangleIm a b c e hab hce).boundary := by
  rw [boundary_rectangleRe, boundary_rectangleIm]
  exact BoundaryChain.cellBoundary_rectangle_re_eq_im a b c e

/-- The type-I and type-II rectangular divisions have a common cycle and both geometric
comparison certificates, for every ambient comparison set. -/
theorem exists_rectangle_common_boundary (a b c e : ℝ) (hab : a < b) (hce : c < e)
    (U : Set ℂ) : ∃ C : BoundaryChain, BoundaryChain.boundary C = 0 ∧
      BoundaryChain.NullChain .re U ((rectangleRe a b c e hab hce).boundary - C) ∧
      BoundaryChain.NullChain .im U ((rectangleIm a b c e hab hce).boundary - C) := by
  refine ⟨(rectangleRe a b c e hab hce).boundary, boundary_boundary _, ?_, ?_⟩
  · simpa only [sub_self] using (BoundaryChain.NullChain.zero : BoundaryChain.NullChain .re U 0)
  · rw [← boundary_rectangleRe_eq_rectangleIm, sub_self]
    exact .zero

end TauCeti.Green.Division
