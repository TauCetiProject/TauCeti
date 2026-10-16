/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Cell
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite graph-cell divisions

A division is a finite set of graph cells covering its region, with pairwise area-null
intersections. No connectedness or simple-connectedness is imposed. Vertical and horizontal
divisions are independent presentations. Their boundary is the integer sum of their actual
four-path cell boundaries, before any cancellation or geometric comparison.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- A finite type-I or type-II division, permitting disconnected regions and finite holes. -/
@[ext]
structure Division (d : Coordinate) (D : Set ℂ) where
  /-- The finitely many graph cells presenting the region. -/
  cells : Finset GraphCell
  covers : (⋃ K ∈ cells, K.region d) = D
  aedisjoint : (cells : Set GraphCell).Pairwise
    (fun K L ↦ AEDisjoint volume (K.region d) (L.region d))

namespace Division

variable {d : Coordinate} {D : Set ℂ}

/-- Every cell of a division lies in its region. -/
theorem region_subset (V : Division d D) {K : GraphCell} (hK : K ∈ V.cells) :
    K.region d ⊆ D := by
  rw [← V.covers]
  exact subset_iUnion₂_of_subset K hK Subset.rfl

/-- A finitely divided region is compact. -/
theorem isCompact (V : Division d D) : IsCompact D := by
  rw [← V.covers]
  exact V.cells.isCompact_biUnion (fun K _ ↦ K.isCompact_region d)

/-- A finitely divided region is measurable. -/
theorem measurableSet (V : Division d D) : MeasurableSet D := V.isCompact.measurableSet

/-- Cellwise integrability is equivalent to integrability on the whole divided region. -/
theorem integrableOn_iff (V : Division d D) {f : ℂ → ℝ} :
    IntegrableOn f D ↔ ∀ K ∈ V.cells, IntegrableOn f (K.region d) := by
  conv_lhs => rw [← V.covers]
  exact integrableOn_finset_iUnion

/-- Pairwise area-null cell overlaps make area integrals additive over the division. -/
theorem integral_eq_sum (V : Division d D) {f : ℂ → ℝ}
    (hf : ∀ K ∈ V.cells, IntegrableOn f (K.region d)) :
    (∫ z in D, f z) = ∑ K ∈ V.cells, ∫ z in K.region d, f z := by
  simpa only [V.covers] using
    TauCeti.MeasureTheory.integral_biUnion_finset₀ V.cells V.aedisjoint
      (fun K _ ↦ (K.measurableSet_region d).nullMeasurableSet)
      (by simpa only [V.covers] using V.integrableOn_iff.mpr hf)

/-- The sum of the actual signed cell-boundary chains. -/
def boundary (V : Division d D) : BoundaryChain := ∑ K ∈ V.cells, K.boundary d

/-- The division boundary is the finite sum of its oriented cell boundaries. -/
theorem boundary_def (V : Division d D) : V.boundary = ∑ K ∈ V.cells, K.boundary d := (rfl)

/-- Every division boundary is an endpoint cycle. -/
@[simp]
theorem boundary_boundary (V : Division d D) : BoundaryChain.boundary V.boundary = 0 := by
  simp [boundary]

/-- Every graph cell is its own one-cell division, giving nondegenerate rectangular examples. -/
def single (d : Coordinate) (K : GraphCell) : Division d (K.region d) where
  cells := {K}
  covers := by simp
  aedisjoint := by simp

@[simp]
theorem single_cells (d : Coordinate) (K : GraphCell) : (single d K).cells = {K} := (rfl)

@[simp]
theorem boundary_single (d : Coordinate) (K : GraphCell) :
    (single d K).boundary = K.boundary d := by
  simp [boundary]

end Division
end TauCeti.Green
