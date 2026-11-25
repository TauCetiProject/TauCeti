/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PolygonalTable
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Convex.Between
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The frontier of a polygonal table is a null set

A segment in a finite-dimensional real vector space of dimension at least two lies in a proper
affine subspace, its affine span, so it is null for every additive Haar measure
(`MeasureTheory.Measure.addHaar_segment`). The frontier of a polygonal billiard table is the
union of its finitely many sides, which are segments in `ℂ`, so it is a Lebesgue-null set
(`TauCeti.PolygonalTable.volume_frontier_carrier`), and the table and its interior have the same
area (`TauCeti.PolygonalTable.volume_interior_carrier`). The positions on the frontier therefore
carry no mass for the Liouville measure of the table.

## References

* N. Chernov, R. Markarian, *Chaotic Billiards*, Mathematical Surveys and Monographs 127, AMS
  (2006), Chapter 2.
-/

public section

open MeasureTheory Set Module

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- **A segment is null** for every additive Haar measure on a real vector space of dimension at
least two: it lies in the affine line through its endpoints. -/
theorem addHaar_segment (μ : Measure E) [μ.IsAddHaarMeasure] (hE : 2 ≤ finrank ℝ E) (a b : E) :
    μ (segment ℝ a b) = 0 := by
  have hne : line[ℝ, a, b] ≠ ⊤ := by
    intro h
    have hdir := congrArg AffineSubspace.direction h
    rw [direction_affineSpan, AffineSubspace.direction_top, vectorSpan_pair] at hdir
    have hle := finrank_span_le_card (R := ℝ) ({a -ᵥ b} : Set E)
    rw [hdir, finrank_top] at hle
    simp at hle
    omega
  exact measure_mono_null (fun x hx => (mem_segment_iff_wbtw.1 hx).mem_affineSpan)
    (addHaar_affineSubspace μ _ hne)

end MeasureTheory.Measure

namespace TauCeti.PolygonalTable

variable (T : PolygonalTable)

/-- **The frontier of a polygonal table is Lebesgue-null**: it is the union of the finitely many
sides of the table, which are segments. -/
theorem volume_frontier_carrier : volume (frontier T.carrier) = 0 := by
  rw [frontier_eq_iUnion_side, measure_iUnion_null_iff]
  intro s
  rw [side_eq_segment]
  exact Measure.addHaar_segment volume Complex.finrank_real_complex.ge _ _

/-- A polygonal table and its interior have the same area. -/
theorem volume_interior_carrier : volume (interior T.carrier) = volume T.carrier :=
  measure_congr (interior_ae_eq_of_null_frontier T.volume_frontier_carrier)

end TauCeti.PolygonalTable
