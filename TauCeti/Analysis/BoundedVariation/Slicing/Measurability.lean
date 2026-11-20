/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Slicing.Basic
import TauCeti.Analysis.BoundedVariation.Real

/-!
# Null-measurability of noninterval sections

This file uses `TauCeti.aemeasurable_perimeter_lineSection` from
`TauCeti.Analysis.BoundedVariation.Slicing.Basic` to prove that the family of noninterval
sections of a finite-volume null-measurable set is null-measurable. No finiteness assumption
on the ambient perimeter is needed.

In one dimension, finite-length sets with perimeter at most two are precisely intervals up to
null sets, including the empty interval. Thus the family of sections which are not intervals
up to null sets is null-measurable (`TauCeti.nullMeasurableSet_noninterval_lineSection`). This
allows slicing-excess estimates to be applied to the entire family of noninterval sections,
rather than just a supplied measurable subfamily.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For each fixed unit direction, the set of transverse points whose sections do not agree
almost everywhere with any interval is null-measurable. -/
theorem nullMeasurableSet_noninterval_lineSection {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    NullMeasurableSet {y : (ℝ ∙ e)ᗮ | ∀ I : Set ℝ, I.OrdConnected →
      ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I} volume := by
  have hm := nullMeasurableSet_lt (aemeasurable_const (b := (2 : ℝ≥0∞)))
    (aemeasurable_perimeter_lineSection hs hfin e he)
  refine hm.congr ?_
  filter_upwards [ae_nullMeasurableSet_lineSection e he hs,
    ae_volume_lineSection_lt_top e he hs hfin] with y hym hyfin
  simp only [← not_le, Real.perimeter_le_two_iff hym hyfin.ne, not_exists, not_and]

end TauCeti
