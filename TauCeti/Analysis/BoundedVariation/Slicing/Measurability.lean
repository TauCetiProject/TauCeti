/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Slicing.Basic
import TauCeti.Analysis.BoundedVariation.Countable
import TauCeti.Analysis.BoundedVariation.Real

/-!
# Measurable perimeter and noninterval sections

The perimeters of parallel line sections of a finite-volume null-measurable set depend
measurably, up to null sets, on the transverse parameter. No finiteness assumption on the
ambient perimeter is needed. The same holds for the variation of sections of an integrable
function.

In one dimension, finite-length sets with perimeter at most two are precisely intervals up to
null sets, including the empty interval. Thus the family of sections which are not intervals
up to null sets is null-measurable. This allows slicing-excess estimates to be applied to the
entire family of noninterval sections, rather than just a supplied measurable subfamily.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The variation of the restrictions of an integrable function to parallel lines is a.e.
measurable in the transverse coordinate, even if the ambient variation is infinite. -/
theorem aemeasurable_totalVariationOn_line {u : E → ℝ} (hu : Integrable u)
    (e : E) (he : ‖e‖ = 1) :
    AEMeasurable (fun y : (ℝ ∙ e)ᗮ ↦
      totalVariationOn volume ⊤ (fun t : ℝ ↦ u ((y : E) + t • e))) volume := by
  have hint := (measurePreserving_orthogonalLineEquiv e he).integrable_comp_of_integrable hu
  simpa only [Function.comp_apply, orthogonalLineEquiv_apply] using
    aemeasurable_totalVariationOn (μ := volume) ⊤ hint.aestronglyMeasurable hint.prod_right_ae

/-- Perimeters of parallel sections of a null-measurable finite-volume set are a.e. measurable
in the transverse coordinate. Infinite perimeters are allowed. -/
theorem aemeasurable_perimeter_lineSection {s : Set E} (hs : NullMeasurableSet s volume)
    (hfin : volume s ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    AEMeasurable (fun y : (ℝ ∙ e)ᗮ ↦
      perimeter volume ⊤ {t : ℝ | (y : E) + t • e ∈ s}) volume := by
  have hu : Integrable (s.indicator (1 : E → ℝ)) volume :=
    (integrableOn_const hfin).integrable_indicator₀ hs
  have hm := aemeasurable_totalVariationOn_line hu e he
  have hline (y : (ℝ ∙ e)ᗮ) : (fun t : ℝ ↦ s.indicator (1 : E → ℝ) ((y : E) + t • e)) =
      {t : ℝ | (y : E) + t • e ∈ s}.indicator 1 :=
    funext fun _ ↦ (indicator_comp_right (fun t : ℝ ↦ (y : E) + t • e)).symm
  simpa only [perimeter_def, hline] using hm

/-- For each fixed unit direction, the set of transverse points whose sections do not agree
almost everywhere with any interval is null-measurable. The exceptional sets in the section
measurability and finite-length statements may depend on the direction. -/
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
