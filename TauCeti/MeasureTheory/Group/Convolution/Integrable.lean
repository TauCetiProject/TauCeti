/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# First moments of convolutions

`MeasureTheory.Measure.integrable_id_conv_iff` states that the convolution of two nonzero finite
measures has a finite first moment exactly when both factors do. This allows an independent
summand with an infinite first moment to be detected from the law of the sum, without a moment
assumption on the other summand.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

/-- A convolution of nonzero finite measures has an integrable identity exactly when both
factors do. -/
@[simp]
theorem integrable_id_conv_iff {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (μ ν : Measure E)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    Integrable id (μ ∗ ν) ↔ Integrable id μ ∧ Integrable id ν := by
  let _ : NeZero μ := ⟨hμ⟩
  let _ : NeZero ν := ⟨hν⟩
  rw [Measure.conv, integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.prod_left_ae.exists
    obtain ⟨x, hx⟩ := h.prod_right_ae.exists
    exact ⟨integrable_add_const_iff.mp hy, integrable_const_add_iff.mp hx⟩
  · rintro ⟨hμ, hν⟩
    exact (hμ.comp_fst ν).add (hν.comp_snd μ)

end MeasureTheory.Measure
