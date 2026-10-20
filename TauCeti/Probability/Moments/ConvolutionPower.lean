/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Group.ConvolutionPower
public import TauCeti.Probability.Moments.Basic

/-!
# Moment-generating functions of convolution powers

A measurable additive real observable turns an `n`-fold convolution into a sum of `n`
independent real variables. Its moment-generating function is therefore the `n`th power of
the single-jump transform. This identity also holds for totalized divergent integrals.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [AddMonoid α] [MeasurableAdd₂ α]

/-- The mgf of an additive real observable under a convolution power is the corresponding
power of its mgf. -/
theorem mgf_addMonoidHom_convolutionPower (μ : Measure α) [SFinite μ]
    (f : α →+ ℝ) (hf : Measurable f) (n : ℕ) (t : ℝ) :
    mgf f (μ.convolutionPower n) t = mgf f μ t ^ n := by
  rw [← mgf_id_map hf.aemeasurable, Measure.map_convolutionPower μ f hf,
    ← mgf_id_map hf.aemeasurable]
  induction n with
  | zero => simp [mgf]
  | succ n ih => simp [TauCeti.mgf_id_conv, ih, pow_succ]

end MeasureTheory.Measure
