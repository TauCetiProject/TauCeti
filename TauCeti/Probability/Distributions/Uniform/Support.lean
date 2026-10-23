/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Topological support of the interval-uniform distribution

The endpoint convention in the defining interval is measure-theoretically irrelevant: for a
nondegenerate interval, the uniform law has the whole closed interval as its topological support.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- A nondegenerate interval-uniform law has support equal to the closed interval between its
endpoints. -/
@[simp]
theorem support_uniformMeasure {a b : ℝ} (hab : a < b) :
    (uniformMeasure a b).support = Icc a b := by
  rw [uniformMeasure_eq_withDensity]
  calc
    (volume.withDensity fun x ↦ pdf.uniformPDF (Ioc a b) x volume).support = closure (Ioo a b) :=
      Measure.support_withDensity_eq_closure_of_subset measurable_uniformPDF_Ioc_volume isOpen_Ioo
        (fun x hx ↦ by
          rw [Function.mem_support, pdf.uniformPDF_ite, ite_eq_left ⟨hx.1, hx.2.le⟩]
          simp [Real.volume_Ioc])
        (fun x hx ↦ by
          rw [closure_Ioo hab.ne]
          constructor
          · by_contra hxa
            apply hx
            have hnot : x ∉ Ioc a b :=
              fun hxI ↦ (not_lt_of_ge (lt_of_not_ge hxa).le) hxI.1
            simp [pdf.uniformPDF_ite, hnot]
          · by_contra hxb
            apply hx
            have hnot : x ∉ Ioc a b := fun hxI ↦ hxb hxI.2
            simp [pdf.uniformPDF_ite, hnot])
    _ = Icc a b := closure_Ioo hab.ne

end TauCeti.Probability
