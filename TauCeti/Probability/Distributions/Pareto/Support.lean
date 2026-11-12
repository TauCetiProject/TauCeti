/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Pareto.PDF

/-!
# Topological support of the Pareto distribution

This file identifies the support of a Pareto law at valid parameters. Its density is positive
from the threshold onward and vanishes below it, so its support is the closed upper half-line.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- A Pareto law with positive threshold and shape has support `[t, ∞)`. -/
@[simp]
theorem support_paretoMeasure {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (paretoMeasure t r).support = Ici t := by
  rw [paretoMeasure]
  calc
    (volume.withDensity (paretoPDF t r)).support = closure (Ioi t) :=
      Measure.support_withDensity_eq_closure_of_subset (measurable_paretoPDF t r) isOpen_Ioi
        (fun x hx ↦ by
          rw [Function.mem_support, paretoPDF, ENNReal.ofReal_ne_zero_iff]
          exact paretoPDFReal_pos ht hr hx.le)
        (fun x hx ↦ by
          rw [closure_Ioi t]
          by_contra h
          exact hx (paretoPDF_of_lt (lt_of_not_ge h)))
    _ = Ici t := closure_Ioi t

end TauCeti.Probability
