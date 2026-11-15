/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# Topological support of the gamma distribution

This file identifies the support of a gamma law with positive shape and rate. Although the law is
almost surely strictly positive, every neighbourhood of zero has positive mass, so the support is
the closed nonnegative half-line.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- A gamma law with positive shape and rate has topological support `[0, ∞)`. -/
@[simp]
theorem support_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (gammaMeasure a r).support = Ici 0 := by
  rw [gammaMeasure]
  calc
    (volume.withDensity (gammaPDF a r)).support = closure (Ioi 0) :=
      Measure.support_withDensity_eq_closure_of_subset
        (measurable_gammaPDF a r) isOpen_Ioi
        (fun x hx ↦ by
          rw [Function.mem_support, gammaPDF, ENNReal.ofReal_ne_zero_iff]
          exact gammaPDFReal_pos ha hr hx)
        (fun x hx ↦ by
          rw [closure_Ioi (0 : ℝ)]
          by_contra h
          exact hx (gammaPDF_of_neg (lt_of_not_ge h)))
    _ = Ici 0 := closure_Ioi (0 : ℝ)

end TauCeti.Probability
