/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.Probability.Cdf

/-!
# Topological support of real Gaussian measures

This file identifies the support of `ProbabilityTheory.gaussianReal` at every variance. A
nondegenerate real Gaussian has full support, while the zero-variance law is supported at its
mean.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- The support of `gaussianReal m v` is all of `ℝ` at nonzero variance and the singleton
containing its mean at zero variance. -/
@[simp]
theorem support_gaussianReal (m : ℝ) (v : ℝ≥0) :
    (gaussianReal m v).support = if v = 0 then {m} else univ := by
  by_cases hv : v = 0
  · subst v
    simp [gaussianReal_zero_var, Measure.support_dirac]
  · simp only [hv, ite_false]
    exact Measure.support_eq_univ_of_strictMono_cdf _ (strictMono_cdf_gaussianReal m hv)

end TauCeti.Probability
