/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.StudentT.Basic
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Topological support of Student t distributions

This file identifies the exact function support of the Student t density and the topological
support of the corresponding measure. For positive degrees of freedom the density is strictly
positive everywhere, so the law has full support. At nonpositive degrees of freedom the totalized
density and measure vanish and their supports are empty.

## Main results

* `TauCeti.Probability.support_studentTPDF` — the density has full function support exactly for
  positive degrees of freedom.
* `TauCeti.Probability.support_studentTMeasure` — the law has full topological support exactly for
  positive degrees of freedom.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 28.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The Student t density is nonzero everywhere at positive degrees of freedom and vanishes
everywhere at nonpositive degrees of freedom. -/
@[simp]
theorem support_studentTPDF (ν : ℝ) :
    Function.support (studentTPDF ν) = if 0 < ν then univ else ∅ := by
  split_ifs with hν
  · ext x
    simp only [Function.mem_support, mem_univ, iff_true, studentTPDF_eq_ofReal,
      ENNReal.ofReal_ne_zero_iff]
    exact studentTPDFReal_pos hν x
  · have hpdf : studentTPDF ν = 0 := by
      funext x
      exact studentTPDF_of_nonpos (not_lt.mp hν) x
    rw [hpdf, Function.support_zero]

/-- The topological support of a Student t law is the whole real line at positive degrees of
freedom and is empty for the totalized zero law at nonpositive degrees of freedom. -/
@[simp]
theorem support_studentTMeasure (ν : ℝ) :
    (studentTMeasure ν).support = if 0 < ν then univ else ∅ := by
  split_ifs with hν
  · have hsupp : Function.support (studentTPDF ν) = univ := by
      simp [hν]
    rw [studentTMeasure_def,
      Measure.support_withDensity_eq_closure (measurable_studentTPDF ν) isOpen_univ hsupp,
      closure_univ]
  · rw [studentTMeasure_of_nonpos (not_lt.mp hν), Measure.support_zero]

end TauCeti.Probability
