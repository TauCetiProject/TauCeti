/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Laplace.Basic
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Topological support of the Laplace distribution

This file identifies the exact topological support of a Laplace law. At positive scale its density
is strictly positive on the whole real line, so the law and Lebesgue measure have the same null
sets and the support is all of `ℝ`. At nonpositive scale the totalized law is zero and has empty
support.

## Main result

* `TauCeti.Probability.support_laplaceMeasure` — the support is `Set.univ` exactly at positive
  scale, and is empty otherwise.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 24.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

/-- The topological support of a Laplace law is the whole real line at positive scale and is empty
for the totalized zero law at nonpositive scale. -/
@[simp]
theorem support_laplaceMeasure (μ b : ℝ) :
    (laplaceMeasure μ b).support = if 0 < b then univ else ∅ := by
  split_ifs with hb
  · have hac : volume ≪ laplaceMeasure μ b := by
      rw [laplaceMeasure_eq_withDensity]
      apply withDensity_absolutelyContinuous' (measurable_laplacePDF μ b).aemeasurable
      exact Filter.Eventually.of_forall fun x ↦ by
        rw [laplacePDF_eq_ofReal]
        exact (ENNReal.ofReal_pos.mpr (laplacePDFReal_pos hb μ x)).ne'
    apply eq_univ_iff_forall.mpr
    intro x
    apply hac.support_mono
    rw [Measure.support_eq_univ]
    exact mem_univ x
  · rw [laplaceMeasure_of_nonpos (not_lt.mp hb), Measure.support_zero]

end Probability

end TauCeti
