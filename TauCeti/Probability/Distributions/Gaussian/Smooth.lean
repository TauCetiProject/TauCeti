/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smoothness of the Gaussian density and distribution function

The real Gaussian density is smooth, including at zero variance where its chosen value is
zero. For nonzero variance the native Gaussian cumulative distribution function is smooth
as well. These results allow smooth composition with the Gaussian CDF, for example in
classical option-pricing formulas. No smoothness is asserted for the CDF of a Dirac mass.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ContDiff NNReal

namespace TauCeti.Probability

/-- The Gaussian density is smooth in its sample variable, for every variance. -/
@[fun_prop]
theorem contDiff_gaussianPDFReal (m : ℝ) (v : ℝ≥0) {n : WithTop ℕ∞} :
    ContDiff ℝ n (gaussianPDFReal m v) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- A nondegenerate Gaussian CDF is smooth to every finite or infinite differentiability order. -/
@[fun_prop]
theorem contDiff_cdf_gaussianReal (m : ℝ) {v : ℝ≥0} {n : ℕ∞} (hv : v ≠ 0) :
    ContDiff ℝ n (cdf (gaussianReal m v)) := by
  have h : ContDiff ℝ ∞ (cdf (gaussianReal m v)) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hasDerivAt_cdf_gaussianReal m hv x).differentiableAt, ?_⟩
    have hderiv : deriv (cdf (gaussianReal m v)) = gaussianPDFReal m v :=
      funext fun x => (hasDerivAt_cdf_gaussianReal m hv x).deriv
    rw [hderiv]
    exact contDiff_gaussianPDFReal m v
  exact h.of_le (by exact_mod_cast le_top)

end TauCeti.Probability
