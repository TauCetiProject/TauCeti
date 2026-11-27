/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Complex moments through degree two

A finite second absolute moment gives all mixed moments of degree at most two. For
probability measures, the complex mean, complex second moment and second absolute moment
determine these mixed moments.
-/

public section

open MeasureTheory
open scoped ComplexConjugate

namespace TauCeti.Probability

/-- A finite second absolute moment makes every mixed monomial of total degree at most two
integrable under a finite measure on `ℂ`. -/
theorem integrable_pow_mul_conj_pow {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ) {p q : ℕ} (h : p + q ≤ 2) :
    Integrable (fun w : ℂ ↦ w ^ p * conj w ^ q) μ := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq, norm_mul, norm_pow, Complex.norm_conj, ← pow_add] using
    integrable_norm_pow_of_le (f := id) aestronglyMeasurable_id h hμ

/-- Probability laws on `ℂ` with the same mean, second moment and second absolute moment
have the same mixed moments of total degree at most two. -/
theorem integral_pow_mul_conj_pow_eq {μ ν : Measure ℂ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    {p q : ℕ} (h : p + q ≤ 2) :
    (∫ w : ℂ, w ^ p * conj w ^ q ∂μ) = ∫ w : ℂ, w ^ p * conj w ^ q ∂ν := by
  have hp : p ≤ 2 := by omega
  have hq : q ≤ 2 := by omega
  interval_cases p <;> interval_cases q <;> try omega
  · simp
  · have hc : (∫ w : ℂ, conj w ∂μ) = ∫ w : ℂ, conj w ∂ν :=
      (integral_conj (f := id)).trans ((congrArg conj hmean).trans (integral_conj (f := id)).symm)
    simpa only [pow_zero, one_mul, pow_one] using hc
  · simpa [← map_pow, integral_conj] using congrArg conj hsq
  · simpa using hmean
  · simpa [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal] using
      congrArg Complex.ofReal habs
  · simpa using hsq

end TauCeti.Probability
