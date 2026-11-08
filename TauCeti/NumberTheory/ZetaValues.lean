/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues

/-!
# Bernoulli polynomials and Bernoulli functions

Mathlib's `bernoulliFun` is the real-variable Bernoulli polynomial. This file records how it
relates to the Bernoulli polynomial over `ℚ` mapped into `ℂ`.

## Main results

* `algebraMap_eval_bernoulli_eq_bernoulliFun`: the Bernoulli polynomial at a rational point, in `ℂ`,
  is `bernoulliFun` at the real point.
-/

public section

/-- The Bernoulli polynomial at a rational point, mapped into `ℂ`, is the Bernoulli function at the
corresponding real point. -/
theorem algebraMap_eval_bernoulli_eq_bernoulliFun {k : ℕ} (x : ℚ) :
    algebraMap ℚ ℂ ((Polynomial.bernoulli k).eval x) = bernoulliFun k (x : ℝ) := by
  simp only [bernoulliFun, Polynomial.eval_map, ← map_ratCast (algebraMap ℚ ℝ),
    Polynomial.eval₂_at_apply]
  norm_cast
