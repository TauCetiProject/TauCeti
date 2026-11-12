/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Characteristic functions of independent Poisson counts

The Euclidean cast of a finite vector of independent Poisson counts has characteristic function
`exp (∑ i, r i * (exp (I * t i) - 1))`. Zero rates and empty coordinate types are included.
This supplies the component transform for Gamma mixtures of Poisson count vectors.

The calculation uses Mathlib's `charFun_map_cast_poissonMeasure` and finite-product integration.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The joint characteristic function of the Euclidean cast of independent Poisson counts. -/
@[simp]
theorem charFun_map_multinomialToEuclidean_pi_poissonMeasure (r : ι → ℝ≥0)
    (t : EuclideanSpace ℝ ι) :
    charFun ((Measure.pi fun i => poissonMeasure (r i)).map multinomialToEuclidean) t =
      Complex.exp (∑ i, (r i : ℂ) * (Complex.exp (Complex.I * (t i : ℂ)) - 1)) := by
  classical
  rw [charFun_apply, integral_map measurable_multinomialToEuclidean.aemeasurable (by fun_prop)]
  simp only [real_inner_comm, inner_multinomialToEuclidean, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_natCast, Finset.sum_mul, Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (fun i (k : ℕ) => Complex.exp ((t i : ℂ) * (k : ℂ) * Complex.I))]
  apply Finset.prod_congr rfl
  intro i _
  have h := charFun_map_cast_poissonMeasure (r i) (t i)
  rw [charFun_apply_real, integral_map (.of_discrete) (by fun_prop)] at h
  simpa only [Complex.ofReal_mul, Complex.ofReal_natCast, mul_comm Complex.I] using h

end TauCeti.Probability
