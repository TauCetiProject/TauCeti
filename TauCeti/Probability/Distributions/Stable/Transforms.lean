/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
import TauCeti.Probability.Distributions.Dirac

/-!
# Boundary transforms of scalar stable laws

This file computes the exponential-integrability domains, moment-generating functions, and
cumulant-generating functions of scalar stable laws at the two light-tailed boundaries.

At zero scale every valid stable law is a Dirac measure at its location, so all exponential
moments exist and the cumulant-generating function is linear. At shape two every valid stable
law is Gaussian with variance twice the squared stable scale, so all exponential moments exist
and the cumulant-generating function is `m * t + s ^ 2 * t ^ 2`.

These formulas provide the boundary cases for the exponential-integrability theory of stable
laws. Positive-scale stable laws of shape below two require separate tail arguments.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-! ### Zero scale -/

/-- Every exponential moment of a valid zero-scale stable law exists. -/
theorem integrableExpSet_id_stableMeasure_zero_scale {α β : ℝ} (hα : α ∈ Ioc 0 2)
    (hβ : |β| ≤ 1) (m : ℝ) :
    integrableExpSet id (stableMeasure α β 0 m) = univ := by
  rw [stableMeasure_zero_scale hα hβ]
  exact integrableExpSet_dirac id m

/-- The moment-generating function of a valid zero-scale stable law is that of its location. -/
theorem mgf_id_stableMeasure_zero_scale {α β : ℝ} (hα : α ∈ Ioc 0 2)
    (hβ : |β| ≤ 1) (m t : ℝ) :
    mgf id (stableMeasure α β 0 m) t = Real.exp (m * t) := by
  rw [stableMeasure_zero_scale hα hβ, mgf_dirac']
  simp [mul_comm]

/-- The cumulant-generating function of a valid zero-scale stable law is linear. -/
theorem cgf_id_stableMeasure_zero_scale {α β : ℝ} (hα : α ∈ Ioc 0 2)
    (hβ : |β| ≤ 1) (m t : ℝ) :
    cgf id (stableMeasure α β 0 m) t = m * t := by
  rw [stableMeasure_zero_scale hα hβ, cgf_dirac']
  simp [mul_comm]

/-! ### Gaussian shape -/

/-- Every exponential moment of a valid shape-two stable law exists. -/
theorem integrableExpSet_id_stableMeasure_two {β : ℝ} (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m : ℝ) : integrableExpSet id (stableMeasure 2 β s m) = univ := by
  rw [stableMeasure_two hβ]
  exact integrableExpSet_id_gaussianReal

/-- The moment-generating function of a shape-two stable law is Gaussian with variance
`2 * s ^ 2`. -/
theorem mgf_id_stableMeasure_two {β : ℝ} (hβ : |β| ≤ 1) (s : ℝ≥0) (m t : ℝ) :
    mgf id (stableMeasure 2 β s m) t = Real.exp (m * t + (s : ℝ) ^ 2 * t ^ 2) := by
  rw [stableMeasure_two hβ, congrFun mgf_id_gaussianReal t]
  push_cast
  ring_nf

/-- The cumulant-generating function of a shape-two stable law is the Gaussian quadratic
`m * t + s ^ 2 * t ^ 2`. -/
theorem cgf_id_stableMeasure_two {β : ℝ} (hβ : |β| ≤ 1) (s : ℝ≥0) (m t : ℝ) :
    cgf id (stableMeasure 2 β s m) t = m * t + (s : ℝ) ^ 2 * t ^ 2 := by
  rw [cgf, mgf_id_stableMeasure_two hβ, Real.log_exp]

end TauCeti.Probability
