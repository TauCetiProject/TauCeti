/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Poisson.Basic
import TauCeti.Probability.Moments.Pi

/-!
# Directional transforms of independent Poisson counts

A real linear combination of a finite independent Poisson count vector has exponential moments
at every real parameter. Its moment generating function factors into the scalar Poisson
transforms. This formula also evaluates the component exponential integrals in multivariate
Gamma–Poisson mixtures.

The scalar transform is `pgf_poissonMeasure`; finite-product integration supplies the joint
formula. Empty coordinate types and zero rates are included.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The directional moment generating function of independent Poisson counts. -/
@[simp]
theorem mgf_sum_mul_natCast_pi_poissonMeasure (r : ι → ℝ≥0) (θ : ι → ℝ) (t : ℝ) :
    mgf (fun k : ι → ℕ => ∑ i, θ i * (k i : ℝ))
      (Measure.pi fun i => poissonMeasure (r i)) t =
        Real.exp (∑ i, (r i : ℝ) * (Real.exp (t * θ i) - 1)) := by
  classical
  rw [TauCeti.mgf_sum_pi (fun i (k : ℕ) => θ i * (k : ℝ)) t, Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => by
    simpa only [pgf_exp, mgf, id_eq, mul_assoc] using
      pgf_poissonMeasure (r i) (Real.exp (t * θ i))

/-- Every directional exponential of independent Poisson counts is integrable. -/
theorem integrable_exp_sum_mul_natCast_pi_poissonMeasure (r : ι → ℝ≥0) (θ : ι → ℝ)
    (t : ℝ) :
    Integrable (fun k : ι → ℕ => Real.exp (t * ∑ i, θ i * (k i : ℝ)))
      (Measure.pi fun i => poissonMeasure (r i)) := by
  rw [← mgf_pos_iff, mgf_sum_mul_natCast_pi_poissonMeasure]
  exact Real.exp_pos _

/-- Every real linear combination of independent Poisson counts has full exponential domain. -/
@[simp]
theorem integrableExpSet_sum_mul_natCast_pi_poissonMeasure (r : ι → ℝ≥0) (θ : ι → ℝ) :
    integrableExpSet (fun k : ι → ℕ => ∑ i, θ i * (k i : ℝ))
      (Measure.pi fun i => poissonMeasure (r i)) = Set.univ := by
  ext t
  simpa [integrableExpSet] using integrable_exp_sum_mul_natCast_pi_poissonMeasure r θ t

/-- The directional cumulant generating function of independent Poisson counts. -/
@[simp]
theorem cgf_sum_mul_natCast_pi_poissonMeasure (r : ι → ℝ≥0) (θ : ι → ℝ) (t : ℝ) :
    cgf (fun k : ι → ℕ => ∑ i, θ i * (k i : ℝ))
      (Measure.pi fun i => poissonMeasure (r i)) t =
        ∑ i, (r i : ℝ) * (Real.exp (t * θ i) - 1) := by
  rw [cgf, mgf_sum_mul_natCast_pi_poissonMeasure, Real.log_exp]

end TauCeti.Probability
