/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Pi

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
  simp only [mgf, Finset.mul_sum, ← mul_assoc, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (k : ℕ) => Real.exp (t * θ i * (k : ℝ)))]
  have hfactor (i : ι) :
      (∫ k : ℕ, Real.exp (t * θ i * (k : ℝ)) ∂poissonMeasure (r i)) =
        Real.exp ((r i : ℝ) * (Real.exp (t * θ i) - 1)) := by
    simpa only [pgf_exp, mgf, id_eq] using pgf_poissonMeasure (r i) (Real.exp (t * θ i))
  simp_rw [hfactor]

/-- Every real linear combination of independent Poisson counts has full exponential domain. -/
@[simp]
theorem integrableExpSet_sum_mul_natCast_pi_poissonMeasure (r : ι → ℝ≥0) (θ : ι → ℝ) :
    integrableExpSet (fun k : ι → ℕ => ∑ i, θ i * (k i : ℝ))
      (Measure.pi fun i => poissonMeasure (r i)) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rw [← mgf_pos_iff, mgf_sum_mul_natCast_pi_poissonMeasure]
  exact Real.exp_pos _

end TauCeti.Probability
