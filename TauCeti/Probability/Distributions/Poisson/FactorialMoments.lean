/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Poisson.Mixed.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Mixed factorial moments of independent Poisson counts

Finite-product integration turns the existing scalar Poisson factorial-moment identity into
mixed factorial moments for independent counts. These formulas are the component calculations
for Gamma mixtures and hence for negative-multinomial moments. Zero rates and empty products
are allowed.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Every mixed factorial moment of independent Poisson counts is integrable. -/
theorem integrable_prod_descFactorial_pi_poissonMeasure (lam : ι → ℝ≥0) (n : ι → ℕ) :
    Integrable (fun k : ι → ℕ => ∏ i, ((k i).descFactorial (n i) : ℝ))
      (Measure.pi fun i => poissonMeasure (lam i)) := by
  apply Integrable.fintype_prod (f := fun i (k : ℕ) => (k.descFactorial (n i) : ℝ))
  intro i
  simpa only [mixedPoissonMeasure_dirac] using
    (integrable_descFactorial_mixedPoissonMeasure_iff
      (ρ := Measure.dirac (lam i)) (n i)).2 (integrable_dirac (by simp))

/-- A mixed factorial moment of independent Poisson counts is the product of the corresponding
powers of their rates. -/
@[simp]
theorem integral_prod_descFactorial_pi_poissonMeasure (lam : ι → ℝ≥0) (n : ι → ℕ) :
    ∫ k : ι → ℕ, ∏ i, ((k i).descFactorial (n i) : ℝ)
      ∂Measure.pi (fun i => poissonMeasure (lam i)) = ∏ i, (lam i : ℝ) ^ n i := by
  rw [integral_fintype_prod_eq_prod (fun i (k : ℕ) => (k.descFactorial (n i) : ℝ))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [mixedPoissonMeasure_dirac, integral_dirac] using
    integral_descFactorial_mixedPoissonMeasure (Measure.dirac (lam i)) (n i)

end TauCeti.Probability
