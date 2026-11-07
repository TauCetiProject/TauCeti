/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The finite Gaussian beta gas

The weight uses the convention `exp (-(β n / 4) ∑ xᵢ²) ∏_{i<j} |xᵢ - xⱼ|^β`, corresponding
to the potential `V x = x² / 2` in `exp (-(β n / 2) ∑ V(xᵢ))`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), (2.6.1)–(2.6.2). Their potential is `β V / 2` in this convention.
-/

public section
noncomputable section

open MeasureTheory Real

namespace TauCeti.Probability

/-- The unnormalized Gaussian beta-gas weight with quadratic potential `V x = x² / 2`. -/
def gaussianBetaGasWeight (n : ℕ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  exp (-(β * (n : ℝ) / 4) * ∑ i, x i ^ 2) *
    ∏ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2), |x p.1 - x p.2| ^ β

/-- The defining formula for the Gaussian beta-gas weight. -/
theorem gaussianBetaGasWeight_def (n : ℕ) (β : ℝ) (x : Fin n → ℝ) :
    gaussianBetaGasWeight n β x =
      exp (-(β * (n : ℝ) / 4) * ∑ i, x i ^ 2) *
        ∏ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2),
          |x p.1 - x p.2| ^ β := (rfl)

/-- The weight is continuous for nonnegative inverse temperature. -/
theorem continuous_gaussianBetaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (gaussianBetaGasWeight n β) := by
  unfold gaussianBetaGasWeight
  fun_prop

/-- The Gaussian beta-gas weight is nonnegative. -/
theorem gaussianBetaGasWeight_nonneg (n : ℕ) (β : ℝ)
    (x : Fin n → ℝ) : 0 ≤ gaussianBetaGasWeight n β x := by
  unfold gaussianBetaGasWeight
  positivity

/-- The partition function, finite and strictly positive for `0 < β`. Outside the integrable
case, the Bochner integral is defined to be zero. -/
def gaussianBetaGasPartitionFunction (n : ℕ) (β : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, gaussianBetaGasWeight n β x
    ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)

/-- The defining integral for the Gaussian beta-gas partition function. -/
theorem gaussianBetaGasPartitionFunction_def (n : ℕ) (β : ℝ) :
    gaussianBetaGasPartitionFunction n β =
      ∫ x : Fin n → ℝ, gaussianBetaGasWeight n β x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ) := (rfl)

/-- The Gaussian beta-gas density; it integrates to one for `0 < β`. -/
def gaussianBetaGasDensity (n : ℕ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  gaussianBetaGasWeight n β x / gaussianBetaGasPartitionFunction n β

/-- The defining formula for the Gaussian beta-gas density. -/
theorem gaussianBetaGasDensity_def (n : ℕ) (β : ℝ) (x : Fin n → ℝ) :
    gaussianBetaGasDensity n β x =
      gaussianBetaGasWeight n β x / gaussianBetaGasPartitionFunction n β := (rfl)

/-- The Gaussian beta-gas measure; it is a probability measure for `0 < β`. -/
def gaussianBetaGasMeasure (n : ℕ) (β : ℝ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity fun x =>
    ENNReal.ofReal (gaussianBetaGasDensity n β x)

/-- The Gaussian beta-gas measure as a with-density measure. -/
theorem gaussianBetaGasMeasure_def (n : ℕ) (β : ℝ) :
    gaussianBetaGasMeasure n β =
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity
        (fun x => ENNReal.ofReal (gaussianBetaGasDensity n β x)) := (rfl)

end TauCeti.Probability
