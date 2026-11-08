/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The finite beta gas

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

/-- The unnormalized beta-gas weight for a potential `V`. -/
def betaGasWeight (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  exp (-(β * (n : ℝ) / 2) * ∑ i, V (x i)) *
    ∏ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2), |x p.1 - x p.2| ^ β

/-- The defining formula for the beta-gas weight. -/
theorem betaGasWeight_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) :
    betaGasWeight n β V x =
      exp (-(β * (n : ℝ) / 2) * ∑ i, V (x i)) *
        ∏ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2),
          |x p.1 - x p.2| ^ β := (rfl)

/-- The beta-gas weight is nonnegative. -/
theorem betaGasWeight_nonneg (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (x : Fin n → ℝ) : 0 ≤ betaGasWeight n β V x := by
  unfold betaGasWeight
  positivity

/-- A continuous potential gives a continuous weight when `β` is nonnegative. -/
theorem continuous_betaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) {V : ℝ → ℝ}
    (hV : Continuous V) : Continuous (betaGasWeight n β V) := by
  unfold betaGasWeight
  fun_prop

/-- The beta-gas partition function; the Bochner integral is zero when not integrable. -/
def betaGasPartitionFunction (n : ℕ) (β : ℝ) (V : ℝ → ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, betaGasWeight n β V x
    ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)

/-- The defining integral for the beta-gas partition function. -/
theorem betaGasPartitionFunction_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    betaGasPartitionFunction n β V =
      ∫ x : Fin n → ℝ, betaGasWeight n β V x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ) := (rfl)

/-- The beta-gas partition function is nonnegative. -/
theorem betaGasPartitionFunction_nonneg (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    0 ≤ betaGasPartitionFunction n β V :=
  integral_nonneg (betaGasWeight_nonneg n β V)

/-- The beta-gas density normalized by its partition function. -/
def betaGasDensity (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  betaGasWeight n β V x / betaGasPartitionFunction n β V

/-- The defining formula for the beta-gas density. -/
theorem betaGasDensity_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) :
    betaGasDensity n β V x = betaGasWeight n β V x / betaGasPartitionFunction n β V := (rfl)

/-- The beta-gas density is nonnegative. -/
theorem betaGasDensity_nonneg (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (x : Fin n → ℝ) : 0 ≤ betaGasDensity n β V x :=
  div_nonneg (betaGasWeight_nonneg n β V x) (betaGasPartitionFunction_nonneg n β V)

/-- The beta-gas measure with the normalized density. -/
def betaGasMeasure (n : ℕ) (β : ℝ) (V : ℝ → ℝ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity fun x =>
    ENNReal.ofReal (betaGasDensity n β V x)

/-- The beta-gas measure as a with-density measure. -/
theorem betaGasMeasure_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    betaGasMeasure n β V =
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity
        (fun x => ENNReal.ofReal (betaGasDensity n β V x)) := (rfl)

/-- The mass of a measurable set is the integral of the beta-gas density over it. -/
theorem betaGasMeasure_apply (n : ℕ) (β : ℝ) (V : ℝ → ℝ) {s : Set (Fin n → ℝ)}
    (hs : MeasurableSet s)
    (hint : Integrable (betaGasWeight n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :
    betaGasMeasure n β V s =
      ENNReal.ofReal (∫ x in s, betaGasDensity n β V x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  have hdens : Integrable (betaGasDensity n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
    hint.div_const _
  rw [betaGasMeasure, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal hdens.restrict
    (ae_of_all _ (betaGasDensity_nonneg n β V))).symm

/-- Integrals against the beta-gas measure are weighted integrals against product volume. -/
theorem integral_betaGasMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) {V : ℝ → ℝ} (hV : Continuous V)
    (f : (Fin n → ℝ) → E) :
    ∫ x, f x ∂betaGasMeasure n β V =
      ∫ x, betaGasDensity n β V x • f x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ) := by
  have hdens : Continuous (betaGasDensity n β V) :=
    (continuous_betaGasWeight n hβ hV).div_const _
  rw [betaGasMeasure, integral_withDensity_eq_integral_toReal_smul
    hdens.measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal, betaGasDensity_nonneg]

/-- Integrability and a positive partition function make the beta-gas measure a probability. -/
theorem isProbabilityMeasure_betaGasMeasure (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : Integrable (betaGasWeight n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)))
    (hpos : 0 < betaGasPartitionFunction n β V) :
    IsProbabilityMeasure (betaGasMeasure n β V) := by
  have hdens : Integrable (betaGasDensity n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
    hint.div_const _
  refine ⟨?_⟩
  rw [betaGasMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hdens
    (ae_of_all _ (betaGasDensity_nonneg n β V))]
  have hi : (∫ x, betaGasDensity n β V x
      ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)) = 1 := by
    simp only [betaGasDensity, integral_div]
    change betaGasPartitionFunction n β V / betaGasPartitionFunction n β V = 1
    exact div_self hpos.ne'
  rw [hi]
  norm_num

/-- The unnormalized Gaussian beta-gas weight with quadratic potential `V x = x² / 2`. -/
def gaussianBetaGasWeight (n : ℕ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  betaGasWeight n β (fun t => t ^ 2 / 2) x

/-- The Gaussian weight is the beta-gas weight for the quadratic potential. -/
theorem gaussianBetaGasWeight_eq_betaGasWeight (n : ℕ) (β : ℝ) :
    gaussianBetaGasWeight n β = betaGasWeight n β (fun t => t ^ 2 / 2) := (rfl)

/-- The defining formula for the Gaussian beta-gas weight. -/
theorem gaussianBetaGasWeight_def (n : ℕ) (β : ℝ) (x : Fin n → ℝ) :
    gaussianBetaGasWeight n β x =
      exp (-(β * (n : ℝ) / 4) * ∑ i, x i ^ 2) *
        ∏ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2),
          |x p.1 - x p.2| ^ β := by
  unfold gaussianBetaGasWeight betaGasWeight
  rw [← Finset.sum_div]
  congr 2
  ring

/-- The weight is continuous for nonnegative inverse temperature. -/
theorem continuous_gaussianBetaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (gaussianBetaGasWeight n β) := by
  exact continuous_betaGasWeight n hβ (V := fun t => t ^ 2 / 2) (by fun_prop)

/-- The Gaussian beta-gas weight is nonnegative. -/
theorem gaussianBetaGasWeight_nonneg (n : ℕ) (β : ℝ)
    (x : Fin n → ℝ) : 0 ≤ gaussianBetaGasWeight n β x := by
  exact betaGasWeight_nonneg n β _ x

/-- The Gaussian beta-gas weight is positive at configurations with distinct coordinates. -/
theorem gaussianBetaGasWeight_pos (n : ℕ) (β : ℝ) {x : Fin n → ℝ}
    (hx : Function.Injective x) : 0 < gaussianBetaGasWeight n β x := by
  rw [gaussianBetaGasWeight_def]
  apply mul_pos (exp_pos _)
  apply Finset.prod_pos
  intro z hz
  have hne : z.1 ≠ z.2 := ne_of_lt (Finset.mem_filter.mp hz).2
  exact Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr (fun h => hne (hx h)))) β

/-- The partition function, finite and strictly positive for `0 < β`. Outside the integrable
case, the Bochner integral is defined to be zero. -/
def gaussianBetaGasPartitionFunction (n : ℕ) (β : ℝ) : ℝ :=
  betaGasPartitionFunction n β (fun t => t ^ 2 / 2)

/-- The Gaussian partition function is the quadratic-potential specialization. -/
theorem gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction (n : ℕ) (β : ℝ) :
    gaussianBetaGasPartitionFunction n β =
      betaGasPartitionFunction n β (fun t => t ^ 2 / 2) := (rfl)

/-- The defining integral for the Gaussian beta-gas partition function. -/
theorem gaussianBetaGasPartitionFunction_def (n : ℕ) (β : ℝ) :
    gaussianBetaGasPartitionFunction n β =
      ∫ x : Fin n → ℝ, gaussianBetaGasWeight n β x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ) := (rfl)

/-- The partition function is nonnegative, including when the weight is not integrable. -/
theorem gaussianBetaGasPartitionFunction_nonneg (n : ℕ) (β : ℝ) :
    0 ≤ gaussianBetaGasPartitionFunction n β := by
  rw [gaussianBetaGasPartitionFunction_def]
  exact integral_nonneg (gaussianBetaGasWeight_nonneg n β)

/-- The Gaussian beta-gas density; it integrates to one for `0 < β`. -/
def gaussianBetaGasDensity (n : ℕ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  betaGasDensity n β (fun t => t ^ 2 / 2) x

/-- The Gaussian density is the quadratic-potential specialization. -/
theorem gaussianBetaGasDensity_eq_betaGasDensity (n : ℕ) (β : ℝ) :
    gaussianBetaGasDensity n β = betaGasDensity n β (fun t => t ^ 2 / 2) := (rfl)

/-- The defining formula for the Gaussian beta-gas density. -/
theorem gaussianBetaGasDensity_def (n : ℕ) (β : ℝ) (x : Fin n → ℝ) :
    gaussianBetaGasDensity n β x =
      gaussianBetaGasWeight n β x / gaussianBetaGasPartitionFunction n β := (rfl)

/-- The Gaussian beta-gas density is nonnegative for every inverse temperature. -/
theorem gaussianBetaGasDensity_nonneg (n : ℕ) (β : ℝ)
    (x : Fin n → ℝ) : 0 ≤ gaussianBetaGasDensity n β x := by
  rw [gaussianBetaGasDensity_def]
  exact div_nonneg (gaussianBetaGasWeight_nonneg n β x)
    (gaussianBetaGasPartitionFunction_nonneg n β)

/-- The Gaussian beta-gas measure; it is a probability measure for `0 < β`. -/
def gaussianBetaGasMeasure (n : ℕ) (β : ℝ) : Measure (Fin n → ℝ) :=
  betaGasMeasure n β (fun t => t ^ 2 / 2)

/-- The Gaussian measure is the quadratic-potential specialization. -/
theorem gaussianBetaGasMeasure_eq_betaGasMeasure (n : ℕ) (β : ℝ) :
    gaussianBetaGasMeasure n β = betaGasMeasure n β (fun t => t ^ 2 / 2) := (rfl)

/-- The Gaussian beta-gas measure as a with-density measure. -/
theorem gaussianBetaGasMeasure_def (n : ℕ) (β : ℝ) :
    gaussianBetaGasMeasure n β =
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity
        (fun x => ENNReal.ofReal (gaussianBetaGasDensity n β x)) := (rfl)

end TauCeti.Probability
