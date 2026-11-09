/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The finite beta gas

For a potential `V : ℝ → ℝ`, the weight is
`exp (-(β n / 2) ∑ V(xᵢ)) ∏_{i<j} |xᵢ - xⱼ|^β`. The Gaussian beta gas is the specialization
`V x = x² / 2`, giving the convention `exp (-(β n / 4) ∑ xᵢ²) ∏_{i<j} |xᵢ - xⱼ|^β`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), (2.6.1)–(2.6.2). The potential term here is `β V / 2`.
-/

public section
noncomputable section

open MeasureTheory Real

namespace TauCeti.Probability

/-- Distinct particle indices represented in increasing order. -/
def betaGasPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- Membership in the ordered-pair index set. -/
@[simp] theorem mem_betaGasPairs (n : ℕ) (p : Fin n × Fin n) :
    p ∈ betaGasPairs n ↔ p.1 < p.2 := by
  simp [betaGasPairs]

/-- The unnormalized beta-gas weight for a potential `V`. -/
def betaGasWeight (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  exp (-(β * (n : ℝ) / 2) * ∑ i, V (x i)) *
    ∏ p ∈ betaGasPairs n, |x p.1 - x p.2| ^ β

/-- The defining formula for the beta-gas weight. -/
theorem betaGasWeight_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) :
    betaGasWeight n β V x =
      exp (-(β * (n : ℝ) / 2) * ∑ i, V (x i)) *
        ∏ p ∈ betaGasPairs n,
          |x p.1 - x p.2| ^ β := (rfl)

/-- The beta-gas weight is nonnegative. -/
theorem betaGasWeight_nonneg (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (x : Fin n → ℝ) : 0 ≤ betaGasWeight n β V x := by
  unfold betaGasWeight
  positivity

/-- The beta-gas weight is positive at configurations with distinct coordinates. -/
theorem betaGasWeight_pos (n : ℕ) (β : ℝ) (V : ℝ → ℝ) {x : Fin n → ℝ}
    (hx : Function.Injective x) : 0 < betaGasWeight n β V x := by
  rw [betaGasWeight_def]
  apply mul_pos (exp_pos _)
  apply Finset.prod_pos
  intro z hz
  have hne : z.1 ≠ z.2 := ne_of_lt ((mem_betaGasPairs n z).mp hz)
  exact Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr (fun h => hne (hx h)))) β

/-- A continuous potential gives a continuous weight when `β` is nonnegative. -/
theorem continuous_betaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) {V : ℝ → ℝ}
    (hV : Continuous V) : Continuous (betaGasWeight n β V) := by
  unfold betaGasWeight
  fun_prop

/-- A measurable potential gives a measurable weight for every inverse temperature. -/
theorem measurable_betaGasWeight (n : ℕ) (β : ℝ) {V : ℝ → ℝ}
    (hV : Measurable V) : Measurable (betaGasWeight n β V) := by
  have hrpow : Measurable (fun t : ℝ => |t| ^ β) := by
    fun_prop
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

/-- A measurable potential gives a measurable normalized density. -/
theorem measurable_betaGasDensity (n : ℕ) (β : ℝ) {V : ℝ → ℝ}
    (hV : Measurable V) : Measurable (betaGasDensity n β V) := by
  have hdens : betaGasDensity n β V =
      fun x => betaGasWeight n β V x / betaGasPartitionFunction n β V := by
    funext x
    exact betaGasDensity_def n β V x
  rw [hdens]
  exact (measurable_betaGasWeight n β hV).div_const _

/-- The beta-gas density is nonnegative. -/
theorem betaGasDensity_nonneg (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (x : Fin n → ℝ) : 0 ≤ betaGasDensity n β V x :=
  div_nonneg (betaGasWeight_nonneg n β V x) (betaGasPartitionFunction_nonneg n β V)

/-- The normalized density is integrable when the weight is integrable. -/
theorem integrable_betaGasDensity (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : Integrable (betaGasWeight n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :
    Integrable (betaGasDensity n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
  hint.div_const _

/-- A positive partition function normalizes the integral of the density. -/
theorem integral_betaGasDensity (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hpos : 0 < betaGasPartitionFunction n β V) :
    (∫ x, betaGasDensity n β V x
      ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)) = 1 := by
  simp only [betaGasDensity, integral_div, ← betaGasPartitionFunction_def]
  exact div_self hpos.ne'

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
  have hdens := integrable_betaGasDensity n β V hint
  rw [betaGasMeasure, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal hdens.restrict
    (ae_of_all _ (betaGasDensity_nonneg n β V))).symm

/-- Integrals against the beta-gas measure are weighted integrals against product volume. -/
theorem integral_betaGasMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hdens : AEMeasurable (betaGasDensity n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)))
    (f : (Fin n → ℝ) → E) :
    ∫ x, f x ∂betaGasMeasure n β V =
      ∫ x, betaGasDensity n β V x • f x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ) := by
  rw [betaGasMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hdens.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal, betaGasDensity_nonneg]

/-- Integrability and a positive partition function make the beta-gas measure a probability. -/
theorem isProbabilityMeasure_betaGasMeasure (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : Integrable (betaGasWeight n β V)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)))
    (hpos : 0 < betaGasPartitionFunction n β V) :
    IsProbabilityMeasure (betaGasMeasure n β V) := by
  have hdens := integrable_betaGasDensity n β V hint
  refine ⟨?_⟩
  rw [betaGasMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hdens
    (ae_of_all _ (betaGasDensity_nonneg n β V))]
  rw [integral_betaGasDensity n β V hpos]
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
        ∏ p ∈ betaGasPairs n,
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
    (hx : Function.Injective x) : 0 < gaussianBetaGasWeight n β x :=
  betaGasWeight_pos n β _ hx

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
    0 ≤ gaussianBetaGasPartitionFunction n β :=
  betaGasPartitionFunction_nonneg n β _

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
    (x : Fin n → ℝ) : 0 ≤ gaussianBetaGasDensity n β x :=
  betaGasDensity_nonneg n β _ x

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
