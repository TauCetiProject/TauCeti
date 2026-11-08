/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaGas.Basic
import TauCeti.Algebra.Order.BigOperators.Sum.ProdReal
import TauCeti.MeasureTheory.Integral.GaussianGrowth

import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Normalizability of the Gaussian beta gas

For every finite number of particles and every positive inverse temperature, the Gaussian beta-gas
weight has a finite, strictly positive integral. Dividing by that integral gives a probability
measure on the particle configurations.
-/

public section
noncomputable section

open MeasureTheory Real

namespace TauCeti.Probability

/-- The unordered pairs of distinct indices in `Fin n`, represented in increasing order. -/
private def gaussianBetaGasPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

private lemma gaussianBetaGasWeight_le_prod (n : ℕ) {β : ℝ} (hβ : 0 < β)
    (x : Fin n → ℝ) :
    gaussianBetaGasWeight n β x ≤
      ∏ i : Fin n, ((1 + |x i|) ^ (2 * (β * ((gaussianBetaGasPairs n).card : ℝ))) *
        exp (-(β * (n : ℝ) / 4) * x i ^ 2)) := by
  classical
  let pairs := gaussianBetaGasPairs n
  let a : ℝ := β * (n : ℝ) / 4
  let p : ℝ := 2 * (β * (pairs.card : ℝ))
  let q : ℝ := ∏ i : Fin n, (1 + |x i|)
  have hvander : (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤ q ^ p :=
    Finset.prod_abs_sub_rpow_le_prod_one_add_abs_rpow hβ.le x pairs
  have hexp : exp (-(β * (n : ℝ) / 4) * ∑ i : Fin n, x i ^ 2) =
      ∏ i : Fin n, exp (-a * x i ^ 2) := by
    have hdistrib : -(β * (n : ℝ) / 4) * ∑ i : Fin n, x i ^ 2 =
        ∑ i : Fin n, (-a * x i ^ 2) := by simp [a, Finset.mul_sum]
    rw [hdistrib]
    exact Real.exp_sum _ _
  have hqpowprod : q ^ p = ∏ i : Fin n, (1 + |x i|) ^ p := by
    exact (Real.finsetProd_rpow (Finset.univ : Finset (Fin n))
      (fun i => 1 + |x i|) (fun _ _ => by positivity) p).symm
  have hpoint : gaussianBetaGasWeight n β x ≤
      ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * x i ^ 2)) := by
    rw [gaussianBetaGasWeight_def]
    rw [show (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) = pairs from rfl]
    rw [hexp]
    calc
      _ ≤ (∏ i : Fin n, exp (-a * x i ^ 2)) * q ^ p := by
        exact mul_le_mul_of_nonneg_left hvander (by positivity)
      _ = ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * x i ^ 2)) := by
        rw [hqpowprod, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        ring
  exact hpoint

/-- The Gaussian beta-gas weight is integrable for every positive inverse temperature. -/
theorem integrable_gaussianBetaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (gaussianBetaGasWeight n β)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  · let pairs := gaussianBetaGasPairs n
    let a : ℝ := β * (n : ℝ) / 4
    let p : ℝ := 2 * (β * (pairs.card : ℝ))
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hmajor : Integrable
        (fun x : Fin n → ℝ =>
          ∏ i, ((1 + |x i|) ^ p * exp (-a * x i ^ 2)))
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
      Integrable.fintype_prod fun _ =>
        integrable_one_add_abs_rpow_mul_exp_neg_sq ha
    apply Integrable.mono' hmajor
      ((continuous_gaussianBetaGasWeight n hβ.le).aestronglyMeasurable)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (gaussianBetaGasWeight_nonneg n β x),
      abs_of_nonneg (by positivity :
        0 ≤ ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * x i ^ 2)))] using
      gaussianBetaGasWeight_le_prod n hβ x

/-- The Gaussian beta-gas partition function is strictly positive. -/
theorem gaussianBetaGasPartitionFunction_pos (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    0 < gaussianBetaGasPartitionFunction n β := by
  let x₀ : Fin n → ℝ := fun i => (i : ℝ)
  have hx₀ : 0 < gaussianBetaGasWeight n β x₀ := by
    apply gaussianBetaGasWeight_pos
    intro i j hij
    dsimp [x₀] at hij
    exact Fin.ext (by exact_mod_cast hij)
  rw [gaussianBetaGasPartitionFunction_def]
  exact integral_pos_of_integrable_nonneg_ne_zero
    (continuous_gaussianBetaGasWeight n hβ.le)
    (integrable_gaussianBetaGasWeight n hβ)
    (gaussianBetaGasWeight_nonneg n β) hx₀.ne'

/-- The Gaussian beta-gas density is integrable for positive inverse temperature. -/
theorem integrable_gaussianBetaGasDensity (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (gaussianBetaGasDensity n β)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  rw [gaussianBetaGasDensity_eq_betaGasDensity]
  apply integrable_betaGasDensity
  rw [← gaussianBetaGasWeight_eq_betaGasWeight]
  exact integrable_gaussianBetaGasWeight n hβ

/-- The Gaussian beta-gas density integrates to one for positive inverse temperature. -/
@[simp]
theorem integral_gaussianBetaGasDensity (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∫ x, gaussianBetaGasDensity n β x
      ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)) = 1 := by
  rw [gaussianBetaGasDensity_eq_betaGasDensity]
  apply integral_betaGasDensity
  rw [← gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction]
  exact gaussianBetaGasPartitionFunction_pos n hβ

/-- The normalized Gaussian beta-gas measure has total mass one. -/
theorem isProbabilityMeasure_gaussianBetaGasMeasure (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (gaussianBetaGasMeasure n β) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure]
  apply isProbabilityMeasure_betaGasMeasure
  · rw [← gaussianBetaGasWeight_eq_betaGasWeight]
    exact integrable_gaussianBetaGasWeight n hβ
  · rw [← gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction]
    exact gaussianBetaGasPartitionFunction_pos n hβ

/-- Evaluate the Gaussian beta-gas measure on a measurable set. -/
theorem gaussianBetaGasMeasure_apply (n : ℕ) {β : ℝ} (hβ : 0 < β)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    gaussianBetaGasMeasure n β s =
      ENNReal.ofReal (∫ x in s, gaussianBetaGasDensity n β x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure, gaussianBetaGasDensity_eq_betaGasDensity]
  apply betaGasMeasure_apply n β _ hs
  rw [← gaussianBetaGasWeight_eq_betaGasWeight]
  exact integrable_gaussianBetaGasWeight n hβ

/-- Integrate a function against the Gaussian beta-gas measure. -/
theorem integral_gaussianBetaGasMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (β : ℝ) (f : (Fin n → ℝ) → E) :
    ∫ x, f x ∂gaussianBetaGasMeasure n β =
      ∫ x, gaussianBetaGasDensity n β x • f x
        ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure, gaussianBetaGasDensity_eq_betaGasDensity]
  apply integral_betaGasMeasure
  exact (measurable_betaGasDensity n β (by fun_prop)).aemeasurable

end TauCeti.Probability
