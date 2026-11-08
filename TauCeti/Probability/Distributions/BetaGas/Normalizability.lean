/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaGas.Basic
import TauCeti.Algebra.Order.BigOperators.Sum.Prod
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

/-- Bound a product of powered pairwise distances by a product of coordinate magnitudes. -/
theorem vandermonde_le_prod (n : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (x : Fin n → ℝ) (pairs : Finset (Fin n × Fin n)) :
    (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤
      (∏ i : Fin n, (1 + |x i|)) ^ (2 * (β * (pairs.card : ℝ))) := by
  classical
  set p : ℝ := 2 * (β * (pairs.card : ℝ)) with hp_def
  let q : ℝ := ∏ i : Fin n, (1 + |x i|)
  have hqsum : 1 + ∑ i : Fin n, |x i| ≤ q := by
    simpa [q] using Finset.one_add_sum_le_prod_one_add (Finset.univ : Finset (Fin n))
      (fun i => |x i|) (fun _ _ => abs_nonneg _)
  have hqone : 1 ≤ q := by
    have hsum : 0 ≤ ∑ i : Fin n, |x i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hqnonneg : 0 ≤ q := by linarith [hqone]
  have hqpow : q ^ 2 ≥ 1 + 2 * ∑ i : Fin n, |x i| := by
    nlinarith [hqsum, hqone]
  have hpair : ∀ z ∈ pairs, |x z.1 - x z.2| ≤ q ^ 2 := by
    intro z hz
    have hi : |x z.1| ≤ ∑ i : Fin n, |x i| :=
      Finset.single_le_sum (f := fun i : Fin n => |x i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have hj : |x z.2| ≤ ∑ i : Fin n, |x i| :=
      Finset.single_le_sum (f := fun i : Fin n => |x i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have hdist := abs_sub_le (x z.1) 0 (x z.2)
    simp only [sub_zero, zero_sub, abs_neg] at hdist
    have hnonneg : 0 ≤ ∑ i : Fin n, |x i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith
  have hvander : (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤ q ^ p := by
    calc
      _ ≤ ∏ z ∈ pairs, (q ^ 2) ^ β := by
        apply Finset.prod_le_prod₀
          (fun z hz => by positivity)
          (fun z hz => Real.rpow_le_rpow (abs_nonneg _) (hpair z hz) hβ)
      _ = ((q ^ 2) ^ β) ^ (pairs.card : ℕ) := by
        simp [Finset.prod_const]
      _ = q ^ (2 * (β * (pairs.card : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ q ^ 2),
          ← Real.rpow_natCast q 2, ← Real.rpow_mul hqnonneg]
        norm_num
      _ = q ^ p := by
        rw [hp_def]
  exact hvander

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
    vandermonde_le_prod n hβ.le x pairs
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
  have hdens : betaGasDensity n β (fun t => t ^ 2 / 2) =
      fun x => betaGasWeight n β (fun t => t ^ 2 / 2) x /
        betaGasPartitionFunction n β (fun t => t ^ 2 / 2) := by
    funext x
    exact betaGasDensity_def n β _ x
  rw [hdens]
  exact ((measurable_betaGasWeight n β (V := fun t => t ^ 2 / 2)
    (by fun_prop)).div_const _).aemeasurable

end TauCeti.Probability
