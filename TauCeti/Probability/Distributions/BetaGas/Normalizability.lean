/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaGas.Basic
import TauCeti.Algebra.Order.BigOperators.SumProd
import TauCeti.MeasureTheory.Integral.GaussianGrowth

import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Normalizability of the Gaussian beta gas

For every finite number of particles and every positive inverse temperature, the Gaussian beta-gas
density has a finite, strictly positive integral. Dividing by that integral gives a probability
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
  set p : ℝ := 2 * (β * (pairs.card : ℝ)) with hp_def
  let q : ℝ := ∏ i : Fin n, (1 + |x i|)
  have hqsum : 1 + ∑ i : Fin n, |x i| ≤ q := by
    simpa [q] using one_add_sum_le_prod (Finset.univ : Finset (Fin n))
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
  have hvander : (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤
      q ^ p := by
    calc
      _ ≤ ∏ z ∈ pairs, (q ^ 2) ^ β := by
        apply Finset.prod_le_prod₀
          (fun z hz => by positivity)
          (fun z hz => Real.rpow_le_rpow (abs_nonneg _) (hpair z hz) hβ.le)
      _ = ((q ^ 2) ^ β) ^ (pairs.card : ℕ) := by
        simp [Finset.prod_const]
      _ = ((q ^ 2) ^ β) ^ (pairs.card : ℝ) := by
        rw [← Real.rpow_natCast]
      _ = (q ^ 2) ^ (β * (pairs.card : ℝ)) := by
        rw [← Real.rpow_mul (by positivity : 0 ≤ q ^ 2)]
      _ = q ^ (2 * (β * (pairs.card : ℝ))) := by
        have hq2 : q ^ (2 : ℕ) = q ^ ((2 : ℕ) : ℝ) := by
          symm
          exact Real.rpow_natCast q 2
        rw [hq2, ← Real.rpow_mul hqnonneg (↑(2 : ℕ) : ℝ)
          (β * (pairs.card : ℝ))]
        congr 1
      _ = q ^ p := by
        rw [hp_def]
  have hexp : exp (-(β * (n : ℝ) / 4) * ∑ i : Fin n, x i ^ 2) =
      ∏ i : Fin n, exp (-a * x i ^ 2) := by
    rw [show -(β * (n : ℝ) / 4) * ∑ i : Fin n, x i ^ 2 =
      ∑ i : Fin n, (-a * x i ^ 2) by simp [a, Finset.mul_sum]]
    exact Real.exp_sum _ _
  have hqpowprod : q ^ p = ∏ i : Fin n, (1 + |x i|) ^ p := by
    exact (Real.finsetProd_rpow (Finset.univ : Finset (Fin n))
      (fun i => 1 + |x i|) (fun _ _ => by positivity) p).symm
  have hpoint : gaussianBetaGasWeight n β x ≤
      ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * x i ^ 2)) := by
    rw [gaussianBetaGasWeight_def]
    change exp (-(β * (n : ℝ) / 4) * ∑ i, x i ^ 2) *
      (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤ _
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
    have hp : 0 ≤ p := by
      dsimp [p]
      positivity
    have hmajor : Integrable
        (fun x : Fin n → ℝ =>
          ∏ i, ((1 + |x i|) ^ p * exp (-a * x i ^ 2)))
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
      Integrable.fintype_prod fun _ =>
        integrable_one_add_abs_rpow_mul_exp_neg_sq hp ha
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
  by_cases hn : n = 0
  · subst n
    simp [gaussianBetaGasPartitionFunction_def, gaussianBetaGasWeight_def]
  · let x₀ : Fin n → ℝ := fun i => (i : ℝ)
    have hx₀ : 0 < gaussianBetaGasWeight n β x₀ := by
      rw [gaussianBetaGasWeight_def]
      apply mul_pos (exp_pos _)
      apply Finset.prod_pos
      intro z hz
      have hz' : z.1 < z.2 := (Finset.mem_filter.mp hz).2
      have hlt : (z.1 : ℝ) < (z.2 : ℝ) := by exact_mod_cast hz'
      have hdiff : x₀ z.1 - x₀ z.2 ≠ 0 := by
        dsimp [x₀]
        exact (sub_ne_zero.mpr (ne_of_lt hlt))
      exact Real.rpow_pos_of_pos (abs_pos.mpr hdiff) β
    rw [gaussianBetaGasPartitionFunction_def]
    exact integral_pos_of_integrable_nonneg_ne_zero
      (continuous_gaussianBetaGasWeight n hβ.le)
      (integrable_gaussianBetaGasWeight n hβ)
      (gaussianBetaGasWeight_nonneg n β) hx₀.ne'

/-- The Gaussian beta-gas density is integrable for positive inverse temperature. -/
theorem integrable_gaussianBetaGasDensity (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (gaussianBetaGasDensity n β)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  convert (integrable_gaussianBetaGasWeight n hβ).div_const
    (gaussianBetaGasPartitionFunction n β) using 1
  funext x
  exact gaussianBetaGasDensity_def n β x

/-- The Gaussian beta-gas density is nonnegative for positive inverse temperature. -/
theorem gaussianBetaGasDensity_nonneg (n : ℕ) {β : ℝ} (hβ : 0 < β)
    (x : Fin n → ℝ) : 0 ≤ gaussianBetaGasDensity n β x := by
  rw [gaussianBetaGasDensity_def]
  exact div_nonneg (gaussianBetaGasWeight_nonneg n β x)
    (gaussianBetaGasPartitionFunction_pos n hβ).le

/-- The Gaussian beta-gas density integrates to one for positive inverse temperature. -/
theorem integral_gaussianBetaGasDensity (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∫ x, gaussianBetaGasDensity n β x
      ∂Measure.pi fun _ : Fin n => (volume : Measure ℝ)) = 1 := by
  simp only [gaussianBetaGasDensity_def, integral_div, ← gaussianBetaGasPartitionFunction_def]
  exact div_self (gaussianBetaGasPartitionFunction_pos n hβ).ne'

/-- The normalized Gaussian beta-gas measure has total mass one. -/
theorem isProbabilityMeasure_gaussianBetaGasMeasure (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (gaussianBetaGasMeasure n β) := by
  refine ⟨?_⟩
  rw [gaussianBetaGasMeasure_def, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianBetaGasDensity n hβ)
    (ae_of_all _ (gaussianBetaGasDensity_nonneg n hβ))]
  rw [integral_gaussianBetaGasDensity n hβ]
  norm_num

end TauCeti.Probability
