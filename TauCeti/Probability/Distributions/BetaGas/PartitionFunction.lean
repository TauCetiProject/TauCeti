/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Gamma
public import TauCeti.Probability.Distributions.BetaGas.Basic

import TauCeti.Analysis.SpecialFunctions.Gaussian.Integral
import TauCeti.MeasureTheory.Measure.Lebesgue.DifferenceMidpoint

/-!
# The two-particle Gaussian beta-gas partition function

For inverse temperature `0 < β`, the unnormalized weight on `ℝ × ℝ` is
`exp (-β / 2 * (x₁ ^ 2 + x₂ ^ 2)) * |x₁ - x₂| ^ β`. Its Lebesgue integral is
`2 ^ (β + 1) * √π * β ^ (-(β + 2) / 2) * Γ ((β + 1) / 2)`.
This is the `n = 2` Gaussian Selberg normalization for the unordered Hermite beta-ensemble; the
choices `β = 1` and `β = 2` give the `2 × 2` GOE and GUE eigenvalue weights in the
`1 / √2` scaling. The general-`n` Gaussian Selberg evaluation remains open.

## Main results

* `betaGasPartitionFunction_two_quadratic_eq` evaluates the general beta-gas partition function
  for the quadratic potential at `n = 2` and `0 < β`.
-/

public section
noncomputable section

open MeasureTheory Real
open Set

namespace TauCeti.Probability

private def twoParticleGaussianBetaGasWeight (β : ℝ) (p : ℝ × ℝ) : ℝ :=
  exp (-β / 2 * (p.1 ^ 2 + p.2 ^ 2)) * |p.1 - p.2| ^ β

private theorem twoParticleGaussianBetaGasWeight_def (β : ℝ) (p : ℝ × ℝ) :
    twoParticleGaussianBetaGasWeight β p =
      exp (-β / 2 * (p.1 ^ 2 + p.2 ^ 2)) * |p.1 - p.2| ^ β := by
  rw [twoParticleGaussianBetaGasWeight]

private lemma betaGasUncenter_weight (β : ℝ) (p : ℝ × ℝ) :
    twoParticleGaussianBetaGasWeight β (TauCeti.MeasureTheory.differenceMidpointEquiv p) =
      (|p.1| ^ β * exp (-(β / 4 * p.1 ^ 2))) * exp (-(β * p.2 ^ 2)) := by
  simp only [twoParticleGaussianBetaGasWeight, TauCeti.MeasureTheory.differenceMidpointEquiv_apply]
  have hd : (p.2 + p.1 / 2) - (p.2 - p.1 / 2) = p.1 := by ring
  have hexp :
      -β / 2 * ((p.2 + p.1 / 2) ^ 2 + (p.2 - p.1 / 2) ^ 2) =
        -(β / 4 * p.1 ^ 2) + -(β * p.2 ^ 2) := by ring
  rw [hd, hexp, exp_add]
  ring

private lemma rpow_div_eq_mul_rpow_neg {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a / b) ^ q = a ^ q * b ^ (-q) := by
  rw [div_rpow ha hb, div_eq_mul_inv, ← rpow_neg hb]

private lemma betaGas_integral_algebra {β : ℝ} (hβ : 0 < β) :
    (β / 4) ^ (-((β + 1) / 2)) * Gamma ((β + 1) / 2) *
        (β ^ (-(1 : ℝ) / 2) * sqrt π) =
      2 ^ (β + 1) * sqrt π * β ^ (-(β + 2) / 2) * Gamma ((β + 1) / 2) := by
  have h4 : (4 : ℝ) ^ ((β + 1) / 2) = 2 ^ (β + 1) := by
    calc
      _ = ((2 : ℝ) ^ (2 : ℝ)) ^ ((β + 1) / 2) := by norm_num
      _ = 2 ^ ((2 : ℝ) * ((β + 1) / 2)) := by
        rw [rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = _ := by congr 1; ring
  have hfactor :
      (β / 4) ^ (-((β + 1) / 2)) =
        β ^ (-((β + 1) / 2)) * 2 ^ (β + 1) := by
    calc
      _ = β ^ (-((β + 1) / 2)) * 4 ^ ((β + 1) / 2) := by
        rw [rpow_div_eq_mul_rpow_neg hβ.le (by norm_num : (0 : ℝ) ≤ 4), neg_neg]
      _ = _ := by rw [h4]
  have hβpow :
      β ^ (-((β + 1) / 2)) * β ^ (-(1 : ℝ) / 2) =
        β ^ (-((β + 2) / 2)) := by
    rw [← rpow_add hβ]
    congr 1
    ring
  rw [hfactor]
  calc
    _ = 2 ^ (β + 1) * sqrt π *
        (β ^ (-((β + 1) / 2)) * β ^ (-(1 : ℝ) / 2)) * Gamma ((β + 1) / 2) := by ring
    _ = _ := by rw [hβpow]; simp only [neg_div]

private lemma betaGas_difference_integral {β : ℝ} (hβ : 0 < β) :
    (∫ d : ℝ, |d| ^ β * exp (-(β / 4 * d ^ 2))) =
      (β / 4) ^ (-((β + 1) / 2)) * Gamma ((β + 1) / 2) := by
  have h := integral_abs_rpow_mul_exp_neg_mul_sq (q := β) (b := β / 4)
    (by linarith) (by positivity)
  rw [neg_div] at h
  simpa only [neg_mul] using h

private theorem twoParticleGaussianBetaGasWeight_integral_eq {β : ℝ} (hβ : 0 < β) :
    (∫ p : ℝ × ℝ, twoParticleGaussianBetaGasWeight β p) =
      2 ^ (β + 1) * sqrt π * β ^ (-(β + 2) / 2) * Gamma ((β + 1) / 2) := by
  rw [Measure.volume_eq_prod]
  let f : ℝ × ℝ → ℝ := twoParticleGaussianBetaGasWeight β
  let g : ℝ → ℝ := fun d => |d| ^ β * exp (-(β / 4 * d ^ 2))
  let h : ℝ → ℝ := fun z => exp (-(β * z ^ 2))
  have hpoint : ∀ p, f (TauCeti.MeasureTheory.differenceMidpointEquiv p) =
      g p.1 * h p.2 := by
    intro p
    exact betaGasUncenter_weight β p
  have hchange :
      (∫ p : ℝ × ℝ, f p ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, g p.1 * h p.2 ∂(volume.prod volume) := by
    have hpres := TauCeti.MeasureTheory.measurePreserving_differenceMidpointEquiv.integral_comp' f
    rw [Measure.volume_eq_prod] at hpres
    rw [← hpres]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hg : ∫ d : ℝ, g d =
      (β / 4) ^ (-((β + 1) / 2)) * Gamma ((β + 1) / 2) := by
    exact betaGas_difference_integral hβ
  have hh : ∫ z : ℝ, h z = β ^ (-(1 : ℝ) / 2) * sqrt π := by
    exact integral_exp_neg_mul_sq_eq_rpow hβ
  dsimp only [f] at hchange
  rw [hchange, integral_prod_mul, hg, hh]
  exact betaGas_integral_algebra hβ

private theorem betaGasWeight_two_quadratic_eq (β : ℝ) (x : Fin 2 → ℝ) :
    betaGasWeight 2 β (fun t => t ^ 2 / 2) x =
      twoParticleGaussianBetaGasWeight β (x 0, x 1) := by
  have hpairs : betaGasPairs 2 = {(0, 1)} := by
    ext ⟨i, j⟩
    simp only [mem_betaGasPairs, Finset.mem_singleton]
    fin_cases i <;> fin_cases j <;> decide
  rw [betaGasWeight_def, twoParticleGaussianBetaGasWeight_def, hpairs]
  simp only [Fin.sum_univ_two, Nat.cast_ofNat, Finset.prod_singleton]
  congr 2
  ring

private theorem betaGasPartitionFunction_two_quadratic_eq_pair (β : ℝ) :
    betaGasPartitionFunction 2 β (fun t => t ^ 2 / 2) =
      ∫ p : ℝ × ℝ, twoParticleGaussianBetaGasWeight β p := by
  rw [betaGasPartitionFunction_def,
    ← (volume_preserving_finTwoArrow ℝ).integral_comp' (twoParticleGaussianBetaGasWeight β)]
  apply integral_congr_ae
  filter_upwards with x
  simpa only [MeasurableEquiv.finTwoArrow_apply, Function.comp_apply] using
    betaGasWeight_two_quadratic_eq β x

/-- The quadratic-potential beta-gas partition function at `n = 2`, for positive inverse
temperature. -/
theorem betaGasPartitionFunction_two_quadratic_eq {β : ℝ} (hβ : 0 < β) :
    betaGasPartitionFunction 2 β (fun t => t ^ 2 / 2) =
      2 ^ (β + 1) * sqrt π * β ^ (-(β + 2) / 2) * Gamma ((β + 1) / 2) := by
  rw [betaGasPartitionFunction_two_quadratic_eq_pair]
  exact twoParticleGaussianBetaGasWeight_integral_eq hβ

end TauCeti.Probability
