/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Gamma

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# A two-particle Gaussian beta gas

This file evaluates the partition function of the two-particle beta gas in the quadratic
potential `V x = x ^ 2 / 2`.

## Main results

* `integrable_twoParticleGaussianBetaGasWeight` proves finiteness of the density integral.
* `integral_twoParticleGaussianBetaGasWeight` evaluates it for every positive `β`.
* `integral_twoParticleGaussianBetaGasWeight_pos` proves that integral is positive.
-/

public section
noncomputable section

open MeasureTheory Real
open Set

namespace TauCeti.Probability

/-- The two-particle Gaussian beta-gas weight in coordinate form. -/
def twoParticleGaussianBetaGasWeight (β : ℝ) (p : ℝ × ℝ) : ℝ :=
  exp (-β / 2 * (p.1 ^ 2 + p.2 ^ 2)) * |p.1 - p.2| ^ β

/-- The defining equation of the two-particle Gaussian beta-gas weight. -/
theorem twoParticleGaussianBetaGasWeight_def (β : ℝ) (p : ℝ × ℝ) :
    twoParticleGaussianBetaGasWeight β p =
      exp (-β / 2 * (p.1 ^ 2 + p.2 ^ 2)) * |p.1 - p.2| ^ β := by
  rw [twoParticleGaussianBetaGasWeight]

private def betaGasCenter (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 - p.2, p.2 + (p.1 - p.2) / 2)

private def betaGasUncenter (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2 + p.1 / 2, p.2 - p.1 / 2)

private def betaGasUncenterEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := betaGasUncenter
  invFun := betaGasCenter
  left_inv p := by
    ext <;> dsimp [betaGasUncenter, betaGasCenter] <;> ring
  right_inv p := by
    ext <;> dsimp [betaGasUncenter, betaGasCenter] <;> ring
  measurable_toFun := by
    -- Unfold `betaGasUncenter` in the measurability goal.
    change Measurable (fun p : ℝ × ℝ => (p.2 + p.1 / 2, p.2 - p.1 / 2))
    fun_prop
  measurable_invFun := by
    -- Unfold `betaGasCenter` in the measurability goal.
    change Measurable (fun p : ℝ × ℝ => (p.1 - p.2, p.2 + (p.1 - p.2) / 2))
    fun_prop

private lemma measurePreserving_betaGasUncenter :
    MeasurePreserving betaGasUncenter (volume.prod volume) (volume.prod volume) := by
  let shift : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 + -(p.1 / 2))
  have hshift : MeasurePreserving shift (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product
      (μa := (volume : Measure ℝ)) (μb := (volume : Measure ℝ))
      (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ))
      (f := id) (g := fun d z : ℝ => z + -(d / 2))
      (MeasurePreserving.id (volume : Measure ℝ)) ?_ ?_
    · fun_prop
    · filter_upwards with d
      have hd : MeasurePreserving (fun z : ℝ => z + -(d / 2)) volume volume :=
        measurePreserving_add_right (G := ℝ) (μ := (volume : Measure ℝ)) (-(d / 2))
      exact hd.map_eq
  have hadd : MeasurePreserving (fun p : ℝ × ℝ => (p.1 + p.2, p.2))
      (volume.prod volume) (volume.prod volume) :=
    measurePreserving_add_prod volume volume
  convert hadd.comp hshift using 1
  ext p <;> dsimp [betaGasUncenter, shift] <;> ring

private lemma betaGasUncenter_weight (β : ℝ) (p : ℝ × ℝ) :
    exp (-β / 2 * ((betaGasUncenter p).1 ^ 2 + (betaGasUncenter p).2 ^ 2)) *
        |(betaGasUncenter p).1 - (betaGasUncenter p).2| ^ β =
      (|p.1| ^ β * exp (-(β / 4 * p.1 ^ 2))) * exp (-(β * p.2 ^ 2)) := by
  simp only [betaGasUncenter]
  have hd : (p.2 + p.1 / 2) - (p.2 - p.1 / 2) = p.1 := by ring
  have hexp :
      -β / 2 * ((p.2 + p.1 / 2) ^ 2 + (p.2 - p.1 / 2) ^ 2) =
        -(β / 4 * p.1 ^ 2) + -(β * p.2 ^ 2) := by ring
  rw [hd, hexp, exp_add]
  ring

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
    rw [div_rpow hβ.le (by norm_num : (0 : ℝ) ≤ 4)]
    rw [rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_eq_mul_inv, inv_inv, h4]
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
    _ = _ := by rw [hβpow]; rw [show -((β + 2) / 2) = -(β + 2) / 2 by ring]

/-- The two-particle Gaussian beta-gas weight is integrable for positive inverse temperature. -/
theorem integrable_twoParticleGaussianBetaGasWeight {β : ℝ} (hβ : 0 < β) :
    Integrable (twoParticleGaussianBetaGasWeight β) (volume.prod volume) := by
  have hweight : twoParticleGaussianBetaGasWeight β =
      fun p : ℝ × ℝ => exp (-β / 2 * (p.1 ^ 2 + p.2 ^ 2)) * |p.1 - p.2| ^ β := by
    funext p
    exact twoParticleGaussianBetaGasWeight_def β p
  rw [hweight]
  apply (measurePreserving_betaGasUncenter.integrable_comp_emb
    betaGasUncenterEquiv.measurableEmbedding).mp
  have hg := integrable_abs_rpow_mul_exp_neg_mul_sq (q := β) (b := β / 4)
    (by linarith) (by positivity)
  have hh : Integrable (fun z : ℝ => exp (-(β * z ^ 2))) := by
    simpa only [neg_mul] using integrable_exp_neg_mul_sq hβ
  have h := hg.mul_prod hh
  convert h using 1
  ext p
  simpa only [Function.comp_apply, neg_mul] using betaGasUncenter_weight β p

/-- The two-particle Gaussian beta-gas density integral has this closed form. -/
theorem integral_twoParticleGaussianBetaGasWeight {β : ℝ} (hβ : 0 < β) :
    (∫ p : ℝ × ℝ, twoParticleGaussianBetaGasWeight β p ∂(volume.prod volume)) =
      2 ^ (β + 1) * sqrt π * β ^ (-(β + 2) / 2) * Gamma ((β + 1) / 2) := by
  simp_rw [twoParticleGaussianBetaGasWeight_def]
  let f : ℝ × ℝ → ℝ :=
    fun p => exp (-β / 2 * (p.1 ^ 2 + p.2 ^ 2)) * |p.1 - p.2| ^ β
  let g : ℝ → ℝ := fun d => |d| ^ β * exp (-(β / 4 * d ^ 2))
  let h : ℝ → ℝ := fun z => exp (-(β * z ^ 2))
  have hpoint : ∀ p, f (betaGasUncenter p) = g p.1 * h p.2 := by
    intro p
    exact betaGasUncenter_weight β p
  have hchange :
      (∫ p : ℝ × ℝ, f p ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, g p.1 * h p.2 ∂(volume.prod volume) := by
    rw [← measurePreserving_betaGasUncenter.integral_comp'
      (f := betaGasUncenterEquiv) f]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hg : ∫ d : ℝ, g d =
      (β / 4) ^ (-((β + 1) / 2)) * Gamma ((β + 1) / 2) := by
    have h := integral_abs_rpow_mul_exp_neg_mul_sq (q := β) (b := β / 4)
      (by linarith) (by positivity)
    -- Normalize the negative exponent to the form used by `rpow_neg`.
    rw [show -(β + 1) / 2 = -((β + 1) / 2) by ring] at h
    simpa [g] using h
  have hh : ∫ z : ℝ, h z = β ^ (-(1 : ℝ) / 2) * sqrt π := by
    have hGaussian : (∫ z : ℝ, exp (-(β * z ^ 2))) = sqrt (π / β) := by
      simpa only [neg_mul] using integral_gaussian β
    dsimp only [h]
    -- Express the denominator square root as a negative real power.
    rw [hGaussian, Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow β,
      show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hβ.le]
    ring
  dsimp only [f] at hchange
  rw [hchange, integral_prod_mul, hg, hh]
  exact betaGas_integral_algebra hβ

/-- The two-particle Gaussian beta-gas density integral is positive. -/
theorem integral_twoParticleGaussianBetaGasWeight_pos {β : ℝ} (hβ : 0 < β) :
    0 < ∫ p : ℝ × ℝ, twoParticleGaussianBetaGasWeight β p ∂(volume.prod volume) := by
  rw [integral_twoParticleGaussianBetaGasWeight hβ]
  have hGamma : 0 < Gamma ((β + 1) / 2) := Gamma_pos_of_pos (by linarith)
  positivity

end TauCeti.Probability
