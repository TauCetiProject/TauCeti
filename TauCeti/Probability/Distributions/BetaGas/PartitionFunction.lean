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

* `twoParticleGaussianBetaGasPartitionFunction` is the unnormalized density integral.
* `integral_twoParticleGaussianBetaGasPartitionFunction` evaluates it for every positive `β`.
-/

public section
noncomputable section

open MeasureTheory Real
open Set

namespace TauCeti.Probability

/-- The two-particle beta-gas partition function for `V x = x ^ 2 / 2`. -/
def twoParticleGaussianBetaGasPartitionFunction (β : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, exp (-β / 2 * (p.1 ^ 2 + p.2 ^ 2)) * |p.1 - p.2| ^ β
    ∂(volume.prod volume)

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

/-- The two-particle Gaussian beta-gas partition function is finite and has this closed form. -/
theorem integral_twoParticleGaussianBetaGasPartitionFunction {β : ℝ} (hβ : 0 < β) :
    twoParticleGaussianBetaGasPartitionFunction β =
      2 ^ (β + 1) * sqrt π * β ^ (-(β + 2) / 2) * Gamma ((β + 1) / 2) := by
  let f : ℝ × ℝ → ℝ :=
    fun p => exp (-β / 2 * (p.1 ^ 2 + p.2 ^ 2)) * |p.1 - p.2| ^ β
  let g : ℝ → ℝ := fun d => |d| ^ β * exp (-(β / 4 * d ^ 2))
  let h : ℝ → ℝ := fun z => exp (-(β * z ^ 2))
  have hpoint : ∀ p, f (betaGasUncenter p) = g p.1 * h p.2 := by
    intro p
    simp only [f, g, h, betaGasUncenter]
    have hd : (p.2 + p.1 / 2) - (p.2 - p.1 / 2) = p.1 := by ring
    have hexp :
        -β / 2 * ((p.2 + p.1 / 2) ^ 2 + (p.2 - p.1 / 2) ^ 2) =
          -(β / 4 * p.1 ^ 2) + -(β * p.2 ^ 2) := by ring
    rw [hd, hexp, exp_add]
    ring
  have hchange :
      (∫ p : ℝ × ℝ, f p ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, g p.1 * h p.2 ∂(volume.prod volume) := by
    rw [← measurePreserving_betaGasUncenter.integral_comp'
      (f := betaGasUncenterEquiv) f]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hg : ∫ d : ℝ, g d =
      (β / 4) ^ (-((β + 1) / 2)) * Gamma ((β + 1) / 2) := by
    have h := integral_abs_rpow_mul_exp_neg_sq (q := β) (b := β / 4)
      (by linarith) (by positivity)
    rw [show -(β + 1) / 2 = -((β + 1) / 2) by ring] at h
    simpa [g] using h
  have hh : ∫ z : ℝ, h z = β ^ (-(1 : ℝ) / 2) * sqrt π := by
    have hGaussian : (∫ z : ℝ, exp (-(β * z ^ 2))) = sqrt (π / β) := by
      simpa only [neg_mul] using integral_gaussian β
    change (∫ z : ℝ, exp (-(β * z ^ 2))) = _
    rw [hGaussian, Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow β,
      show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hβ.le]
    ring
  rw [twoParticleGaussianBetaGasPartitionFunction, hchange, integral_prod_mul, hg, hh]
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

end TauCeti.Probability
