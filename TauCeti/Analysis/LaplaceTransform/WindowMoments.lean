/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.LaplaceTransform.GammaKernel
import TauCeti.MeasureTheory.Integral.Exp.GammaTail

/-!
# Gamma moments on scale windows

For a nonnegative function of at most exponential growth, one Gamma moment per window
`[U, L * U]` is controlled by the exponentially damped integral on the window and a constant
independent of `U`. The degree is at least `U` and is chosen independently of the function.
In the windowed Landau argument, the function is the positive part of the original input.

This is the integral estimate used in Levent Alpöge's
[formalization of the Riemann hypothesis for Dirichlet L-functions](https://github.com/leanprover-community/riemann-hypothesis)
(`Deduction.landau_window_ineq` and `Deduction.landau_window_key`), with arbitrary growth and
window rates.
-/

public section

open Filter MeasureTheory Real Set

namespace TauCeti

/-- A scale window lies in the positive half-line up to a null set, even when its lower endpoint
is zero or the window is empty. -/
private theorem scaleWindow_ae_le_Ioi {L U : ℝ} (hL : 1 < L) :
    Icc U (L * U) ≤ᵐ[volume] Ioi 0 := by
  have hsub : Icc U (L * U) ⊆ Ici 0 := by
    intro u hu
    apply mem_Ici.mpr
    by_contra! h
    exact (not_lt_of_ge (hu.1.trans hu.2)) (mul_lt_of_one_lt_left (hu.1.trans_lt h) hL)
  have hle : Icc U (L * U) ≤ᵐ[volume] Ici 0 := ae_of_all _ fun _ hu ↦ hsub hu
  exact hle.trans ((Ioi_ae_eq_Ici (μ := volume)).mono fun _ h ↦ h.mpr)

/-- The growth majorant bounds the Gamma moment off the window by the tail mass at a lower rate. -/
private theorem integral_mul_gammaKernel_tail_le {L U σ A B : ℝ} {n : ℕ}
    (hσA : A < σ) {f : ℝ → ℝ}
    (hm : IntegrableOn (fun u ↦ f u * (u ^ n * exp (-(σ * u)) / n.factorial))
      (Ioi 0 \ Icc U (L * U)))
    (hbound : ∀ᵐ u ∂volume.restrict (Ioi 0), f u ≤ B * exp (A * u)) :
    ∫ u in Ioi 0 \ Icc U (L * U), f u * (u ^ n * exp (-(σ * u)) / n.factorial) ≤
      B * ∫ u in Ioi 0 \ Icc U (L * U), u ^ n * exp (-((σ - A) * u)) / n.factorial := by
  rw [← integral_const_mul]
  have hmajor : IntegrableOn (fun u ↦ B * (u ^ n * exp (-((σ - A) * u)) / n.factorial)) (Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul_Ioi n (sub_pos.mpr hσA)).div_const _).const_mul B
  refine setIntegral_mono_ae_restrict hm (hmajor.mono_set sdiff_subset) ?_
  refine ae_restrict_of_ae_restrict_of_subset sdiff_subset ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hbound] with u hu hb
  have hb' : f u * exp (-(A * u)) ≤ B :=
    (mul_le_mul_of_nonneg_right hb (exp_pos _).le).trans_eq (by
      rw [mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one])
  rw [pow_mul_exp_neg_mul_div_factorial_eq_exp_neg_mul_mul n σ A u, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hb'
    (pow_mul_exp_neg_mul_div_factorial_nonneg n _ (mem_Ioi.mp hu).le)

/-- On the window, use the supremum of the kernel after shifting the rate by `θ`. -/
private theorem integral_mul_gammaKernel_on_window_le {L U σ A θ B : ℝ} {n : ℕ}
    (hWS : Icc U (L * U) ≤ᵐ[volume] Ioi 0) (hσθ : θ < σ) {f : ℝ → ℝ}
    (hm : IntegrableOn (fun u ↦ f u * (u ^ n * exp (-(σ * u)) / n.factorial)) (Ioi 0))
    (hf : ∀ᵐ u ∂volume.restrict (Ioi 0), 0 ≤ f u)
    (hbound : ∀ᵐ u ∂volume.restrict (Ioi 0), f u ≤ B * exp (A * u)) :
    ∫ u in Icc U (L * U), f u * (u ^ n * exp (-(σ * u)) / n.factorial) ≤
      (∫ u in Icc U (L * U), f u * exp (-(θ * u))) / (σ - θ) ^ n := by
  let W := Icc U (L * U)
  let K (a u : ℝ) := u ^ n * exp (-(a * u)) / n.factorial
  let g := fun u ↦ f u * exp (-(θ * u))
  have hw := Measure.restrict_mono_ae hWS
  have hK : Continuous (K σ) := by dsimp [K]; fun_prop
  -- The kernel does not vanish on `(0, ∞)`, so the integrable moment gives measurability of `f`.
  have hfm : AEStronglyMeasurable f (volume.restrict W) := by
    have hmW := (hm.mono_set_ae hWS).aestronglyMeasurable
    have hmK := hmW.aemeasurable.div hK.measurable.aemeasurable
    refine hmK.aestronglyMeasurable.congr ?_
    filter_upwards [ae_mono hw (ae_restrict_mem measurableSet_Ioi)] with u hu
    exact mul_div_cancel_right₀ _ (by dsimp [K]; positivity [(mem_Ioi.mp hu)])
  have hgmaj : IntegrableOn (fun u ↦ B * exp ((A - θ) * u)) W :=
    (by fun_prop : Continuous (fun u ↦ B * exp ((A - θ) * u))).continuousOn.integrableOn_compact
      isCompact_Icc
  have hgm : AEStronglyMeasurable g (volume.restrict W) :=
    hfm.mul (by fun_prop : AEStronglyMeasurable (fun u ↦ exp (-(θ * u))) _)
  have hg : IntegrableOn g W := by
    refine hgmaj.mono_nonneg hgm ?_ ?_
    · filter_upwards [ae_mono hw hf] with u hu using mul_nonneg hu (exp_pos _).le
    · filter_upwards [ae_mono hw hbound] with u hb
      simpa only [g, mul_assoc, ← exp_add, ← sub_eq_add_neg, ← sub_mul] using
        mul_le_mul_of_nonneg_right hb (exp_pos (-(θ * u))).le
  rw [div_eq_mul_inv, ← integral_mul_const]
  apply setIntegral_mono_ae_restrict (hm.mono_set_ae hWS) (hg.mul_const _)
  filter_upwards [ae_mono hw hf, ae_mono hw (ae_restrict_mem measurableSet_Ioi)] with u hu hs
  rw [pow_mul_exp_neg_mul_div_factorial_eq_exp_neg_mul_mul n σ θ u, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (pow_mul_exp_neg_mul_div_factorial_le_inv_pow n (sub_pos.mpr hσθ) (mem_Ioi.mp hs).le)
    (mul_nonneg hu (exp_pos _).le)

/-- Split a tilted Gamma moment into its contribution on a scale window and its tail. -/
private theorem integral_mul_gammaKernel_le_of_tail {L U σ A θ B C : ℝ} {n : ℕ}
    (hWS : Icc U (L * U) ≤ᵐ[volume] Ioi 0) (hσA : A < σ) (hσθ : θ < σ)
    (htail : ∫ u in Ioi 0 \ Icc U (L * U),
      u ^ n * exp (-((σ - A) * u)) / n.factorial ≤ C / (σ - θ) ^ n)
    (f : ℝ → ℝ) (hf : ∀ᵐ u ∂volume.restrict (Ioi 0), 0 ≤ f u)
    (hbound : ∀ᵐ u ∂volume.restrict (Ioi 0), f u ≤ B * exp (A * u)) :
    ∫ u in Ioi 0, f u * (u ^ n * exp (-(σ * u)) / n.factorial) ≤
      ((∫ u in Icc U (L * U), f u * exp (-(θ * u))) + B * C) / (σ - θ) ^ n := by
  let W := Icc U (L * U)
  let S := Ioi (0 : ℝ)
  let K (a u : ℝ) := u ^ n * exp (-(a * u)) / n.factorial
  let m := fun u ↦ f u * K σ u
  let g := fun u ↦ f u * exp (-(θ * u))
  have hw := Measure.restrict_mono_ae hWS
  have hg0 : 0 ≤ᵐ[volume.restrict W] g := by
    filter_upwards [ae_mono hw hf] with u hu
    exact mul_nonneg hu (exp_pos _).le
  have hB : 0 ≤ B := by
    have : (ae (volume.restrict S)).NeBot := ae_restrict_neBot.mpr (by simp [S])
    obtain ⟨u, h₁, h₂⟩ := (hf.and hbound).exists
    exact nonneg_of_mul_nonneg_left (h₁.trans h₂) (exp_pos _)
  by_cases hm : IntegrableOn m S
  · have hWin : ∫ u in W, m u ≤ (∫ u in W, g u) / (σ - θ) ^ n :=
      integral_mul_gammaKernel_on_window_le hWS hσθ hm hf hbound
    have hTail : ∫ u in S \ W, m u ≤ B * C / (σ - θ) ^ n := by
      rw [mul_div_assoc]
      exact (integral_mul_gammaKernel_tail_le hσA (hm.mono_set sdiff_subset) hbound).trans
        (mul_le_mul_of_nonneg_left htail hB)
    have heq : (∫ u in W ∩ S, m u) = ∫ u in W, m u :=
      setIntegral_congr_set (hWS.mono fun _ h ↦ ⟨And.left, fun hw ↦ ⟨hw, h hw⟩⟩)
    have hsplit := setIntegral_sdiff (t := W ∩ S)
      (measurableSet_Icc.inter measurableSet_Ioi) hm inter_subset_right
    rw [sdiff_inter_self_eq_sdiff, heq] at hsplit
    calc
      ∫ u in S, m u ≤ ((∫ u in W, g u) / (σ - θ) ^ n) + B * C / (σ - θ) ^ n := by
        linarith only [hsplit, hWin, hTail]
      _ = _ := (add_div ..).symm
  · -- Outside the domain of the Bochner integral the left side is zero.
    have hmass0 : 0 ≤ ∫ u in S \ W, K (σ - A) u := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff (measurableSet_Icc (a := U)
        (b := L * U)))] with u hu
      exact pow_mul_exp_neg_mul_div_factorial_nonneg n _ (mem_Ioi.mp hu.1).le
    have hC : 0 ≤ C := by
      simpa only [zero_mul] using
        (le_div_iff₀ (pow_pos (sub_pos.mpr hσθ) n)).mp (hmass0.trans htail)
    rw [integral_undef (f := m) hm]
    exact div_nonneg (add_nonneg (integral_nonneg_of_ae hg0) (mul_nonneg hB hC)) (by positivity)

/-- Given a growth rate `A`, a damping rate `θ` and a window ratio `L > 1`, choose a single
expansion rate `σ > max A θ`. At each scale `U` there is a degree `n ≥ U` for which every
nonnegative input bounded above by `B exp(Au)` on `(0, ∞)` has Gamma moment at most the sum of
its damped window integral and `B * C`, divided by `(σ - θ)^n`. Both bounds on the input
are almost everywhere; no separate measurability assumption is needed for the inequality.
The same rate, constant and choice of degree work for every input. -/
theorem exists_integral_mul_gammaKernel_le_window (A θ : ℝ) {L : ℝ} (hL : 1 < L) :
    ∃ σ > max A θ, ∃ C > 0, ∀ U : ℝ, ∃ n : ℕ, U ≤ n ∧
      ∀ (f : ℝ → ℝ) {B : ℝ}, (∀ᵐ u ∂volume.restrict (Ioi 0), 0 ≤ f u) →
        (∀ᵐ u ∂volume.restrict (Ioi 0), f u ≤ B * exp (A * u)) →
        ∫ u in Ioi 0, f u * (u ^ n * exp (-(σ * u)) / n.factorial) ≤
          ((∫ u in Icc U (L * U), f u * exp (-(θ * u))) + B * C) / (σ - θ) ^ n := by
  obtain ⟨τ, hτ, C, hC, h⟩ := exists_integral_gammaKernel_sdiff_Icc_mul_le (A - θ) hL
  have hA : A - θ < τ := (le_max_right ..).trans_lt hτ
  have hθ : 0 < τ := zero_lt_one.trans ((le_max_left ..).trans_lt hτ)
  refine ⟨τ + θ, max_lt (by linarith) (by linarith), C, hC, fun U ↦ ?_⟩
  obtain ⟨n, hn, ht⟩ := h U
  have hrate : τ + θ - A = τ - (A - θ) := by ring
  refine ⟨n, hn, fun f {_} hf hb ↦
    integral_mul_gammaKernel_le_of_tail (scaleWindow_ae_le_Ioi hL)
      (σ := τ + θ) (by linarith) (by linarith) ?_ f hf hb⟩
  simpa only [hrate, add_sub_cancel_right] using ht

end TauCeti
