/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Topology.EMetricSpace.BoundedVariation

import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Fourier.DirichletJordan
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.TruncatedInversion

/-!
# Principal-value Mellin inversion

At a positive point where the input has locally bounded variation, symmetric truncations of
the inverse Mellin integral converge to the mean of the left and right limits. In logarithmic
coordinates, this is Dirichlet–Jordan Fourier inversion for an exponentially weighted function.
-/

public section

open Complex Filter MeasureTheory Set Topology
open scoped FourierTransform

namespace MellinConvergent

private theorem exists_boundedVariationOn_exp_neg_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {σ x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hv : BoundedVariationOn f (Icc (x - δ) (x + δ))) :
    ∃ r > 0, BoundedVariationOn (fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u)))
      (Icc (-Real.log x - r) (-Real.log x + r)) := by
  let u₀ := -Real.log x
  let φ := fun u : ℝ ↦ Real.exp (-u)
  let w := fun u : ℝ ↦ Real.exp (-σ * u)
  have hφ : φ u₀ = x := by simp [φ, u₀, Real.exp_log hx]
  have hφc : Continuous φ := by fun_prop
  have hφa : StrictAnti φ := fun _ _ hab ↦ Real.exp_lt_exp.mpr (neg_lt_neg hab)
  have hpre : u₀ ∈ φ ⁻¹' Ioo (x - δ) (x + δ) := by
    rw [mem_preimage, hφ]
    constructor <;> linarith
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_Ioo.preimage hφc) u₀ hpre
  let S := Icc (u₀ - r / 2) (u₀ + r / 2)
  have hmaps : MapsTo φ S (Icc (x - δ) (x + δ)) := by
    intro u hu
    apply Ioo_subset_Icc_self (hball ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hcomp : BoundedVariationOn (f ∘ φ) S :=
    ne_top_of_le_ne_top hv
      (eVariationOn.comp_le_of_antitoneOn f φ (hφa.antitone.antitoneOn _) hmaps)
  have hwc : ContDiffOn ℝ 1 w S := (by fun_prop : ContDiff ℝ 1 w).contDiffOn
  obtain ⟨C, hC⟩ := hwc.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hwv := hC.comp_boundedVariationOn (mapsTo_id _) (BoundedVariationOn.id_Icc _ _)
  exact ⟨r / 2, by positivity, hwv.fun_smul hcomp⟩

private theorem oneSidedLimits_exp_neg_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {σ x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hv : BoundedVariationOn f (Icc (x - δ) (x + δ))) :
    let g := fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u))
    g.leftLim (-Real.log x) = Real.exp (σ * Real.log x) • f.rightLim x ∧
      g.rightLim (-Real.log x) = Real.exp (σ * Real.log x) • f.leftLim x := by
  let u₀ := -Real.log x
  let φ := fun u : ℝ ↦ Real.exp (-u)
  let w := fun u : ℝ ↦ Real.exp (-σ * u)
  have hφ : φ u₀ = x := by simp [φ, u₀, Real.exp_log hx]
  have hφc : Continuous φ := by fun_prop
  have hφa : StrictAnti φ := fun _ _ hab ↦ Real.exp_lt_exp.mpr (neg_lt_neg hab)
  let g := fun u : ℝ ↦ w u • f (φ u)
  have hφL : Tendsto φ (𝓝[<] u₀) (𝓝[>] x) := tendsto_nhdsWithin_iff.mpr
    ⟨hφ ▸ hφc.continuousAt.continuousWithinAt,
      Filter.Eventually.mono self_mem_nhdsWithin (fun _ hu ↦ hφ ▸ hφa hu)⟩
  have hφR : Tendsto φ (𝓝[>] u₀) (𝓝[<] x) := tendsto_nhdsWithin_iff.mpr
    ⟨hφ ▸ hφc.continuousAt.continuousWithinAt,
      Filter.Eventually.mono self_mem_nhdsWithin (fun _ hu ↦ hφ ▸ hφa hu)⟩
  have hGL : g.leftLim u₀ = w u₀ • f.rightLim x := by
    obtain ⟨l, hl⟩ := hv.exists_tendsto_right x
    rw [show Icc (x - δ) (x + δ) ∩ Ioi x = Ioc x (x + δ) by grind,
      nhdsWithin_Ioc_eq_nhdsGT (by linarith)] at hl
    rw [rightLim_eq_of_tendsto hl]
    have hw : Tendsto w (𝓝[<] u₀) (𝓝 (w u₀)) :=
      (by fun_prop : Continuous w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact leftLim_eq_of_tendsto (hw.smul (hl.comp hφL))
  have hGR : g.rightLim u₀ = w u₀ • f.leftLim x := by
    obtain ⟨l, hl⟩ := hv.exists_tendsto_left x
    rw [show Icc (x - δ) (x + δ) ∩ Iio x = Ico (x - δ) x by grind,
      nhdsWithin_Ico_eq_nhdsLT (by linarith)] at hl
    rw [leftLim_eq_of_tendsto hl]
    have hw : Tendsto w (𝓝[>] u₀) (𝓝 (w u₀)) :=
      (by fun_prop : Continuous w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact rightLim_eq_of_tendsto (hw.smul (hl.comp hφR))
  simpa only [g, φ, w, u₀, neg_mul_neg] using And.intro hGL hGR

/-- **Principal-value Mellin inversion.** If the Mellin integral of `f` converges absolutely
on the line `Re s = σ` and `f` has bounded variation near `x > 0`, truncating the inverse integral
symmetrically in height recovers the mean of the one-sided limits at `x`. -/
theorem tendsto_truncated_mellinInv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → E} {σ x δ : ℝ} (hf : MellinConvergent f σ) (hx : 0 < x) (hδ : 0 < δ)
    (hv : BoundedVariationOn f (Icc (x - δ) (x + δ))) :
    Tendsto
      (fun T : ℝ ↦ (1 / (2 * Real.pi)) •
        ∫ y in -T..T, (x : ℂ) ^ (-(σ + y * I)) • mellin f (σ + y * I))
      atTop (𝓝 ((1 / 2 : ℝ) • (f.leftLim x + f.rightLim x))) := by
  let u₀ := -Real.log x
  let φ := fun u : ℝ ↦ Real.exp (-u)
  let w := fun u : ℝ ↦ Real.exp (-σ * u)
  let g := fun u ↦ w u • f (φ u)
  have hw (u : ℝ) : Complex.exp (-(σ : ℂ) * u) = (w u : ℂ) := by
    simp [w, Complex.ofReal_exp]
  have hgi : Integrable g := by
    simpa only [g, φ, hw, Complex.coe_smul] using
      (TauCeti.mellinConvergent_iff_integrable_exp_smul f σ).mp hf
  obtain ⟨r, hr, hgv⟩ := exists_boundedVariationOn_exp_neg_smul hx hδ hv
  have H := hgi.tendsto_intervalIntegral_fourierInv_fourier_of_boundedVariationOn
    (x := u₀) hr hgv
  obtain ⟨hGL, hGR⟩ := oneSidedLimits_exp_neg_smul (σ := σ) hx hδ hv
  have hGL' : g.leftLim u₀ = w u₀ • f.rightLim x := by simpa [g, φ, w, u₀] using hGL
  have hGR' : g.rightLim u₀ = w u₀ • f.leftLim x := by simpa [g, φ, w, u₀] using hGR
  rw [hGL', hGR', ← smul_add, add_comm (f.rightLim x)] at H
  have hheight : Tendsto (fun T : ℝ ↦ T / (2 * Real.pi)) atTop atTop :=
    (tendsto_id.const_mul_atTop (by positivity : 0 < (2 * Real.pi)⁻¹)).congr
      (fun T ↦ by rw [div_eq_mul_inv, mul_comm]; rfl)
  have H' := (H.comp hheight).const_smul ((x : ℂ) ^ (-σ : ℂ))
  have hw₀ : (x : ℂ) ^ (-σ : ℂ) * (w u₀ : ℂ) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le,
      ofReal_exp, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    simp only [u₀]
    push_cast
    ring
  have hcancel (z : E) : (x : ℂ) ^ (-σ : ℂ) • ((1 / 2 : ℝ) • w u₀ • z) =
      (1 / 2 : ℝ) • z := by
    calc
      _ = (1 / 2 : ℝ) • ((x : ℂ) ^ (-σ : ℂ) • (w u₀ • z)) := smul_comm _ _ _
      _ = _ := by rw [← Complex.coe_smul (w u₀) z, ← mul_smul, hw₀, one_smul]
  rw [hcancel] at H'
  exact H'.congr (fun T ↦ (TauCeti.intervalIntegral_cpow_smul_mellin_eq f σ hx T).symm)

end MellinConvergent
