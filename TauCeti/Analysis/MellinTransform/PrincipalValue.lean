/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Topology.EMetricSpace.BoundedVariation

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.BoundedVariation.OneDimensional.Reparam
import TauCeti.Analysis.Fourier.DirichletJordan
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.TruncatedInversion
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Principal-value Mellin inversion

Assume the Mellin integral converges absolutely on the vertical line of inversion. At a positive
point where the input has locally bounded variation, symmetric truncations of the inverse Mellin
integral converge to the mean of the left and right limits. In logarithmic coordinates, this is
Dirichlet–Jordan Fourier inversion for an exponentially weighted function, using
`TauCeti.intervalIntegral_cpow_smul_mellin_eq` for the finite truncations.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, §5.1.
-/

public section

open Complex Filter MeasureTheory Set Topology
open scoped FourierTransform

namespace MellinConvergent

private theorem tendsto_oneSided_exp_neg_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {σ x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hv : BoundedVariationOn f (Icc (x - δ) (x + δ))) :
    let g := fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u))
    Tendsto g (𝓝[<] (-Real.log x)) (𝓝 (Real.exp (σ * Real.log x) • f.rightLim x)) ∧
      Tendsto g (𝓝[>] (-Real.log x)) (𝓝 (Real.exp (σ * Real.log x) • f.leftLim x)) := by
  let u₀ := -Real.log x
  let φ := fun u : ℝ ↦ Real.exp (-u)
  let w := fun u : ℝ ↦ Real.exp (-σ * u)
  have hφ : φ u₀ = x := by simp [φ, u₀, Real.exp_log hx]
  have hφc : ContinuousAt φ u₀ := by fun_prop
  have hφa : StrictAnti φ := fun _ _ hab ↦ Real.exp_lt_exp.mpr (neg_lt_neg hab)
  let g := fun u : ℝ ↦ w u • f (φ u)
  have hφL : Tendsto φ (𝓝[<] u₀) (𝓝[>] x) := by
    rw [← hφ]
    exact hφc.continuousWithinAt.tendsto_nhdsWithin hφa.mapsTo_Iio
  have hφR : Tendsto φ (𝓝[>] u₀) (𝓝[<] x) := by
    rw [← hφ]
    exact hφc.continuousWithinAt.tendsto_nhdsWithin hφa.mapsTo_Ioi
  have hmem : Icc (x - δ) (x + δ) ∈ 𝓝 x :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hl := hv.tendsto_leftLim_of_mem_nhdsLT (mem_nhdsWithin_of_mem_nhds hmem)
  have hr := hv.tendsto_rightLim_of_mem_nhdsGT (mem_nhdsWithin_of_mem_nhds hmem)
  have hw : ContinuousAt w u₀ := by fun_prop
  have hGL : Tendsto g (𝓝[<] u₀) (𝓝 (w u₀ • f.rightLim x)) :=
    (hw.tendsto.mono_left nhdsWithin_le_nhds).smul (hr.comp hφL)
  have hGR : Tendsto g (𝓝[>] u₀) (𝓝 (w u₀ • f.leftLim x)) :=
    (hw.tendsto.mono_left nhdsWithin_le_nhds).smul (hl.comp hφR)
  simpa only [g, φ, w, u₀, neg_mul_neg] using And.intro hGL hGR

/-- **Principal-value Mellin inversion.** If the Mellin integral of `f` converges absolutely
on the line `Re s = σ` and `f` has bounded variation near `x > 0`, truncating the inverse integral
symmetrically in height recovers the mean of the one-sided limits at `x`. The proof transfers
Dirichlet–Jordan inversion via `TauCeti.intervalIntegral_cpow_smul_mellin_eq`. For the analytic
argument, see Montgomery and Vaughan, *Multiplicative Number Theory I*, §5.1. -/
theorem tendsto_truncated_mellinInv_mellin
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
  have hφ : φ u₀ = x := by simp [φ, u₀, Real.exp_log hx]
  have hmem : Icc (x - δ) (x + δ) ∈ 𝓝 (φ u₀) := by
    rw [hφ]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hφa : StrictAnti φ := fun _ _ hab ↦ Real.exp_lt_exp.mpr (neg_lt_neg hab)
  obtain ⟨r, hr, hgv⟩ := hv.exists_Icc_smul_comp hmem
    (t := univ) univ_mem (by fun_prop : ContinuousAt φ u₀)
    (Or.inr (hφa.antitone.antitoneOn _)) (by fun_prop : ContDiffOn ℝ 1 w univ)
  have H := hgi.tendsto_intervalIntegral_fourierInv_fourier_of_boundedVariationOn
    (x := u₀) hr hgv
  obtain ⟨hGL, hGR⟩ := tendsto_oneSided_exp_neg_smul (σ := σ) hx hδ hv
  have hGL' : g.leftLim u₀ = w u₀ • f.rightLim x := by
    simpa [g, φ, w, u₀] using leftLim_eq_of_tendsto hGL
  have hGR' : g.rightLim u₀ = w u₀ • f.leftLim x := by
    simpa [g, φ, w, u₀] using rightLim_eq_of_tendsto hGR
  rw [hGL', hGR', ← smul_add, add_comm (f.rightLim x)] at H
  have hheight : Tendsto (fun T : ℝ ↦ T / (2 * Real.pi)) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm, id_eq] using
      tendsto_id.const_mul_atTop (by positivity : 0 < (2 * Real.pi)⁻¹)
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
