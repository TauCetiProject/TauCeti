/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform

import TauCeti.Analysis.Fourier.Decay
import Mathlib.Analysis.MellinInversion

/-!
# Mellin decay on vertical strips

A compactly supported `C^N` function whose closed support lies in the positive half-line
has Mellin transform of size `O((1 + |Im s|)⁻ᴺ)`, uniformly as `Re s` ranges over any
compact set. In particular, smooth test functions have faster-than-polynomial decay on
vertical strips, as needed for absolutely convergent explicit formulas.

The logarithmic substitution turns the Mellin transform into the Fourier transform of
`u ↦ exp(-σu) • f(exp(-u))`. On a compact set of parameters `σ`, joint `C^N` regularity
bounds the derivatives in `u` through order `N` on one common compact support. The finite-order
Fourier decay bound then gives the result without assuming an additional derivative or
completeness of the target space.

The finite-order statement is motivated by the `C¹` bump estimate
[MellinOfPsi in PNT+](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a6eae76b4b06abf85b456a5491ff7a983879b9c8/PrimeNumberTheoremAnd/MellinCalculus.lean#L398).
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped FourierTransform

namespace TauCeti

section RealSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private lemma continuous_slice_iteratedFDeriv {N n : ℕ} {H : ℝ × ℝ → E}
    (hH : ContDiff ℝ N H) (hn : n ≤ N) :
    Continuous (fun p : ℝ × ℝ ↦ iteratedFDeriv ℝ n (fun u ↦ H (p.1, u)) p.2) := by
  have heq (p : ℝ × ℝ) :
      iteratedFDeriv ℝ n (fun u ↦ H (p.1, u)) p.2 =
        (iteratedFDeriv ℝ n H p).compContinuousLinearMap
          (fun _ ↦ ContinuousLinearMap.inr ℝ ℝ ℝ) := by
    have hc : ContDiff ℝ N (fun q : ℝ × ℝ ↦ H ((p.1, 0) + q)) :=
      hH.comp (contDiff_const.add contDiff_id)
    have hi := (ContinuousLinearMap.inr ℝ ℝ ℝ).iteratedFDeriv_comp_right hc p.2
      (by exact_mod_cast hn)
    simpa only [Function.comp_def, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
      add_zero, zero_add, iteratedFDeriv_comp_add_left, Prod.eta] using hi
  simp_rw [heq]
  exact (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n ↦ ContinuousLinearMap.inr ℝ ℝ ℝ)).comp
      (hH.continuous_iteratedFDeriv (by exact_mod_cast hn))

private lemma uniform_slice_bound {N : ℕ} {H : ℝ × ℝ → E}
    (hH : ContDiff ℝ N H) {K S : Set ℝ} (hK : IsCompact K) (hS : IsCompact S)
    (hsupp : ∀ σ ∈ K, tsupport (fun u ↦ H (σ, u)) ⊆ S) :
    ∃ C > 0, ∀ σ ∈ K, ∀ n ≤ N, ∀ u,
      ‖iteratedFDeriv ℝ n (fun v ↦ H (σ, v)) u‖ ≤ C := by
  have hb (n : Fin (N + 1)) : ∃ C : ℝ, ∀ p ∈ K ×ˢ S,
      ‖iteratedFDeriv ℝ (n : ℕ) (fun v ↦ H (p.1, v)) p.2‖ ≤ C :=
    (hK.prod hS).exists_bound_of_continuousOn
      (continuous_slice_iteratedFDeriv hH (by omega)).continuousOn
  choose C hC using hb
  let B : ℝ := 1 + ∑ n : Fin (N + 1), |C n|
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, fun σ hσ n hn u ↦ ?_⟩
  by_cases hu : u ∈ S
  · let i : Fin (N + 1) := ⟨n, by omega⟩
    calc
      _ ≤ C i := hC i (σ, u) ⟨hσ, hu⟩
      _ ≤ |C i| := le_abs_self _
      _ ≤ ∑ j : Fin (N + 1), |C j| :=
        Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i)
      _ ≤ B := by dsimp [B]; linarith
  · have hz : iteratedFDeriv ℝ n (fun v ↦ H (σ, v)) u = 0 := by
      apply Function.notMem_support.mp
      intro hm
      exact hu (hsupp σ hσ (support_iteratedFDeriv_subset n hm))
    rw [hz, norm_zero]
    exact hB.le

end RealSpace

section ComplexSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

private lemma contDiff_weighted_log (N : ℕ) {f : ℝ → F} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun p : ℝ × ℝ ↦
      (Real.exp (-p.1 * p.2) : ℂ) • f (Real.exp (-p.2))) := by
  have he : ContDiff ℝ N (fun p : ℝ × ℝ ↦ (Real.exp (-p.1 * p.2) : ℂ)) := by
    have hr : ContDiff ℝ N (fun p : ℝ × ℝ ↦ Real.exp (-p.1 * p.2)) := by
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp hr
  exact he.smul (hf.comp (by fun_prop))

private lemma compact_log_support {f : ℝ → F} (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi 0) :
    ∃ S : Set ℝ, IsCompact S ∧ ∀ σ : ℝ,
      tsupport (fun u ↦ (Real.exp (-σ * u) : ℂ) • f (Real.exp (-u))) ⊆ S := by
  let S : Set ℝ := (fun x ↦ -Real.log x) '' tsupport f
  have hS : IsCompact S := hc.image_of_continuousOn
    (Real.continuousOn_log.neg.mono fun x hx ↦ (ne_of_gt (hp hx) : x ≠ 0))
  refine ⟨S, hS, fun σ ↦ closure_minimal ?_ hS.isClosed⟩
  intro u hu
  have hn : f (Real.exp (-u)) ≠ 0 := by
    intro h
    exact hu (by simp [h])
  refine ⟨Real.exp (-u), subset_closure hn, ?_⟩
  simp

end ComplexSpace

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma angular_mellin_bound (f : ℝ → E) (s : ℂ) (N : ℕ) {B : ℝ}
    (hB : (1 + ‖(2 * Real.pi)⁻¹ * s.im‖) ^ N *
      ‖𝓕 (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u)))
        ((2 * Real.pi)⁻¹ * s.im)‖ ≤ B) :
    (1 + |s.im|) ^ N * ‖mellin f s‖ ≤ (2 * Real.pi) ^ N * B := by
  let w : ℝ := (2 * Real.pi)⁻¹ * s.im
  have hw : |s.im| = (2 * Real.pi) * ‖w‖ := by
    dsimp [w]
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hscale : 1 + |s.im| ≤ (2 * Real.pi) * (1 + ‖w‖) := by
    rw [hw]
    nlinarith [Real.two_le_pi]
  simp_rw [mellin_eq_fourier, div_eq_mul_inv, mul_comm s.im, ← Complex.coe_smul]
  calc
    _ ≤ ((2 * Real.pi) * (1 + ‖w‖)) ^ N *
        ‖𝓕 (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u))) w‖ := by
      gcongr
    _ = (2 * Real.pi) ^ N * ((1 + ‖w‖) ^ N *
        ‖𝓕 (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u))) w‖) := by rw [mul_pow]; ring
    _ ≤ (2 * Real.pi) ^ N * B := mul_le_mul_of_nonneg_left hB (by positivity)

end Scaling

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma weighted_log_family_data {N : ℕ} {f : ℝ → E}
    (hf : ContDiff ℝ N f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi 0)
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ S : Set ℝ, IsCompact S ∧ ∃ C > 0,
      (∀ σ : ℝ, tsupport (fun u ↦ (Real.exp (-σ * u) : ℂ) • f (Real.exp (-u))) ⊆ S) ∧
      (∀ σ ∈ K, ∀ n ≤ N, ∀ u,
        ‖iteratedFDeriv ℝ n (fun v ↦ (Real.exp (-σ * v) : ℂ) • f (Real.exp (-v))) u‖ ≤ C) := by
  obtain ⟨S, hS, hsupp⟩ := compact_log_support hc hp
  have hH := contDiff_weighted_log N hf
  obtain ⟨D, hD, hbound⟩ := uniform_slice_bound hH hK hS (fun σ _ ↦ hsupp σ)
  exact ⟨S, hS, D, hD, hsupp, hbound⟩

end Family

section Endpoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Mellin transform of a compactly supported `C^N` function with positive support decays
with order `N` in the imaginary direction, uniformly over any compact set of real parts. -/
theorem exists_one_add_abs_im_pow_mul_norm_mellin_le {N : ℕ} {f : ℝ → E}
    (hf : ContDiff ℝ N f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi 0)
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ K → (1 + |s.im|) ^ N * ‖mellin f s‖ ≤ C := by
  obtain ⟨S, hS, D, hD, hsupp, hbound⟩ := weighted_log_family_data hf hc hp hK
  let C : ℝ := (2 * Real.pi) ^ N * (2 ^ N * (D * volume.real S))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1 + C, add_pos_of_pos_of_nonneg zero_lt_one hC, fun s hs ↦ ?_⟩
  let w : ℝ := (2 * Real.pi)⁻¹ * s.im
  have hg : ContDiff ℝ N (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u))) := by
    have ht : ContDiff ℝ N (fun u : ℝ ↦ (s.re, u)) :=
      contDiff_const.prodMk contDiff_id
    exact (contDiff_weighted_log N hf).comp ht
  have hmeas : MeasurableSet S := hS.measurableSet
  have hfinite : volume S ≠ ⊤ := hS.measure_lt_top.ne
  have hfour : (1 + ‖w‖) ^ N *
      ‖𝓕 (fun u ↦ (Real.exp (-s.re * u) : ℂ) • f (Real.exp (-u))) w‖ ≤
        2 ^ N * (D * volume.real S) :=
    TauCeti.one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset hg hmeas hfinite
      (hsupp s.re) (hbound s.re hs) w
  exact (angular_mellin_bound f s N hfour).trans (by dsimp [C]; linarith)

end Endpoint

end TauCeti
