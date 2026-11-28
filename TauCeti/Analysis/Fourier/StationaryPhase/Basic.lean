/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Matrix.DeterminantBound

/-! # Stationary phase for holomorphic phases -/

public section

open Filter Topology
open Metric

namespace TauCeti

private theorem neg_gradient_bound_vanishes {n : ℕ} {x x₀ : Fin n → ℂ} {Λ : ℝ}
    (hΛ : Λ < 0) (D : (Fin n → ℂ) →L[ℂ] ℂ)
    (hgrad : ‖x - x₀‖ ≤ Λ * ‖fun k : Fin n ↦ D (Pi.single k 1)‖) :
    ‖x - x₀‖ = 0 ∧ D = 0 := by
  have hGzero : ‖fun k : Fin n ↦ D (Pi.single k 1)‖ = 0 := by
    by_contra hG
    have hGpos : 0 < ‖fun k : Fin n ↦ D (Pi.single k 1)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hG)
    have hneg : Λ * ‖fun k : Fin n ↦ D (Pi.single k 1)‖ < 0 :=
      mul_neg_of_neg_of_pos hΛ hGpos
    linarith [norm_nonneg (x - x₀), hgrad]
  have hdist : ‖x - x₀‖ = 0 := by
    have h := hgrad
    rw [hGzero, mul_zero] at h
    exact le_antisymm h (norm_nonneg _)
  have hcoords : (fun k : Fin n ↦ D (Pi.single k 1)) = 0 := norm_eq_zero.mp hGzero
  have hcoordzero (k : Fin n) : D (Pi.single k 1) = 0 := by
    have h := congrFun hcoords k
    simpa using h
  have hD : D = 0 := by
    ext y
    have hy : y = ∑ k : Fin n, y k • Pi.single k (1 : ℂ) := by
      ext j
      simp [Pi.single_apply]
    rw [hy, map_sum]
    simp [hcoordzero]
  exact ⟨hdist, hD⟩

/-- A lower bound on the complex gradient transfers to the real part of any rotation
of the phase, with a loss depending only on the modulus of the multiplier. -/
theorem norm_le_mul_norm_fderiv_re_of_norm_le_gradient {n : ℕ}
    {g : (Fin n → ℂ) → ℂ} {x x₀ : Fin n → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hg : DifferentiableAt ℂ g x) {Λ : ℝ}
    (hgrad : ‖x - x₀‖ ≤ Λ * ‖fun k : Fin n ↦ fderiv ℂ g x (Pi.single k 1)‖) :
    ‖x - x₀‖ ≤ (2 * Λ / ‖c‖) *
      ‖fderiv ℝ (fun y ↦ (c * g y).re) x‖ := by
  let D := fderiv ℂ g x
  let A := fderiv ℝ (fun y ↦ (c * g y).re) x
  have hA (v : Fin n → ℂ) : A v = (c * D v).re := by
    have h := ((hg.hasFDerivAt.const_smul c).restrictScalars ℝ)
    rw [show A = _ from (Complex.reCLM.hasFDerivAt.comp x h).fderiv]
    rfl
  have hpos := norm_pos_iff.mpr hc
  have hcoord : ‖fun k : Fin n ↦ D (Pi.single k 1)‖ ≤ 2 * ‖A‖ / ‖c‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    let v : Fin n → ℂ := Pi.single k 1
    have hv : ‖v‖ = 1 := by simp [v, Pi.norm_single]
    have hre : |(c * D v).re| ≤ ‖A‖ := by
      simpa only [← hA, Real.norm_eq_abs, hv, mul_one] using A.le_opNorm v
    have him : |(c * D v).im| ≤ ‖A‖ := by
      have hI : A (Complex.I • v) = -(c * D v).im := by
        rw [hA, map_smul, smul_eq_mul, mul_left_comm, Complex.I_mul_re]
      simpa only [Real.norm_eq_abs, norm_smul, Complex.norm_I, hv, mul_one, hI, abs_neg]
        using A.le_opNorm (Complex.I • v)
    apply (le_div_iff₀ hpos).mpr
    calc
      ‖D v‖ * ‖c‖ = ‖c * D v‖ := by rw [norm_mul, mul_comm]
      _ ≤ |(c * D v).re| + |(c * D v).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 * ‖A‖ := by linarith
  by_cases hΛ : 0 ≤ Λ
  · exact hgrad.trans ((mul_le_mul_of_nonneg_left hcoord hΛ).trans_eq (by ring))
  · obtain ⟨hdist, hD⟩ := neg_gradient_bound_vanishes (lt_of_not_ge hΛ) D hgrad
    have hAzero : A = 0 := by
      ext v
      rw [hA, hD]
      simp
    rw [hdist]
    change 0 ≤ (2 * Λ / ‖c‖) * ‖A‖
    rw [hAzero]
    simp

/-- Cauchy estimates on two concentric balls, with a bound uniform in the analytic function
and in the point of the smaller closed ball. -/
theorem exists_norm_iteratedFDeriv_le_of_analyticOnNhd_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (k : ℕ) {c : E} {r R : ℝ} (h : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → F) (M : ℝ),
      AnalyticOnNhd ℂ f (ball c R) → (∀ y ∈ ball c R, ‖f y‖ ≤ M) →
      ∀ y ∈ closedBall c r, ‖iteratedFDeriv ℂ k f y‖ ≤ C * M := by
  induction k generalizing r R with
  | zero =>
    refine ⟨1, by positivity, fun f M _ hM y hy ↦ ?_⟩
    simpa using hM y (closedBall_subset_ball h hy)
  | succ k ih =>
    let ρ := (r + R) / 2
    have hrρ : r < ρ := by dsimp [ρ]; linarith
    have hρR : ρ < R := by dsimp [ρ]; linarith
    obtain ⟨C, hC, hbound⟩ := ih hρR
    refine ⟨2 * C / (ρ - r), by positivity, fun f M hf hM y hy ↦ ?_⟩
    have hsub : ball y (ρ - r) ⊆ ball c ρ :=
      ball_subset_ball' (by linarith [mem_closedBall.mp hy])
    have ha := hf.iteratedFDeriv_of_isOpen isOpen_ball k
    rw [← norm_fderiv_iteratedFDeriv]
    exact (norm_fderiv_le_of_forall_mem_ball_norm_le
      (ha.differentiableOn.mono (hsub.trans (ball_subset_ball hρR.le))) (sub_pos.mpr hrρ)
      (fun z hz ↦ hbound f M hf hM z (ball_subset_closedBall (hsub hz)))).trans_eq (by ring)

private theorem norm_le_mul_norm_of_hasFDerivAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {x₀ : E} {L : E →L[ℂ] F} {r Λ : ℝ} (hr : 0 < r)
    (hf : HasFDerivAt f L x₀)
    (hbound : ∀ x ∈ closedBall x₀ r, ‖x - x₀‖ ≤ Λ * ‖f x - f x₀‖) (v : E) :
    ‖v‖ ≤ Λ * ‖L v‖ := by
  have hline : HasDerivAt (fun z : ℂ ↦ x₀ + z • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x₀
  have hpath : HasDerivAt (fun z : ℂ ↦ f (x₀ + z • v)) (L v) 0 :=
    hf.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hlimit : Tendsto (fun z : ℂ ↦ z⁻¹ • (f (x₀ + z • v) - f x₀))
      (𝓝[≠] 0) (𝓝 (L v)) := by
    simpa only [zero_add, zero_smul, add_zero] using hpath.tendsto_slope_zero
  apply ge_of_tendsto (tendsto_const_nhds.mul hlimit.norm)
  have hc : Tendsto (fun z : ℂ ↦ x₀ + z • v) (𝓝[≠] 0) (𝓝 x₀) := by
    simpa only [zero_smul, add_zero] using
      hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hc.eventually (closedBall_mem_nhds x₀ hr), self_mem_nhdsWithin] with z hz hne
  have hb := hbound (x₀ + z • v) hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr (Set.mem_compl_singleton_iff.mp hne)
  rw [add_sub_cancel_left, norm_smul] at hb
  rw [norm_smul, norm_inv, ← div_eq_inv_mul, ← mul_div_assoc, le_div_iff₀ hpos, mul_comm ‖v‖]
  exact hb

private theorem det_ne_zero_and_norm_inv_le_of_norm_lower {n : ℕ}
    (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) {Λ : ℝ}
    (hlower : ∀ v, ‖v‖ ≤ Λ * ‖L v‖) :
    LinearMap.det L.toLinearMap ≠ 0 ∧ ‖(LinearMap.det L.toLinearMap)⁻¹‖ ≤ n.factorial * Λ ^ n := by
  have hinj : Function.Injective L.toLinearMap := LinearMap.ker_eq_bot.mp (by
    apply LinearMap.ker_eq_bot'.2
    intro v hv
    change L v = 0 at hv
    simpa [hv] using hlower v)
  let e := LinearEquiv.ofInjectiveEndo L.toLinearMap hinj
  have he (v : Fin n → ℂ) : ‖e.symm v‖ ≤ Λ * ‖v‖ := by
    simpa [show L (e.symm v) = v from e.apply_symm_apply v] using hlower (e.symm v)
  have hb (i j : Fin n) : ‖LinearMap.toMatrix' e.symm.toLinearMap i j‖ ≤ Λ := by
    rw [LinearMap.toMatrix'_apply]
    exact (norm_le_pi_norm _ _).trans (by simpa [Pi.norm_single] using he (Pi.single j 1))
  have hdet := Matrix.norm_det_le_factorial_prod _ hb
  rw [LinearMap.det_toMatrix'] at hdet
  have hmul := e.det_mul_det_symm
  change LinearMap.det L.toLinearMap * LinearMap.det e.symm.toLinearMap = 1 at hmul
  have hne : LinearMap.det L.toLinearMap ≠ 0 := by
    intro hz
    simp [hz] at hmul
  have hsymm : LinearMap.det e.symm.toLinearMap = (LinearMap.det L.toLinearMap)⁻¹ := by
    apply (mul_left_cancel₀ hne)
    rw [hmul, mul_inv_cancel₀ hne]
  exact ⟨hne, by simpa [hsymm] using hdet⟩

/-- A linear lower bound on the complex gradient at a critical point makes the Hessian
nondegenerate and bounds the reciprocal of its determinant. -/
theorem det_hessian_ne_zero_and_norm_inv_le_of_norm_le_gradient {n : ℕ} {x₀ : Fin n → ℂ}
    {g : (Fin n → ℂ) → ℂ} {r Λ : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball x₀ (2 * r))) (hcrit : fderiv ℂ g x₀ = 0)
    (hbound : ∀ x ∈ closedBall x₀ r,
      ‖x - x₀‖ ≤ Λ * ‖fun k : Fin n ↦ fderiv ℂ g x (Pi.single k 1)‖) :
    let H := Matrix.of fun i j : Fin n ↦
      iteratedFDeriv ℂ 2 g x₀ ![Pi.single i 1, Pi.single j 1]
    H.det ≠ 0 ∧ ‖H.det⁻¹‖ ≤ n.factorial * Λ ^ n := by
  let grad (x : Fin n → ℂ) (i : Fin n) := fderiv ℂ g x (Pi.single i 1)
  let D := fderiv ℂ (fderiv ℂ g) x₀
  let L := ContinuousLinearMap.pi fun i : Fin n ↦
    (ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp D
  have hD : HasFDerivAt (fderiv ℂ g) D x₀ := by
    apply DifferentiableAt.hasFDerivAt
    exact (hg.analyticOnNhd_of_finiteDimensional isOpen_ball _
      (mem_ball_self (by positivity))).fderiv.differentiableAt
  have hgrad : HasFDerivAt grad L x₀ := by
    apply hasFDerivAt_pi.2
    intro i
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).hasFDerivAt.comp x₀ hD
  have hz : grad x₀ = 0 := by
    ext i
    simp [grad, hcrit]
  have hlower := norm_le_mul_norm_of_hasFDerivAt hr hgrad (by simpa [hz] using hbound)
  have hmat : (Matrix.of fun i j : Fin n ↦
      iteratedFDeriv ℂ 2 g x₀ ![Pi.single i 1, Pi.single j 1]) =
      (LinearMap.toMatrix' L.toLinearMap).transpose := by
    ext i j
    simp [L, D, LinearMap.toMatrix'_apply, iteratedFDeriv_two_apply]
  dsimp only
  rw [hmat, Matrix.det_transpose, LinearMap.det_toMatrix']
  exact det_ne_zero_and_norm_inv_le_of_norm_lower L hlower

end TauCeti
