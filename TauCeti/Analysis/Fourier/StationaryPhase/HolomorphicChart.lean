/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.StationaryPhase.Basic

import TauCeti.Analysis.Calculus.ApproximatesLinearOn.Basic
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! # A uniform inverse chart for bounded holomorphic maps -/

public section

open Metric Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [Nontrivial E]

/-- A bounded holomorphic map fixing zero with identity derivative admits an inverse chart on
balls whose radii are independent of the map. -/
theorem exists_bounded_analytic_inverse_chart {R : ℝ} (hR : 0 < R) (M : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      ∀ (f : E → E), AnalyticOnNhd ℂ f (ball 0 R) → (∀ x ∈ ball 0 R, ‖f x‖ ≤ M) →
        f 0 = 0 → fderiv ℂ f 0 = ContinuousLinearMap.id ℂ E →
        ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧ e.source = ball 0 ρ ∧
          ball 0 (ρ / 4) ⊆ e.target ∧ AnalyticOnNhd ℂ e.symm (ball 0 (ρ / 4)) ∧
          (∀ x ∈ ball 0 (ρ / 4), ‖e.symm x‖ ≤ ρ) ∧
          (∀ x ∈ ball 0 ρ, ‖f x‖ ≤ 3 / 2 * ‖x‖) ∧
          fderiv ℂ e.symm 0 = ContinuousLinearMap.id ℂ E := by
  let I := ContinuousLinearEquiv.refl ℂ E
  obtain ⟨C, -, hCauchy⟩ :=
    exists_norm_iteratedFDeriv_le_of_analyticOnNhd_ball (E := E) (F := E) 2
      (c := 0) (show R / 2 < R by linarith)
  let D := max 1 (C * M)
  have hD : 1 ≤ D := le_max_left ..
  have hDp : 0 < D := zero_lt_one.trans_le hD
  let ρ := min (R / 2) (1 / (2 * D))
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρR : ρ < R := (min_le_left ..).trans_lt (by linarith)
  refine ⟨ρ, hρ, hρR, fun f hf hM h0 h1 ↦ ?_⟩
  have hsub : ball (0 : E) ρ ⊆ ball 0 R := ball_subset_ball hρR.le
  have hclose (x : E) (hx : x ∈ ball 0 ρ) :
      ‖fderiv ℂ f x - ContinuousLinearMap.id ℂ E‖ ≤ 1 / 2 := by
    rw [← h1]
    calc
      _ ≤ D * ‖x - 0‖ :=
        (convex_ball (0 : E) ρ).norm_image_sub_le_of_norm_fderiv_le
          (fun z hz ↦ (hf z (hsub hz)).fderiv.differentiableAt)
          (fun z hz ↦ by
            simpa only [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] using
              (hCauchy f M hf hM z
                (ball_subset_closedBall (ball_subset_ball (min_le_left ..) hz))).trans
                (le_max_right 1 (C * M))) (mem_ball_self hρ) hx
      _ ≤ 1 / 2 := by
        have hn : ‖x - 0‖ ≤ 1 / (2 * D) := by
          rw [← dist_eq_norm]
          exact (mem_ball.1 hx).le.trans (min_le_right ..)
        calc
          _ ≤ D * (1 / (2 * D)) := mul_le_mul_of_nonneg_left hn hDp.le
          _ = _ := by field_simp
  have happ : ApproximatesLinearOn f (I : E →L[ℂ] E) (ball 0 ρ) (1 / 2) :=
    (convex_ball _ _).approximatesLinearOn_of_nnnorm_fderiv_sub_le
      (fun x hx ↦ (hf x (hsub hx)).differentiableAt)
      (fun x hx ↦ by exact_mod_cast hclose x hx)
  have hI : ‖(I.symm : E →L[ℂ] E)‖₊ = 1 := by
    change ‖ContinuousLinearMap.id ℂ E‖₊ = 1
    rw [ContinuousLinearMap.nnNorm_id]
  have hc : Subsingleton E ∨ (1 / 2 : NNReal) < ‖(I.symm : E →L[ℂ] E)‖₊⁻¹ :=
    Or.inr (by rw [hI]; norm_num)
  let e := happ.toOpenPartialHomeomorph f (ball 0 ρ) hc isOpen_ball
  have htarget : ball 0 (ρ / 4) ⊆ e.target := by
    have ha := happ.closedBall_subset_target hc isOpen_ball (b := 0)
      (show 0 ≤ ρ / 2 by positivity) (closedBall_subset_ball (by linarith))
    rw [h0, hI] at ha
    refine (ball_subset_closedBall.trans (closedBall_subset_closedBall ?_)).trans ha
    push_cast
    ring_nf
    norm_num
  have he0 : e 0 = 0 := h0
  have hsource0 : 0 ∈ e.source := mem_ball_self hρ
  have hes0 : e.symm 0 = 0 := by
    simpa only [he0] using e.left_inv hsource0
  refine ⟨e, rfl, rfl, htarget, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hmem : e.symm x ∈ ball 0 ρ := e.map_target (htarget hx)
    obtain ⟨L, hL⟩ := ContinuousLinearMap.isInvertible_of_norm_sub_le_half I
      (A := fderiv ℂ f (e.symm x)) (by
        rw [hI, inv_one]
        change ‖fderiv ℂ f (e.symm x) - ContinuousLinearMap.id ℂ E‖₊ ≤ 1 / 2
        exact_mod_cast hclose _ hmem)
    exact e.analyticAt_symm (htarget hx) (hf _ (hsub hmem)) hL.symm
  · intro x hx
    exact (mem_ball_zero_iff.1 (e.map_target (htarget hx))).le
  · intro x hx
    have h := happ x hx 0 (mem_ball_self hρ)
    simp only [h0, sub_zero, ContinuousLinearEquiv.coe_coe, I, ContinuousLinearEquiv.refl_apply,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h
    calc
      ‖f x‖ = ‖(f x - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · have hf0 := (hf 0 (mem_ball_self hR)).hasStrictFDerivAt
    have ht0 := htarget (mem_ball_self (show 0 < ρ / 4 by positivity))
    rw [h1] at hf0
    have h := e.hasStrictFDerivAt_symm ht0 (f' := I) (by rwa [hes0])
    exact h.hasFDerivAt.fderiv

end TauCeti
