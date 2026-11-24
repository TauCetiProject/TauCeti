/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.Gronwall.TwoSided

/-!
# Grönwall bounds from interior derivatives

A curve continuous on a closed interval satisfies the exact Grönwall estimate from any
reference point when its derivative satisfies the affine norm bound in the interior.
There is no differentiability requirement at either endpoint, and no completeness or sign
condition on the rate or error. Continuity transports the interior comparison to both endpoints.

## Main results

* `TauCeti.norm_le_gronwallBound_of_norm_deriv_le`: exact bound from any reference time.
* `TauCeti.norm_le_exp_of_affine_deriv_bound`: a convenient exponential bound for nonnegative
  affine coefficients, including initial or terminal reference points.

These estimates apply to spatial coefficient bounds for ancient flows and their pointed limits.

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Set Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Grönwall's exact bound from an arbitrary point of a closed interval. Derivatives are
required only in the interior; continuity suffices at the endpoints. -/
theorem norm_le_gronwallBound_of_norm_deriv_le
    {f f' : ℝ → E} {a b t₀ δ K ε : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hinit : ‖f t₀‖ ≤ δ)
    (hbound : ∀ t ∈ Ioo a b, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ gronwallBound δ K ε |t - t₀| := by
  intro t ht
  by_cases hab : a < b
  · have hinterior (s : ℝ) (hs : s ∈ Ioo a b) (u : ℝ) (hu : u ∈ Ioo a b) :
        ‖f u‖ ≤ gronwallBound ‖f s‖ K ε |u - s| := by
      have hsub : Icc (min s u) (max s u) ⊆ Ioo a b := by
        intro v hv
        exact ⟨(lt_min hs.1 hu.1).trans_le hv.1, hv.2.trans_lt (max_lt hs.2 hu.2)⟩
      exact norm_le_gronwallBound_of_norm_derivWithin_le
        ⟨min_le_left _ _, le_max_left _ _⟩
        (fun v hv ↦ (hf' v (hsub hv)).hasDerivWithinAt) le_rfl
        (fun v hv ↦ hbound v (hsub hv)) u ⟨min_le_right _ _, le_max_right _ _⟩
    have hG : Continuous (fun p : ℝ × ℝ ↦ gronwallBound p.1 K ε p.2) := by
      unfold gronwallBound
      split_ifs <;> fun_prop
    have href (u : ℝ) (hu : u ∈ Ioo a b) :
        ‖f u‖ ≤ gronwallBound ‖f t₀‖ K ε |u - t₀| := by
      have ht₀cl : t₀ ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
      have hright : ContinuousOn (fun s ↦ gronwallBound ‖f s‖ K ε |u - s|) (Icc a b) :=
        hG.comp_continuousOn
          (hf.norm.prodMk (continuous_const.sub continuous_id).abs.continuousOn)
      apply ContinuousWithinAt.closure_le ht₀cl
        continuousWithinAt_const ((hright t₀ ht₀).mono Ioo_subset_Icc_self)
      exact fun s hs ↦ hinterior s hs u hu
    have hend : ‖f t‖ ≤ gronwallBound ‖f t₀‖ K ε |t - t₀| := by
      have htcl : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
      apply ContinuousWithinAt.closure_le htcl
        ((hf t ht).norm.mono Ioo_subset_Icc_self)
        (hG.comp
          (continuous_const.prodMk (continuous_id.sub continuous_const).abs)).continuousWithinAt
      exact href
    apply hend.trans
    unfold gronwallBound
    split_ifs <;> gcongr
  · have htt₀ : t = t₀ := by linarith [ht.1, ht.2, ht₀.1, ht₀.2]
    simpa only [htt₀, sub_self, abs_zero, gronwallBound_x0] using hinit

/-- Nonnegative affine coefficients give a simple exponential bound from any reference point
of a closed interval, assuming differentiability only in the interior. -/
theorem norm_le_exp_of_affine_deriv_bound
    {f : ℝ → E} {a b t₀ C K D : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hinit : ‖f t₀‖ ≤ D)
    (hbound : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ C + K * ‖f t‖) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ max D 1 * exp ((C + K) * |t - t₀|) := by
  have hupper (x : ℝ) (hx : 0 ≤ x) :
      gronwallBound D K C x ≤ max D 1 * exp ((C + K) * x) := by
    have hDC : D ≤ max D 1 := le_max_left _ _
    have h1 : 1 ≤ max D 1 := le_max_right _ _
    have hdecomp : gronwallBound D K C x = D * exp (K * x) + gronwallBound 0 K C x := by
      unfold gronwallBound
      split_ifs with h
      · simp [h]
      · ring
    rw [hdecomp]
    calc
      D * exp (K * x) + gronwallBound 0 K C x ≤ (D + C * x) * exp (K * x) := by
        have h := gronwallBound_zero_le_mul_exp hK hC (x := x)
        nlinarith
      _ ≤ max D 1 * exp (C * x) * exp (K * x) := by
        gcongr
        have hcx : 0 ≤ C * x := mul_nonneg hC hx
        have h := Real.add_one_le_exp (C * x)
        nlinarith
      _ = max D 1 * exp ((C + K) * x) := by rw [mul_assoc, ← exp_add, add_mul]
  intro t ht
  exact (norm_le_gronwallBound_of_norm_deriv_le ht₀ hf
    (fun s hs ↦ (hf' s hs).hasDerivAt) hinit
    (fun s hs ↦ by simpa only [add_comm] using hbound s hs) t ht).trans
      (hupper _ (abs_nonneg _))

end TauCeti
