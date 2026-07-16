/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Contour.CrossingMonotonicity
import TauCeti.Analysis.Contour.CrossingWindows
import TauCeti.Analysis.Contour.ExitTime

/-!
# Window splitting of the truncated integral at a crossing

At a transverse crossing `γ t₀ = s` — non-zero one-sided derivative limits, unique crossing on
the window `[t₀ - r, t₀ + r]` — there are exit-time functions `τL, τR` converging to `t₀` from
each side with exit radius exactly `ε`, such that for every integrand `g` with integrable
`ε`-truncation the truncated integral over the window eventually splits into the two *plain*
side integrals:

  `∫ (t₀-r)..(t₀+r), truncated = ∫ (t₀-r)..(τL ε), g (γ u) γ'(u) + ∫ (τR ε)..(t₀+r), g (γ u) γ'(u)`.

The middle piece `[τL ε, τR ε]` is annihilated — there the curve is inside the `ε`-ball, by
strict monotonicity of the distance profile up to the exit times — and on the side pieces the
truncation is inactive, by monotonicity inside the monotone radius and the positive window
distance bound beyond it.

The truncated integrand `if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0` is the integrand of
`Contour.HasCauchyPVAt`, so this is the per-window skeleton of the principal-value evaluation:
consumers add the per-side fundamental-theorem evaluation and the limit of the exit-time terms.

## Main results

* `Contour.exists_exit_times_truncated_integral_split` — the shared window-splitting core.

## Provenance

Migrated from `perCrossing_window_splitting` of `LocalCutoffs.lean` in the AINTLIB
`LeanModularForms` development, restated for a raw curve with the analytic inputs (one-sided
derivative limits, eventual differentiability, continuity on the window) as hypotheses in place
of the bundled `ClosedPwC1Immersion`, and the integrability hypothesis quantified over the
window rather than `[0, 1]`. See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers
and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- The truncated integral vanishes on an interval where the curve stays within radius `ε`. -/
private theorem integral_truncated_eq_zero {γ : ℝ → ℂ} {g : ℂ → ℂ} {s : ℂ} {l u ε : ℝ}
    (hlu : l ≤ u) (h_le : ∀ t ∈ Ioc l u, ‖γ t - s‖ ≤ ε) :
    ∫ t in l..u, (if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0) = 0 := by
  calc ∫ t in l..u, (if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
      = ∫ _ in l..u, (0 : ℂ) := by
        refine intervalIntegral.integral_congr_ae ?_
        rw [uIoc_of_le hlu]
        filter_upwards with t ht
        rw [if_neg (not_lt.mpr (h_le t ht))]
    _ = 0 := by simp

/-- The truncated integral is the plain integral on an interval where the curve stays at
distance `> ε` almost everywhere. -/
private theorem integral_truncated_eq_of_ae_gt {γ : ℝ → ℂ} {g : ℂ → ℂ} {s : ℂ} {l u ε : ℝ}
    (hlu : l ≤ u) (h_gt : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ioc l u → ε < ‖γ t - s‖) :
    ∫ t in l..u, (if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0) =
      ∫ t in l..u, g (γ t) * deriv γ t := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le hlu]
  filter_upwards [h_gt] with t ht htm
  rw [if_pos (ht htm)]

/-- **The monotone exit substrate at a transverse crossing**: a radius `ρ ≤ r` on whose
one-sided windows the distance profile is strictly monotone and the curve leaves the crossed
point. -/
private theorem exists_monotone_leave_radius {γ : ℝ → ℂ} {s : ℂ} {t₀ r : ℝ}
    {L_R L_L : ℂ} (hr_pos : 0 < r) (h_at : γ t₀ = s)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - r) (t₀ + r)))
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (h_diff_R : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (h_diff_L : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∃ ρ > 0, ρ ≤ r ∧
      StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + ρ)) ∧
      StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - ρ) t₀) ∧
      (∀ t ∈ Ioc t₀ (t₀ + ρ), γ t ≠ s) ∧
      (∀ t ∈ Ico (t₀ - ρ) t₀, γ t ≠ s) := by
  have hγ_at : ContinuousAt γ t₀ :=
    hγ_cont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  obtain ⟨r_R, hr_R_pos, hmono_raw⟩ :=
    exists_strictMonoOn_norm_sub_right h_at hL_R h_tendsto_R hγ_at h_diff_R
  obtain ⟨r_L, hr_L_pos, hanti_raw⟩ :=
    exists_strictAntiOn_norm_sub_left h_at hL_L h_tendsto_L hγ_at h_diff_L
  set ρ : ℝ := min r (min r_R r_L) with hρ_def
  have hρ_pos : 0 < ρ := lt_min hr_pos (lt_min hr_R_pos hr_L_pos)
  have hρ_R : ρ ≤ r_R := (min_le_right _ _).trans (min_le_left _ _)
  have hρ_L : ρ ≤ r_L := (min_le_right _ _).trans (min_le_right _ _)
  have hmono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + ρ)) :=
    hmono_raw.mono (Icc_subset_Icc le_rfl (by linarith))
  have hanti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - ρ) t₀) :=
    hanti_raw.mono (Icc_subset_Icc (by linarith) le_rfl)
  refine ⟨ρ, hρ_pos, min_le_left _ _, hmono, hanti, ?_, ?_⟩
  · intro t ht heq
    have h_strict : ‖γ t₀ - s‖ < ‖γ t - s‖ :=
      hmono ⟨le_rfl, by linarith [ht.1]⟩ ⟨ht.1.le, ht.2⟩ ht.1
    rw [h_at, heq, sub_self, norm_zero] at h_strict
    exact absurd h_strict (lt_irrefl 0)
  · intro t ht heq
    have h_strict : ‖γ t₀ - s‖ < ‖γ t - s‖ :=
      hanti ⟨ht.1, ht.2.le⟩ ⟨by linarith [ht.2], le_rfl⟩ ht.2
    rw [h_at, heq, sub_self, norm_zero] at h_strict
    exact absurd h_strict (lt_irrefl 0)

/-- **Shared window-splitting core.** At a transverse crossing `γ t₀ = s` (non-zero one-sided
derivative limits `L_R`, `L_L`, unique crossing on the window `[t₀ - r, t₀ + r]`), there are
exit-time functions `τL, τR` tending to `t₀` one-sidedly with exit radius exactly `ε`, such
that for every integrand `g` with interval-integrable `ε`-truncations on the window, the
truncated integral over the window eventually equals the sum of the two plain side integrals
up to the exit times. -/
theorem exists_exit_times_truncated_integral_split {γ : ℝ → ℂ} {s : ℂ} {t₀ r : ℝ}
    {L_R L_L : ℂ} (hr_pos : 0 < r) (h_at : γ t₀ = s)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - r) (t₀ + r)))
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (h_diff_R : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (h_diff_L : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (h_unique : ∀ t ∈ Icc (t₀ - r) (t₀ + r), γ t = s → t = t₀)
    (g : ℂ → ℂ)
    (h_int : ∀ ε : ℝ, 0 < ε → ∀ a b : ℝ, t₀ - r ≤ a → a ≤ b → b ≤ t₀ + r →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume a b) :
    ∃ τL τR : ℝ → ℝ,
      Tendsto τL (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) ∧
      Tendsto τR (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (τL ε) - s‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (τR ε) - s‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), τL ε ∈ Ioo (t₀ - r) t₀) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), τR ε ∈ Ioo t₀ (t₀ + r)) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫ u in (t₀ - r)..(t₀ + r),
            (if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) =
          (∫ u in (t₀ - r)..(τL ε), g (γ u) * deriv γ u) +
          (∫ u in (τR ε)..(t₀ + r), g (γ u) * deriv γ u)) := by
  classical
  obtain ⟨ρ, hρ_pos, hρ_le_r, hmono, hanti, h_leave_R, h_leave_L⟩ :=
    exists_monotone_leave_radius hr_pos h_at hγ_cont hL_R hL_L h_tendsto_R h_tendsto_L
      h_diff_R h_diff_L
  have hγ_cont_R : ContinuousOn γ (Icc t₀ (t₀ + ρ)) :=
    hγ_cont.mono (Icc_subset_Icc (by linarith) (by linarith))
  have hγ_cont_L : ContinuousOn γ (Icc (t₀ - ρ) t₀) :=
    hγ_cont.mono (Icc_subset_Icc (by linarith) (by linarith))
  set τL := firstExitTimeLeft γ t₀ ρ s with hτL_def
  set τR := firstExitTimeRight γ t₀ ρ s with hτR_def
  have h_toL : Tendsto τL (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) :=
    firstExitTimeLeft_tendsto hρ_pos hγ_cont_L h_at h_leave_L
  have h_toR : Tendsto τR (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) :=
    firstExitTimeRight_tendsto hρ_pos hγ_cont_R h_at h_leave_R
  have h_radL : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (τL ε) - s‖ = ε :=
    eventually_norm_at_firstExitTimeLeft_eq hρ_pos hγ_cont_L h_at h_leave_L
  have h_radR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (τR ε) - s‖ = ε :=
    eventually_norm_at_firstExitTimeRight_eq hρ_pos hγ_cont_R h_at h_leave_R
  have h_memL : ∀ᶠ ε in 𝓝[>] (0 : ℝ), τL ε ∈ Ioo (t₀ - ρ) t₀ :=
    h_toL (Ioo_mem_nhdsLT (by linarith))
  have h_memR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), τR ε ∈ Ioo t₀ (t₀ + ρ) :=
    h_toR (Ioo_mem_nhdsGT (by linarith))
  refine ⟨τL, τR, h_toL, h_toR, h_radL, h_radR,
    h_memL.mono fun ε hε => ⟨by linarith [hε.1], hε.2⟩,
    h_memR.mono fun ε hε => ⟨hε.1, by linarith [hε.2]⟩, ?_⟩
  obtain ⟨m, hm_pos, h_far_L, h_far_R⟩ :=
    exists_window_dist_lower_bound hγ_cont h_unique hρ_pos hρ_le_r
  filter_upwards [h_radL, h_radR, h_memL, h_memR, Ioo_mem_nhdsGT hm_pos]
    with ε hεL hεR hτL hτR hεm
  have hε_pos : 0 < ε := hεm.1
  have h_lb : t₀ - r ≤ τL ε := by linarith [hτL.1]
  have h_mid_le : τL ε ≤ τR ε := by linarith [hτL.2, hτR.1]
  have h_ub : τR ε ≤ t₀ + r := by linarith [hτR.2]
  have h_mid_zero : ∫ u in (τL ε)..(τR ε),
      (if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) = 0 := by
    refine integral_truncated_eq_zero h_mid_le fun u hu => ?_
    rcases lt_trichotomy u t₀ with h_lt | h_eq | h_ge
    · have h_bd : ‖γ u - s‖ ≤ ‖γ (τL ε) - s‖ := by
        rcases eq_or_lt_of_le hu.1.le with h_eq' | h_lt'
        · rw [h_eq']
        · exact (hanti ⟨hτL.1.le, hτL.2.le⟩ ⟨by linarith [hτL.1], h_lt.le⟩ h_lt').le
      rwa [hεL] at h_bd
    · rw [h_eq, h_at, sub_self, norm_zero]
      exact hε_pos.le
    · have h_bd : ‖γ u - s‖ ≤ ‖γ (τR ε) - s‖ := by
        rcases eq_or_lt_of_le hu.2 with h_eq' | h_lt'
        · rw [h_eq']
        · exact (hmono ⟨h_ge.le, by linarith [hτR.2, hu.2]⟩ ⟨hτR.1.le, hτR.2.le⟩ h_lt').le
      rwa [hεR] at h_bd
  have h_left_eq : ∫ u in (t₀ - r)..(τL ε),
      (if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) =
      ∫ u in (t₀ - r)..(τL ε), g (γ u) * deriv γ u := by
    refine integral_truncated_eq_of_ae_gt h_lb ?_
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      (MeasureTheory.measure_singleton (τL ε))] with u hu_ne hu
    have h_u_lt : u < τL ε := lt_of_le_of_ne hu.2 hu_ne
    rcases lt_or_ge u (t₀ - ρ) with h_lt | h_ge
    · exact lt_of_lt_of_le hεm.2 (h_far_L u ⟨hu.1.le, h_lt.le⟩)
    · have h_bd : ‖γ (τL ε) - s‖ < ‖γ u - s‖ :=
        hanti ⟨h_ge, by linarith [hτL.2, h_u_lt]⟩ ⟨hτL.1.le, hτL.2.le⟩ h_u_lt
      rwa [hεL] at h_bd
  have h_right_eq : ∫ u in (τR ε)..(t₀ + r),
      (if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) =
      ∫ u in (τR ε)..(t₀ + r), g (γ u) * deriv γ u := by
    refine integral_truncated_eq_of_ae_gt h_ub (Eventually.of_forall fun u hu => ?_)
    rcases le_or_gt u (t₀ + ρ) with h_le | h_gt
    · have h_bd : ‖γ (τR ε) - s‖ < ‖γ u - s‖ :=
        hmono ⟨hτR.1.le, hτR.2.le⟩ ⟨by linarith [hτR.1, hu.1], h_le⟩ hu.1
      rwa [hεR] at h_bd
    · exact lt_of_lt_of_le hεm.2 (h_far_R u ⟨h_gt.le, hu.2⟩)
  have h_int_left := h_int ε hε_pos (t₀ - r) (τL ε) le_rfl h_lb (by linarith [hτL.2])
  have h_int_mid := h_int ε hε_pos (τL ε) (τR ε) h_lb h_mid_le h_ub
  have h_int_right := h_int ε hε_pos (τR ε) (t₀ + r) (h_lb.trans h_mid_le) h_ub le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (h_int_left.trans h_int_mid) h_int_right,
    ← intervalIntegral.integral_add_adjacent_intervals h_int_left h_int_mid,
    h_mid_zero, add_zero, h_left_eq, h_right_eq]

end TauCeti.Contour

end
