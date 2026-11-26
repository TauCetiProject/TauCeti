/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.Taylor.WindowPoleComparison
import TauCeti.Analysis.LaplaceTransform.WindowCoefficients
import TauCeti.Analysis.LaplaceTransform.WindowMoments
import TauCeti.Analysis.Meromorphic.ExpansionDisc

/-!
# Windowed Landau theorem for simple poles

A one-sided bound in mean on arbitrarily far-out proportional windows excludes poles of a
continued Laplace transform, if all poles are simple and the real ones have positive residue.
The Gamma moment estimate selects one Taylor degree per window, uniformly in the imaginary
part of the expansion centre. An isolated pole forces faster growth at that same degree.

This is the simple-pole argument of Levent Alpöge's `Deduction.landau_window`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Interval Nat Topology

namespace TauCeti

/-- Select a degree on each sufficiently far-out good window at which the sum of the shifted
coefficient norm and the real-centred reflected coefficient has a uniform geometric bound. -/
private theorem exists_window_taylor_bound_of_hasLaplace {g : ℝ → ℝ} {F : ℂ → ℂ}
    {A θ L B : ℝ} (hL : 1 < L)
    (hg : ∀ᵐ u ∂volume.restrict (Ioi 0), max (g u) 0 ≤ B * Real.exp (A * u))
    (hLap : ∀ z : ℂ, max A θ < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z (F z))
    (hwin : ∀ η > 0, ∃ᶠ U in atTop,
      (∫ u in U..(L * U), max (g u) 0 * Real.exp (-θ * u)) ≤ Real.exp (η * U)) :
    ∃ σ > max A θ, ∀ η > 0, ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ,
      U ≤ (k : ℝ) ∧ ∀ γ : ℝ,
        ‖iteratedDeriv k F ((σ : ℂ) + γ * I) / (k ! : ℂ)‖ +
          ((-1) ^ k * (iteratedDeriv k F σ / (k ! : ℂ))).re ≤
            C * Real.exp (η * U) / (σ - θ) ^ k := by
  obtain ⟨σ, hσ, D, _, hmoment⟩ := exists_integral_mul_gammaKernel_le_window A θ hL
  refine ⟨σ, hσ, fun η hη ↦ ⟨2 * (1 + |B * D|), fun U₀ ↦ ?_⟩⟩
  obtain ⟨U, hU, hwinU⟩ := frequently_atTop.mp (hwin η hη) (max U₀ 0)
  have hU₀ : 0 ≤ U := (le_max_right ..).trans hU
  have hUL : U ≤ L * U := le_mul_of_one_le_left hU₀ hL.le
  rw [intervalIntegral.integral_of_le hUL, ← integral_Icc_eq_integral_Ioc] at hwinU
  obtain ⟨k, hk, hm⟩ := hmoment U
  have he : 1 ≤ Real.exp (η * U) := Real.one_le_exp (mul_nonneg hη.le hU₀)
  have hden : 0 < (σ - θ) ^ k := pow_pos (sub_pos.mpr ((le_max_right ..).trans_lt hσ)) _
  have hn {z : ℂ} (hz : z.re = σ) :
      ∀ᶠ w in 𝓝 z, HasLaplace (fun u ↦ (g u : ℂ)) w (F w) := by
    have hz' : z ∈ {w : ℂ | max A θ < w.re} := by simpa [hz] using hσ
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz'] with w hw
    exact hLap w hw
  refine ⟨U, (le_max_left ..).trans hU, k, hk, fun γ ↦ ?_⟩
  have hγ : ((σ : ℂ) + γ * I).re = σ := by simp
  have hc := norm_add_re_laplace_coeff_le (hn hγ) (hn (by simp [hγ])) k
  calc
    _ ≤ 2 * ∫ u in Ioi 0, max (g u) 0 * (u ^ k * Real.exp (-σ * u) / k !) := by
      -- Put the reflected-coefficient scalar `(-1) ^ k / k !` in the factored form of the goal.
      have hsmul (x : ℂ) : ((-1) ^ k / k ! : ℂ) • x = (-1) ^ k * (x / (k ! : ℂ)) := by
        rw [smul_eq_mul]
        ring
      have hnorm (x : ℂ) : ‖((-1) ^ k / k ! : ℂ) • x‖ = ‖x / (k ! : ℂ)‖ := by
        rw [hsmul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      rw [hnorm, hsmul, hγ] at hc
      exact hc
    _ ≤ 2 * ((Real.exp (η * U) + B * D) / (σ - θ) ^ k) := by
      have hm' := hm (fun u ↦ max (g u) 0) (Eventually.of_forall fun _ ↦ le_max_right ..) hg
      simp only [neg_mul] at hwinU
      simpa only [neg_mul] using mul_le_mul_of_nonneg_left (hm'.trans
        (div_le_div_of_nonneg_right (add_le_add_left hwinU _) hden.le)) zero_le_two
    _ ≤ _ := by
      have hBD := (le_abs_self (B * D)).trans (le_mul_of_one_le_right (abs_nonneg _) he)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by nlinarith only [hBD]) hden.le

/-- **Windowed Landau theorem for simple poles.** Suppose `F` is meromorphic on `re z > θ`
and agrees with the Laplace transform of a real function `g` on `re z > A`. Suppose the
positive part of `g` is bounded almost everywhere by `B exp(Au)` on the positive ray. If for each
`η > 0` the weighted positive-part integral on `[U, L * U]` is at most `exp(η U)` at arbitrarily
large `U`, for a fixed `L > 1`, then `F` has no poles in `re z > θ`, provided all poles there are
simple and every real pole there has positive real part of its residue. -/
theorem meromorphicOrderAt_nonneg_of_hasLaplace_window_of_simple_poles
    {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ L B : ℝ} (hL : 1 < L)
    (hg : ∀ᵐ u ∂volume.restrict (Ioi 0), max (g u) 0 ≤ B * Real.exp (A * u))
    (hF : MeromorphicOn F {z | θ < z.re})
    (hLap : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z (F z))
    (hsimple : ∀ z : ℂ, θ < z.re → meromorphicOrderAt F z < 0 → meromorphicOrderAt F z = -1)
    (hres : ∀ β : ℝ, θ < β → meromorphicOrderAt F (β : ℂ) = -1 → 0 < (Contour.residue F β).re)
    (hwin : ∀ η > 0, ∃ᶠ U in atTop,
      (∫ u in U..(L * U), max (g u) 0 * Real.exp (-θ * u)) ≤ Real.exp (η * U)) :
    ∀ ρ : ℂ, θ < ρ.re → 0 ≤ meromorphicOrderAt F ρ := by
  let N := toMeromorphicNFOn F {z | θ < z.re}
  have hN : MeromorphicNFOn N {z | θ < z.re} := meromorphicNFOn_toMeromorphicNFOn ..
  have hord {z : ℂ} (hz : θ < z.re) : meromorphicOrderAt N z = meromorphicOrderAt F z :=
    meromorphicOrderAt_toMeromorphicNFOn hF hz
  have hAn := DifferentiableOn.analyticOnNhd (differentiableOn_of_hasLaplace_re_gt hLap)
    (isOpen_lt continuous_const continuous_re)
  have hLapN (z : ℂ) (hz : max A θ < z.re) : HasLaplace (fun u ↦ (g u : ℂ)) z (N z) := by
    have ha := (le_max_left A θ).trans_lt hz
    have hn : N z = F z := (toMeromorphicNFOn_eq_toMeromorphicNFAt hF
      ((le_max_right A θ).trans_lt hz)).trans
      (congrFun (toMeromorphicNFAt_eq_self.mpr (hAn z ha).meromorphicNFAt) z)
    exact hn.symm ▸ hLap z ha
  obtain ⟨σ, hσ, hupper⟩ := exists_window_taylor_bound_of_hasLaplace hL hg hLapN hwin
  have hleft (z : ℂ) (hz : θ < z.re) (hp : meromorphicOrderAt N z < 0) : z.re < σ := by
    by_contra! h
    rw [hord hz] at hp
    exact hp.not_ge (hAn z (((le_max_left A θ).trans_lt hσ).trans_le h)).meromorphicOrderAt_nonneg
  -- The per-centre form of `hupper`, for the shifted-pole and real-pole branches below.
  have hupperγ (γ : ℝ) : ∀ η > 0, ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ, U ≤ (k : ℝ) ∧
      ‖iteratedDeriv k N ((σ : ℂ) + γ * I) / (k ! : ℂ)‖ +
        ((-1) ^ k * (iteratedDeriv k N σ / (k ! : ℂ))).re ≤ C * Real.exp (η * U) / (σ - θ) ^ k :=
    fun η hη ↦ (hupper η hη).imp fun _ hC U₀ ↦
      (hC U₀).imp fun _ ⟨hU, k, hk, hu⟩ ↦ ⟨hU, k, hk, hu γ⟩
  intro ρ hρθ
  by_contra! hρ
  rcases hN.exists_analytic_discs_or_rightmost_real_pole hleft ⟨ρ, hρθ, (hord hρθ).trans_lt hρ⟩ with
    ⟨γ, p, r, hd, hdr, hr, hpN, hz, hw⟩ | ⟨β, r, hβ, hdist, hdr, hr, hβN, _, hz⟩
  · have hc : ((σ : ℂ) + γ * I).re = σ := by simp
    have hpθ : θ < p.re := ball_subset_setOfPred_lt_re (R := r)
      (by rw [hc]; linarith only [hr]) (by rw [mem_ball, dist_comm]; exact hdr)
    rw [dist_eq_norm] at hd hdr
    have hb := hz.differentiableOn.le_norm_sub_of_window_taylor_bound_of_simple_pole
      hw.differentiableOn (lt_min hdr hdr) (sub_ne_zero.mp (norm_pos_iff.mp hd))
      (by rw [hord hpθ]; exact hsimple p hpθ ((hord hpθ).symm.trans_lt hpN)) (hupperγ γ)
    exact (hdr.trans_le hr).not_ge hb
  · have hβθ : θ < (β : ℂ).re := by simpa using hβ
    have hsimpleβ := hsimple β hβθ ((hord hβθ).symm.trans_lt hβN)
    have hnonpos := hz.differentiableOn.residue_re_nonpos_of_window_taylor_bound
      (sub_pos.mp hdist) (lt_min hdr (hdr.trans_le hr)) ((hord hβθ).trans hsimpleβ).ge
      (fun η hη ↦ (hupperγ 0 η hη).imp fun _ hC U₀ ↦ (hC U₀).imp fun _ ⟨hU, k, hk, hu⟩ ↦
        ⟨hU, k, hk, (le_add_of_nonneg_left (norm_nonneg _)).trans hu⟩)
    rw [Contour.residue_congr_nhdsNE (hF.toMeromorphicNFOn_eq_self_on_nhdsNE hβθ)] at hnonpos
    exact (hres β hβ hsimpleβ).not_ge hnonpos

end TauCeti
