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
import TauCeti.Analysis.LaplaceTransform.Conj
import TauCeti.Analysis.LaplaceTransform.Window.Coefficients
import TauCeti.Analysis.LaplaceTransform.Window.Moments
import TauCeti.Analysis.Meromorphic.WindowPoleComparison

/-!
# Windowed Landau theorem with an exponential majorant

Under an upper bound in mean on arbitrarily far-out proportional windows, a continued real
Laplace transform is either pole-free to the right of the bound's exponent or has a rightmost
pole that is real with negative leading Laurent coefficient. When all poles are simple and
all real residues are positive, only the pole-free case is possible.

The argument extends the simple-pole case of Levent Alpöge's `Deduction.landau_window`
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

/-- If a continued real Laplace transform has a pole to the right of `θ` despite an upper
bound in mean on arbitrarily far-out proportional windows, there is a real pole in `(θ, A]`
with negative real leading coefficient. No pole lies to its right. The positive part of the
input is assumed to have an almost-everywhere exponential majorant at rate `A`. -/
theorem exists_rightmost_real_pole_of_hasLaplace_window_of_ae_le_exp
    {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ L B : ℝ} (hL : 1 < L)
    (hg : ∀ᵐ u ∂volume.restrict (Ioi 0), max (g u) 0 ≤ B * Real.exp (A * u))
    (hF : MeromorphicOn F {z | θ < z.re})
    (hLap : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z (F z))
    (hwin : ∀ η > 0, ∃ᶠ U in atTop,
      (∫ u in U..(L * U), max (g u) 0 * Real.exp (-θ * u)) ≤ Real.exp (η * U))
    (hp : ∃ ρ : ℂ, θ < ρ.re ∧ meromorphicOrderAt F ρ < 0) :
    ∃ β ∈ Ioc θ A, meromorphicOrderAt F (β : ℂ) < 0 ∧
      (∀ z : ℂ, β < z.re → 0 ≤ meromorphicOrderAt F z) ∧
      ∃ c < (0 : ℝ), meromorphicTrailingCoeffAt F (β : ℂ) = (c : ℂ) := by
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
  obtain ⟨ρ, hρθ, hρ⟩ := hp
  obtain ⟨β, hβ, hβN, hmax, hc⟩ := hN.exists_rightmost_real_pole_of_window_taylor_bound
    hleft ⟨ρ, hρθ, (hord hρθ).trans_lt hρ⟩ fun γ η hη ↦
      (hupper η hη).imp fun _ hC U₀ ↦ (hC U₀).imp fun _ ⟨hU, k, hk, hu⟩ ↦ ⟨hU, k, hk, hu γ⟩
  have hβθ : θ < (β : ℂ).re := by simpa using hβ
  have hβF := (hord hβθ).symm.trans_lt hβN
  have hβA : β ≤ A := le_of_not_gt fun h ↦
    hβF.not_ge (hAn β (by simpa using h)).meromorphicOrderAt_nonneg
  refine ⟨β, ⟨hβ, hβA⟩, hβF, fun z hz ↦ ?_, ?_⟩
  · rw [← hord (hβ.trans hz)]
    exact le_of_not_gt fun hpz ↦ hz.not_ge (hmax z hpz)
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
    (hF.toMeromorphicNFOn_eq_self_on_nhdsNE hβθ)] at hc
  have him := im_meromorphicTrailingCoeffAt_eq_zero_of_hasLaplace hF hLap hβ
  have he : meromorphicTrailingCoeffAt F (β : ℂ) =
      ((meromorphicTrailingCoeffAt F (β : ℂ)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using him)
  refine ⟨_, hc.lt_of_ne ?_, he⟩
  intro hzero
  exact (hF β hβθ).meromorphicTrailingCoeffAt_ne_zero (ne_top_of_lt hβF)
    (he.trans (by rw [hzero, ofReal_zero]))

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
  intro ρ hρθ
  by_contra! hp
  obtain ⟨β, hβ, hpole, _, c, hc, he⟩ :=
    exists_rightmost_real_pole_of_hasLaplace_window_of_ae_le_exp hL hg hF hLap hwin ⟨ρ, hρθ, hp⟩
  have horder := hsimple β (by simpa using hβ.1) hpole
  have hpos := hres β hβ.1 horder
  rw [Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one horder, he, ofReal_re]
    at hpos
  exact hc.not_gt hpos

end TauCeti
