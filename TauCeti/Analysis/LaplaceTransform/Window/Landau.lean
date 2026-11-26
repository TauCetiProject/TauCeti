/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.LaplaceTransform.Conj
import TauCeti.Analysis.LaplaceTransform.GammaKernel
import TauCeti.Analysis.LaplaceTransform.Window.IntegrableWeight
import TauCeti.Analysis.Meromorphic.WindowPoleComparison
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Windowed Landau theorem with absolute convergence

For the meromorphic continuation of a real Laplace transform, bounds on the positive-part
integral on arbitrarily far-out proportional windows imply that if there are poles, one of
maximal real part is real and has a strictly negative leading Laurent coefficient. Absolute
convergence on an initial half-plane suffices; no pointwise growth bound or simplicity of poles
is needed.

The coefficient comparison follows the method of Levent Alpöge's `Deduction.landau_window`
(<https://github.com/leanprover-community/riemann-hypothesis>), using an integrable exponential
weight off the windows.
-/

public section

open Complex Filter MeasureTheory Set
open scoped Interval Nat Real

namespace TauCeti

-- The Gamma-tail profile is strictly smaller than one. Thus moving the expansion line
-- sufficiently far right beats any fixed gap between the baseline and window exponents.
private theorem exists_window_expansion_rate (a θ L : ℝ) (hL : 1 < L) :
    ∃ σ > max a θ, 1 ≤ (σ - a) * √L ∧
      max ((√L)⁻¹ * Real.exp (1 - (√L)⁻¹)) (√(√L) * Real.exp (1 - √(√L))) *
        (σ - θ) ≤ σ - a := by
  let q := max ((√L)⁻¹ * Real.exp (1 - (√L)⁻¹)) (√(√L) * Real.exp (1 - √(√L)))
  have hsqrt : 1 < √L := by simpa using Real.sqrt_lt_sqrt zero_le_one hL
  have hfourth : 1 < √(√L) := by simpa using Real.sqrt_lt_sqrt zero_le_one hsqrt
  have hq : q < 1 := max_lt
    (mul_exp_one_sub_lt_one (inv_lt_one_of_one_lt₀ hsqrt).ne)
    (mul_exp_one_sub_lt_one hfourth.ne')
  obtain ⟨σ, hσ⟩ := exists_gt (max (max (a + 1) θ) ((a - q * θ) / (1 - q)))
  have ha : a + 1 < σ := (le_max_left ..).trans_lt ((le_max_left ..).trans_lt hσ)
  have hθ : θ < σ := (le_max_right ..).trans_lt ((le_max_left ..).trans_lt hσ)
  have hrate := (div_lt_iff₀ (sub_pos.mpr hq)).mp ((le_max_right ..).trans_lt hσ)
  refine ⟨σ, max_lt (by linarith) hθ,
    one_le_mul_of_one_le_of_one_le (by linarith) hsqrt.le, ?_⟩
  linarith only [hrate]

private theorem exists_window_taylor_bound_of_integrableOn {g : ℝ → ℝ} {F : ℂ → ℂ}
    {A θ L : ℝ} (hL : 1 < L)
    (hLap : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z (F z))
    (hwin : ∀ η > 0, ∃ᶠ U in atTop,
      (∫ u in U..(L * U), max (g u) 0 * Real.exp (-θ * u)) ≤ Real.exp (η * U)) :
    ∃ σ > max A θ, ∀ (γ η : ℝ), 0 < η → ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ,
      U ≤ (k : ℝ) ∧
        ‖iteratedDeriv k F ((σ : ℂ) + γ * I) / (k ! : ℂ)‖ +
          ((-1) ^ k * (iteratedDeriv k F σ / (k ! : ℂ))).re ≤
          C * Real.exp (η * U) / (σ - θ) ^ k := by
  -- Take the absolute moment at a rate strictly inside the half-plane of convergence.
  let a := A + 1
  have hAa : A < a := lt_add_one A
  have ha : IntegrableOn (fun u ↦ g u * Real.exp (-(a * u))) (Ioi 0) := by
    simpa only [IntegrableOn, smul_eq_mul, ← ofReal_mul, ← ofReal_neg, ← ofReal_exp, ofReal_re,
      Complex.reCLM_apply, neg_mul, mul_comm (Real.exp _)] using
      Complex.reCLM.integrable_comp (hLap (a : ℂ) (by simpa using hAa)).integrable
  obtain ⟨σ, hσ, hrate, hq⟩ := exists_window_expansion_rate a θ L hL
  let D := ∫ u in Ioi 0, |g u| * Real.exp (-(a * u))
  let T := ((σ - a) * √L * (√(√L) - 1))⁻¹
  have hσθ := (le_max_right a θ).trans_lt hσ
  refine ⟨σ, (max_le_max_right θ hAa.le).trans_lt hσ, fun γ η hη ↦ ⟨2 * (1 + |D|), fun U₀ ↦ ?_⟩⟩
  obtain ⟨U, hU, hgood⟩ := frequently_atTop.mp (hwin η hη) (max (max U₀ 0) T)
  have hU₀ : 0 ≤ U := (le_max_right U₀ 0).trans ((le_max_left ..).trans hU)
  have hUT : T ≤ U := (le_max_right ..).trans hU
  have hUL : U ≤ L * U := le_mul_of_one_le_left hU₀ hL.le
  have hk := (pow_mul_exp_neg_mul_div_factorial_le_off_window hL hrate hUT).2.2.1
  have hcoeff := norm_add_re_laplace_coeff_le_window_of_integrableOn
    (fun z hz ↦ hLap z (hAa.trans hz)) ha hL hrate hσθ hq hUT γ
  let k := ⌈(σ - a) * √L * U⌉₊
  have hscalar (k : ℕ) (z : ℂ) : ((-1) ^ k / k ! : ℂ) • z = (-1) ^ k * (z / (k ! : ℂ)) := by
    simp only [smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc]
  simp only [hscalar, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hcoeff
  refine ⟨U, (le_max_left ..).trans ((le_max_left ..).trans hU), k, hk, hcoeff.trans ?_⟩
  rw [intervalIntegral.integral_of_le hUL, ← integral_Icc_eq_integral_Ioc] at hgood
  have he : 1 ≤ Real.exp (η * U) := Real.one_le_exp (mul_nonneg hη.le hU₀)
  have hD : D ≤ |D| * Real.exp (η * U) := (le_abs_self D).trans (le_mul_of_one_le_right
    (abs_nonneg D) he)
  have hsum : (∫ u in Icc U (L * U), max (g u) 0 * Real.exp (-(θ * u))) + D ≤
      (1 + |D|) * Real.exp (η * U) := by
    rw [add_mul, one_mul]
    simpa only [neg_mul] using add_le_add hgood hD
  calc
    _ ≤ 2 * ((σ - θ) ^ k)⁻¹ * ((1 + |D|) * Real.exp (η * U)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- **Windowed Landau theorem.** Suppose `F` is meromorphic on `Re z > θ` and is the
one-sided Laplace transform of a real function `g` on `Re z > A`. Suppose that for every `η > 0`
the integral of `max (g u) 0 * exp (-θ * u)` on `[U, L * U]` is at most `exp (η * U)` for
arbitrarily large `U`, with a fixed `L > 1`. Then either `F` has no pole in `Re z > θ`, or a
real pole `β ∈ (θ, A]` has real part at least that of every pole in the half-plane and has
strictly negative real leading Laurent coefficient. -/
theorem meromorphicOrderAt_nonneg_or_exists_rightmost_real_pole_of_hasLaplace_window
    {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ L : ℝ} (hL : 1 < L)
    (hF : MeromorphicOn F {z | θ < z.re})
    (hLap : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z (F z))
    (hwin : ∀ η > 0, ∃ᶠ U in atTop,
      (∫ u in U..(L * U), max (g u) 0 * Real.exp (-θ * u)) ≤ Real.exp (η * U)) :
    (∀ z : ℂ, θ < z.re → 0 ≤ meromorphicOrderAt F z) ∨
      ∃ β ∈ Ioc θ A, meromorphicOrderAt F (β : ℂ) < 0 ∧
        (∀ z : ℂ, θ < z.re → meromorphicOrderAt F z < 0 → z.re ≤ β) ∧
        (meromorphicTrailingCoeffAt F (β : ℂ)).re < 0 ∧
        (meromorphicTrailingCoeffAt F (β : ℂ)).im = 0 := by
  by_cases hp : ∃ z : ℂ, θ < z.re ∧ meromorphicOrderAt F z < 0
  · let N := toMeromorphicNFOn F {z | θ < z.re}
    have hAn := (differentiableOn_of_hasLaplace_re_gt hLap).analyticOnNhd
      (isOpen_lt continuous_const continuous_re)
    have hLapN (z : ℂ) (hz : max A θ < z.re) : HasLaplace (fun u ↦ (g u : ℂ)) z (N z) := by
      have hzA := (le_max_left A θ).trans_lt hz
      have he := toMeromorphicNFOn_eq_toMeromorphicNFAt hF ((le_max_right A θ).trans_lt hz)
      rw [toMeromorphicNFAt_eq_self.mpr (hAn z hzA).meromorphicNFAt] at he
      dsimp only [N]
      rw [he]
      exact hLap z hzA
    obtain ⟨σ, hσ, hcoeff⟩ := exists_window_taylor_bound_of_integrableOn hL hLapN hwin
    have hord {z : ℂ} (hz : θ < z.re) : meromorphicOrderAt N z = meromorphicOrderAt F z :=
      meromorphicOrderAt_toMeromorphicNFOn hF hz
    have hleA {z : ℂ} (h : meromorphicOrderAt F z < 0) : z.re ≤ A :=
      le_of_not_gt fun hz ↦ h.not_ge (hAn z hz).meromorphicOrderAt_nonneg
    have hleft (z : ℂ) (hz : θ < z.re) (h : meromorphicOrderAt N z < 0) : z.re < σ :=
      (hleA ((hord hz).symm.trans_lt h)).trans_lt
        ((le_max_left A θ).trans_lt ((le_max_left ..).trans_lt hσ))
    obtain ⟨β, hb, hbp, hmax, hRe⟩ :=
      (meromorphicNFOn_toMeromorphicNFOn F {z | θ < z.re})
        |>.exists_rightmost_real_pole_of_window_taylor_bound hleft
          (hp.imp fun z ⟨hz, h⟩ ↦ ⟨hz, (hord hz).trans_lt h⟩) hcoeff
    have hb' : θ < (β : ℂ).re := by simpa using hb
    rw [hord hb'] at hbp
    have hIm := im_meromorphicTrailingCoeffAt_eq_zero_of_hasLaplace hF hLap hb
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE (hF.toMeromorphicNFOn_eq_self_on_nhdsNE hb')] at hRe
    refine Or.inr ⟨β, ⟨hb, by simpa using hleA hbp⟩, hbp,
      fun z hz h ↦ hmax z ((hord hz).trans_lt h), hRe.lt_of_ne ?_, hIm⟩
    intro hzero
    apply (hF β hb').meromorphicTrailingCoeffAt_ne_zero hbp.ne_top
    exact Complex.ext hzero hIm
  · exact Or.inl fun z hz ↦ le_of_not_gt fun h ↦ hp ⟨z, hz, h⟩

end TauCeti
