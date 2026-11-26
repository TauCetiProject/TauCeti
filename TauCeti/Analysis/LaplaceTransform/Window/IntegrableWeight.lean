/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.LaplaceTransform.GammaKernel
import TauCeti.Analysis.LaplaceTransform.WindowCoefficients
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Window bounds for Laplace coefficients with an integrable weight

An exponential moment of the absolute input controls the contribution outside a scale window
`[U, L U]`. At the degree `k = ⌈(σ - A) √L U⌉` of
`TauCeti.pow_mul_exp_neg_mul_div_factorial_le_off_window`, the norm of the signed Taylor
coefficient `(-1)^k Φ⁽ᵏ⁾/k!` at any vertical shift `σ + iγ`, plus the real part of the same
coefficient at the real centre `σ`, is bounded uniformly in the shift. The real-part term can be
negative, so this does not bound the coefficient at `σ + iγ` by itself. No pointwise growth
hypothesis on the input is needed.

The coefficient comparison uses the same normalization as `Deduction.landau_coeff` in
Levent Alpöge's Lean formalization of the Riemann hypothesis for Dirichlet L-functions
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex Filter MeasureTheory Real Set
open scoped Nat AbsoluteValue Topology

namespace TauCeti

local notation "W" => fun (k : ℕ) (a u : ℝ) ↦ u ^ k * Real.exp (-(a * u)) / k !

/-- Compare an integrand bounded by the positive-part Gamma moment with its two integrable
majorants, using the different rates on and off the window. -/
private theorem integral_le_window_of_le_kernel {g J : ℝ → ℝ} {A θ σ U V : ℝ} (k : ℕ)
    (hU : 0 < U) (hr : θ < σ)
    (hA : IntegrableOn (fun u ↦ g u * Real.exp (-(A * u))) (Ioi 0))
    (hJ : IntegrableOn J (Ioi 0))
    (hJle : ∀ u > 0, J u ≤ 2 * (max (g u) 0 * W k σ u))
    (htail : ∀ u > 0, u ∉ Icc U V → W k (σ - A) u ≤ ((σ - θ) ^ k)⁻¹) :
    (∫ u in Ioi 0, J u) ≤ 2 * ((σ - θ) ^ k)⁻¹ *
      ((∫ u in Icc U V, max (g u) 0 * Real.exp (-(θ * u))) +
        ∫ u in Ioi 0, |g u| * Real.exp (-(A * u))) := by
  let s := Icc U V
  let F (u : ℝ) := max (g u) 0 * Real.exp (-(θ * u))
  let G (u : ℝ) := |g u| * Real.exp (-(A * u))
  let B := ((σ - θ) ^ k)⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsub : s ⊆ Ioi 0 := fun _ hu ↦ hU.trans_le hu.1
  have hs : MeasurableSet s := measurableSet_Icc
  have hrestrict : (volume.restrict (Ioi 0)).restrict s = volume.restrict s := by
    rw [Measure.restrict_restrict hs, inter_eq_left.mpr hsub]
  have hG : Integrable G (volume.restrict (Ioi 0)) := by
    simpa only [G, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hA.norm
  have hF : Integrable (s.indicator F) (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff hs, IntegrableOn, hrestrict]
    have hc : Continuous (fun u : ℝ ↦ Real.exp ((A - θ) * u)) := by fun_prop
    have hshift := (hA.mono_set hsub).mul_continuousOn hc.continuousOn isCompact_Icc
    have he (u : ℝ) : -(A * u) + (A - θ) * u = -(θ * u) := by ring
    refine (hshift.sup (integrable_zero _ _ _)).congr (ae_of_all _ fun u ↦ ?_)
    simp only [Pi.sup_apply, Pi.zero_apply, F,
      max_mul_of_nonneg _ _ (Real.exp_nonneg _), zero_mul, mul_assoc, ← Real.exp_add, he]
  have hbound (u : ℝ) (hu : 0 < u) : J u ≤ (2 * B) * (s.indicator F u + G u) := by
    apply (hJle u hu).trans
    have hmax : max (g u) 0 ≤ |g u| := max_le (le_abs_self _) (abs_nonneg _)
    by_cases h : u ∈ s
    · rw [indicator_of_mem h]
      have hw := pow_mul_exp_neg_mul_div_factorial_le_inv_pow k (sub_pos.mpr hr) hu.le
      dsimp only
      rw [pow_mul_exp_neg_mul_div_factorial_eq_exp_neg_mul_mul k σ θ]
      calc
        _ = (2 * F u) * W k (σ - θ) u := by dsimp [F]; ring
        _ ≤ (2 * F u) * B := mul_le_mul_of_nonneg_left hw (by dsimp [F]; positivity)
        _ = (2 * B) * F u := by ring
        _ ≤ (2 * B) * (F u + G u) := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (by dsimp [G]; positivity)) (mul_nonneg (by norm_num) hB)
    · rw [indicator_of_notMem h, zero_add]
      have hw := htail u hu h
      dsimp only
      rw [pow_mul_exp_neg_mul_div_factorial_eq_exp_neg_mul_mul k σ A]
      calc
        _ = 2 * (max (g u) 0 * Real.exp (-(A * u))) * W k (σ - A) u := by ring
        _ ≤ (2 * G u) * B := by
          apply mul_le_mul _ hw (pow_mul_exp_neg_mul_div_factorial_nonneg k _ hu.le)
            (by dsimp [G]; positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le)
            (by norm_num)
        _ = (2 * B) * G u := by ring
  have hi := integral_mono_ae hJ ((hF.add hG).const_mul (2 * B))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦ hbound u hu)
  simpa only [Pi.add_apply, integral_const_mul, integral_add hF hG, integral_indicator hs,
    hrestrict] using hi

/-- **Laplace coefficients on a window, with an integrable weight.** Let `Φ` be the Laplace
transform of a real input `g` on `re z > A`, and let `g u * exp (-A u)` be integrable on
`(0, ∞)`. At the degree `k = ⌈(σ - A) √L U⌉`, the norm of the signed Taylor coefficient
`(-1)^k Φ⁽ᵏ⁾/k!` at `σ + iγ`, plus the real part of that coefficient at `σ`, is at most
`2 (σ - θ)⁻ᵏ` times the positive part of `g` damped at rate `θ` on `[U, L U]` plus the absolute
exponential moment of `g` at rate `A`.

With `p(t) = t exp (1 - t)`, the rate condition is `q (σ - θ) ≤ σ - A` for
`q = max (p (1/√L)) (p (L^(1/4)))`, and the hypotheses on `σ - A` and `U` are those of
`TauCeti.pow_mul_exp_neg_mul_div_factorial_le_off_window`, which also gives `U ≤ k`. -/
theorem norm_add_re_laplace_coeff_le_window_of_integrableOn {g : ℝ → ℝ} {Φ : ℂ → ℂ}
    {A θ σ L U : ℝ} (hΦ : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z (Φ z))
    (hA : IntegrableOn (fun u ↦ g u * Real.exp (-(A * u))) (Ioi 0)) (hL : 1 < L)
    (hσ : 1 ≤ (σ - A) * √L) (hθ : θ < σ)
    (hq : max ((√L)⁻¹ * Real.exp (1 - (√L)⁻¹)) (√(√L) * Real.exp (1 - √(√L))) * (σ - θ) ≤
      σ - A)
    (hU : ((σ - A) * √L * (√(√L) - 1))⁻¹ ≤ U) (γ : ℝ) :
    let k := ⌈(σ - A) * √L * U⌉₊
    ‖((-1) ^ k / k ! : ℂ) • iteratedDeriv k Φ ((σ : ℂ) + (γ : ℂ) * I)‖ +
        (((-1) ^ k / k ! : ℂ) • iteratedDeriv k Φ (σ : ℂ)).re ≤
      2 * ((σ - θ) ^ k)⁻¹ *
        ((∫ u in Icc U (L * U), max (g u) 0 * Real.exp (-(θ * u))) +
          ∫ u in Ioi 0, |g u| * Real.exp (-(A * u))) := by
  intro k
  obtain ⟨hq₀, -, -, hker⟩ := pow_mul_exp_neg_mul_div_factorial_le_off_window hL hσ hU
  have ha : 0 < σ - A := pos_of_mul_pos_left (zero_lt_one.trans_le hσ) (sqrt_nonneg L)
  have hσθ : 0 < σ - θ := sub_pos.mpr hθ
  have hU₀ : 0 < U := by
    have hr : 1 < √(√L) := by
      rw [lt_sqrt zero_le_one, one_pow, lt_sqrt zero_le_one, one_pow]
      exact hL
    have : 0 < (σ - A) * √L * (√(√L) - 1) :=
      mul_pos (zero_lt_one.trans_le hσ) (sub_pos.mpr hr)
    exact (inv_pos.mpr this).trans_le hU
  -- Off the window, the kernel at the tilted rate `σ - A` is at most `(σ - θ)⁻ᵏ`.
  have htail (u : ℝ) (hu : 0 < u) (hout : u ∉ Icc U (L * U)) :
      W k (σ - A) u ≤ ((σ - θ) ^ k)⁻¹ := by
    refine (hker u hu.le hout).trans ?_
    rw [← inv_pow, ← inv_pow, ← mul_pow]
    refine pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr ha.le) hq₀.le) ?_ k
    rw [inv_mul_le_iff₀ ha, le_mul_inv_iff₀ hσθ]
    exact hq
  -- Reduce to the positive-part moment, then split it along the window.
  have hev (z : ℂ) (hz : A < z.re) :
      ∀ᶠ w in 𝓝 z, HasLaplace (fun u ↦ (g u : ℂ)) w (Φ w) :=
    eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
      fun w hw ↦ hΦ w hw
  have hzre : ((σ : ℂ) + (γ : ℂ) * I).re = σ := by simp
  have hσA : A < σ := sub_pos.mp ha
  have h₁ := norm_add_re_laplace_coeff_le (hev ((σ : ℂ) + (γ : ℂ) * I) (by rwa [hzre]))
    (hev (((σ : ℂ) + (γ : ℂ) * I).re : ℂ) (by rwa [ofReal_re, hzre])) k
  rw [hzre] at h₁
  refine h₁.trans ?_
  have hJ (u : ℝ) : max (g u) 0 * (u ^ k * Real.exp (-σ * u) / k !) =
      max (g u) 0 * W k σ u := by
    rw [neg_mul]
  simp only [hJ]
  by_cases hint : IntegrableOn (fun u ↦ max (g u) 0 * W k σ u) (Ioi 0)
  · rw [← integral_const_mul]
    exact integral_le_window_of_le_kernel k hU₀ hθ hA (hint.const_mul 2) (fun _ _ ↦ le_rfl)
      htail
  · rw [integral_undef hint, mul_zero]
    positivity

end TauCeti
