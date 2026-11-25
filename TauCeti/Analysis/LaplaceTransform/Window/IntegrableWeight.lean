/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.LaplaceTransform.GammaKernel
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Window bounds for Laplace coefficients with an integrable weight

An exponential moment of the absolute input controls the contribution outside a scale window.
The degree is chosen so that both tails can be compared with kernels at tilted rates. This gives
an upper bound for the signed Taylor coefficients at a real centre and at every vertical shift
of that centre, without a pointwise growth hypothesis on the input.

The coefficient comparison uses the same normalization as `Deduction.landau_coeff` in
Levent Alpöge's Lean formalization of the Riemann hypothesis for Dirichlet L-functions
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex Filter MeasureTheory Real Set
open scoped Nat AbsoluteValue

namespace TauCeti

local notation "W" => fun (k : ℕ) (a u : ℝ) ↦ u ^ k * Real.exp (-(a * u)) / k !
local notation "P" => fun (t : ℝ) ↦ t * Real.exp (1 - t)
local notation "C" => fun (Φ : ℂ → ℂ) (k : ℕ) (z : ℂ) ↦
  ((-1) ^ k / k ! : ℂ) * iteratedDeriv k Φ z

/-- At a degree `k` large enough for the tails of `[U, b⁴ U]` to lie on the two sides of the
kernel's peak, the tilted rates used in the tails give a uniform majorant. -/
private theorem gammaKernel_le_inv_pow_of_notMem_window {b a r U : ℝ} {k : ℕ}
    (hb : 1 < b) (ha : 0 < a)
    (hr : 0 < r) (hq : max (P (b ^ 2)⁻¹) (P b) * r ≤ a)
    (hk₁ : a * b ^ 2 * U ≤ (k : ℝ)) (hk₂ : (k : ℝ) ≤ a * b ^ 3 * U)
    {u : ℝ} (hu : 0 ≤ u) (h : u ∉ Icc U (b ^ 4 * U)) : W k a u ≤ (r ^ k)⁻¹ := by
  have tilt (t : ℝ) (ht : 0 < t) (hexp : (a / t - a) * u ≤ (1 - t) * k)
      (htr : P t * r ≤ a) : W k a u ≤ (r ^ k)⁻¹ := by
    have ht' : 0 < a / t := div_pos ha ht
    have hs : a - (a - a / t) = a / t := by ring
    dsimp only
    rw [pow_mul_exp_neg_mul_div_factorial_eq_exp_neg_mul_mul k a (a - a / t), hs]
    calc
      _ ≤ Real.exp ((1 - t) * k) * ((a / t) ^ k)⁻¹ := by
        refine mul_le_mul ?_ (pow_mul_exp_neg_mul_div_factorial_le_inv_pow k ht' hu)
          (pow_mul_exp_neg_mul_div_factorial_nonneg k _ hu) (by positivity)
        apply Real.exp_le_exp.mpr
        linarith
      _ = (P t / a) ^ k := by
        rw [mul_comm (1 - t) (k : ℝ), Real.exp_natCast_mul, ← inv_pow, inv_div, ← mul_pow]
        congr 1
        dsimp
        ring
      _ ≤ (r ^ k)⁻¹ := by
        rw [← inv_pow]
        apply pow_le_pow_left₀ (by positivity)
        calc
          P t / a ≤ (a / r) / a := div_le_div_of_nonneg_right ((le_div_iff₀ hr).2 htr) ha.le
          _ = r⁻¹ := by field_simp [ha.ne']
  have hb₀ : 0 < b := lt_trans zero_lt_one hb
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with hleft | hright
  · have hb₂ : 1 ≤ b ^ 2 := by nlinarith
    refine tilt (b ^ 2)⁻¹ (by positivity) ?_ ?_
    · rw [div_inv_eq_mul, ← mul_sub_one, mul_comm a, mul_assoc]
      have h₁ : (b ^ 2 - 1) * (a * u) ≤ (b ^ 2 - 1) * (a * U) := by gcongr
      have h₂ := mul_le_mul_of_nonneg_left hk₁ (sub_nonneg.mpr (inv_le_one_of_one_le₀ hb₂))
      have he : (1 - (b ^ 2)⁻¹) * (a * b ^ 2 * U) = (b ^ 2 - 1) * (a * U) := by
        field_simp
      rw [he] at h₂
      exact h₁.trans h₂
    · exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le).trans hq
  · refine tilt b hb₀ ?_ ((mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le).trans hq)
    apply (mul_le_mul_iff_right₀ hb₀).mp
    have he : b * (a / b - a) = (1 - b) * a := by field_simp
    rw [← mul_assoc, he, mul_assoc, mul_left_comm b]
    apply mul_le_mul_of_nonpos_left _ (sub_nonpos.mpr hb.le)
    calc
      b * (k : ℝ) ≤ b * (a * b ^ 3 * U) := mul_le_mul_of_nonneg_left hk₂ hb₀.le
      _ = a * (b ^ 4 * U) := by ring
      _ ≤ a * u := mul_le_mul_of_nonneg_left hright.le ha.le

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

/-- Integrate the real and vertical-shift integrands against the window majorants. -/
private theorem laplace_taylorCoeff_le_of_window_tail {g : ℝ → ℝ} {Φ : ℂ → ℂ} {A θ σ U V : ℝ}
    (hΦ : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z (Φ z))
    (hA : IntegrableOn (fun u ↦ g u * Real.exp (-(A * u))) (Ioi 0))
    (hσ : A < σ) (hθ : θ < σ) (hU : 0 < U) (k : ℕ)
    (htail : ∀ u > 0, u ∉ Icc U V → W k (σ - A) u ≤ ((σ - θ) ^ k)⁻¹)
    (γ : ℝ) :
    ‖C Φ k ((σ : ℂ) + (γ : ℂ) * I)‖ + (C Φ k (σ : ℂ)).re ≤
      2 * ((σ - θ) ^ k)⁻¹ *
        ((∫ u in Icc U V, max (g u) 0 * Real.exp (-(θ * u))) +
          ∫ u in Ioi 0, |g u| * Real.exp (-(A * u))) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let H (z : ℂ) (u : ℝ) := Complex.exp (-z * u) * (((u : ℂ) ^ k / k !) * (g u : ℂ))
  have hT (z : ℂ) (hz : z.re = σ) : Integrable (H z) μ ∧ (∫ u, H z u ∂μ) = C Φ k z := by
    have hn := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hz ▸ hσ)
    have h := hasLaplace_pow_div_factorial_smul_iteratedDeriv
      (eventually_of_mem hn fun w hw ↦ hΦ w hw) k
    exact ⟨by simpa only [H, smul_eq_mul] using h.integrable,
      by simpa only [H, smul_eq_mul] using h.integral_eq⟩
  let z : ℂ := (σ : ℂ) + (γ : ℂ) * I
  obtain ⟨hz, hzeq⟩ := hT z (by simp [z])
  obtain ⟨hs, hseq⟩ := hT (σ : ℂ) (by simp)
  have hpoint (u : ℝ) (hu : 0 < u) : ‖H z u‖ + (H σ u).re ≤ 2 * (max (g u) 0 * W k σ u) := by
    have hn : ‖H z u‖ = |g u| * W k σ u := by
      simp [H, z, Complex.norm_exp, norm_pow, abs_of_pos hu]
      ring
    have hr : (H σ u).re = g u * W k σ u := by
      dsimp only [H]
      rw [← ofReal_neg, ← ofReal_mul, ← ofReal_exp, ← ofReal_pow, ← ofReal_natCast,
        ← ofReal_div, ← ofReal_mul, ← ofReal_mul, ofReal_re]
      simp only [neg_mul]
      ring
    rw [hn, hr, ← add_mul, abs_add_eq_two_nsmul_posPart, two_nsmul, ← two_mul, mul_assoc]
    rfl
  rw [← hzeq, ← hseq, ← reCLM_apply, ← reCLM.integral_comp_comm hs]
  simp only [reCLM_apply]
  refine (add_le_add_left (norm_integral_le_integral_norm (μ := μ) (H z)) _).trans ?_
  have hsr : Integrable (fun u ↦ (H σ u).re) μ := hs.re
  rw [← integral_add hz.norm hsr]
  exact integral_le_window_of_le_kernel k hU hθ hA (hz.norm.add hsr) hpoint htail

/-- For the reflected Taylor coefficient `(-1)^k Φ⁽ᵏ⁾/k!`, bound the sum of its norm at any
vertical shift of the centre and its real part at the real centre. Only absolute integrability
of the input at the baseline rate `A` is used to control the tails.

The constants `q ∈ (0,1)` and `D > 0` depend only on the window ratio `L`. With `b = √√L`
and `p(t) = t exp (1 - t)`, one can take `q = max (p(1/b²), p(b))` and `D = 1 / (b² (b - 1))`.
The chosen degree is `⌈(σ - A) √L U⌉`, and the estimate holds once `(σ - A) U ≥ D` and the
expansion line `σ` satisfies `(σ - A) √L ≥ 1` and `q (σ - θ) ≤ σ - A`. -/
theorem exists_laplace_taylorCoeff_window_le {L : ℝ} (hL : 1 < L) :
    ∃ q ∈ Ioo (0 : ℝ) 1, ∃ D > 0,
      ∀ {g : ℝ → ℝ} {Φ : ℂ → ℂ} {A θ σ U : ℝ},
        (∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z (Φ z)) →
        IntegrableOn (fun u ↦ g u * Real.exp (-(A * u))) (Ioi 0) →
        1 ≤ (σ - A) * √L → θ < σ → q * (σ - θ) ≤ σ - A → D ≤ (σ - A) * U →
        let k := ⌈(σ - A) * √L * U⌉₊
        U ≤ (k : ℝ) ∧ ∀ γ : ℝ,
          ‖((-1) ^ k / k ! : ℂ) * iteratedDeriv k Φ ((σ : ℂ) + (γ : ℂ) * I)‖ +
              (((-1) ^ k / k ! : ℂ) * iteratedDeriv k Φ (σ : ℂ)).re ≤
            2 * ((σ - θ) ^ k)⁻¹ *
              ((∫ u in Icc U (L * U), max (g u) 0 * Real.exp (-(θ * u))) +
                ∫ u in Ioi 0, |g u| * Real.exp (-(A * u))) := by
  let b := √(√L)
  have hb : 1 < b := by
    dsimp [b]
    have hs : ∀ {x : ℝ}, 1 < x → 1 < √x := fun hx ↦ by
      simpa using (lt_sqrt (x := 1) zero_le_one).2 (by simpa using hx)
    exact hs (hs hL)
  have hb₂ : b ^ 2 = √L := sq_sqrt (sqrt_nonneg _)
  have hb₄ : b ^ 4 = L := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hb₂,
    sq_sqrt (by linarith)]
  have hprof {t : ℝ} (ht : t ≠ 1) : P t < 1 := by
    dsimp only
    rw [← lt_div_iff₀ (Real.exp_pos _), one_div, ← Real.exp_neg]
    simpa only [neg_sub, sub_add_cancel] using Real.add_one_lt_exp (sub_ne_zero.mpr ht)
  have hleft : (b ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  let q := max (P (b ^ 2)⁻¹) (P b)
  let D := (b ^ 2 * (b - 1))⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨q, ⟨lt_of_lt_of_le (by dsimp only; positivity : 0 < P b) (le_max_right _ _),
    max_lt (hprof hleft.ne) (hprof hb.ne')⟩, D, hD, ?_⟩
  intro g Φ A θ σ U hΦ hA hσ hθ hq hU k
  have ha : 0 < σ - A := pos_of_mul_pos_left (zero_lt_one.trans_le hσ) (sqrt_nonneg L)
  have hu : 0 < U := pos_of_mul_pos_right (hD.trans_le hU) ha.le
  have hk₁ : (σ - A) * b ^ 2 * U ≤ (k : ℝ) := by rw [hb₂]; exact Nat.le_ceil _
  have hk₂ : (k : ℝ) ≤ (σ - A) * b ^ 3 * U := by
    have hgap := (inv_le_iff_one_le_mul₀ (by positivity : 0 < b ^ 2 * (b - 1))).mp hU
    have hceil : (k : ℝ) < (σ - A) * b ^ 2 * U + 1 := by
      rw [hb₂]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith [show (σ - A) * b ^ 3 * U =
      (σ - A) * b ^ 2 * U + (σ - A) * U * (b ^ 2 * (b - 1)) by ring]
  refine ⟨?_, ?_⟩
  · rw [hb₂] at hk₁
    exact (le_mul_of_one_le_left hu.le hσ).trans hk₁
  · have htail (u : ℝ) (hpos : 0 < u) (hnot : u ∉ Icc U (L * U)) :=
      gammaKernel_le_inv_pow_of_notMem_window hb ha (sub_pos.mpr hθ) hq hk₁ hk₂ hpos.le
        (by rwa [hb₄])
    exact laplace_taylorCoeff_le_of_window_tail hΦ hA (sub_pos.mp ha) hθ hu k htail

end TauCeti
