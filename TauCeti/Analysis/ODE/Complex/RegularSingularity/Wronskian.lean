/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Basic
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Complex.PowerSeries.BranchCut
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.ODE.Wronskian
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Abel–Liouville Wronskian and fundamental pair at a regular singularity

For `w''(z) + f(z) w'(z) + g(z) w(z) = 0` at a regular singularity `z₀` where
`(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and `(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` on `0 < ‖z - z₀‖ < r`:
* Using `H(u) = ∑_{s ≥ 1} (fs s / s) u^s`
  (`FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_div_natCast`,
  `HasFPowerSeriesOnBall.hasDerivAt_tsum_div_natCast`), the weighted Wronskian
  `(z - z₀)^{fs 0} exp(H(z - z₀)) (w₁ w₂' - w₁' w₂)` is constant on
  `{z | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}` (`TauCeti.cpow_mul_exp_mul_wronskian_eq`).
* Explicit Abel–Liouville formulas (`TauCeti.wronskian_regularSingular_eq`,
  `TauCeti.wronskian_regularSingular_second_eq`), nonvanishing
  (`TauCeti.wronskian_regularSingular_ne_zero`, `TauCeti.wronskian_regularSingular_second_ne_zero`),
  and fundamental pair existence (`TauCeti.exists_regularSingular_fundamental_pair` for
  `TauCeti.regularSingularEquation`).

## References
* NIST DLMF §2.7(ii), 2.7.1–2.7.6, <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology ENNReal

namespace TauCeti

/-- **Abel–Liouville Wronskian constancy at a regular singularity**: for any two holomorphic
solutions `w₁`, `w₂` of `w'' + f w' + g w = 0` on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`,
where `(z - z₀) f(z) = ∑ fs s * (z - z₀)^s` on `0 < ‖z - z₀‖ < r`, the weighted Wronskian
`(z - z₀)^{fs 0} exp(H(z - z₀)) (w₁ w₂' - w₁' w₂)` is constant on the slit punctured disc, where
`H(u) = ∑' s, (if s = 0 then 0 else fs s / s) * u ^ s`. -/
theorem cpow_mul_exp_mul_wronskian_eq {z₀ : ℂ} {r : ℝ} {f g w₁ w₂ : ℂ → ℂ} {fs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hw₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hsol₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (hw₂ : DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hsol₂ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0) :
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    let F : ℂ → ℂ := fun z =>
      (z - z₀) ^ fs 0 * cexp (H (z - z₀)) * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z)
    ∀ z₁ z₂, z₁ ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} →
      z₂ ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} → F z₁ = F z₂ := by
  intro H _ z₁ z₂ hz₁ hz₂
  set U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
  have hr : 0 < r := (norm_nonneg (z₁ - z₀)).trans_lt hz₁.2
  have hopen : IsOpen U := isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  have hpF := FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt fs z₀ hr
    fun z hz0 hzr => (hf z hz0 hzr).summable
  have hE : ∀ z ∈ U, HasDerivAt (fun w => (w - z₀) ^ fs 0 * cexp (H (w - z₀)))
      (f z * ((z - z₀) ^ fs 0 * cexp (H (z - z₀)))) z := by
    rintro z ⟨hzs, hzb⟩
    have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
    have hH_at : HasDerivAt H (((∑' s, fs s * (z - z₀) ^ s) - fs 0) / (z - z₀)) (z - z₀) := by
      simpa only [sub_zero, zero_add] using
        hpF.hasDerivAt_tsum_div_natCast hzu0 (eNorm_lt_ofReal_iff.mpr hzb)
    have hH_deriv : HasDerivAt (fun w => H (w - z₀)) (f z - fs 0 * (z - z₀)⁻¹) z :=
      (hH_at.comp_sub_const z z₀).congr_deriv (by
        rw [(hf z (norm_pos_iff.mpr hzu0) hzb).tsum_eq]; field_simp [hzu0])
    refine ((((hasDerivAt_id z).sub_const z₀).cpow_const (c := fs 0) hzs).mul
      hH_deriv.cexp).congr_deriv ?_
    dsimp only [id]
    rw [cpow_eq_cpow_sub_natCast_mul_pow hzu0 (fs 0) 1, Nat.cast_one, pow_one]
    field_simp [hzu0]; ring
  have hpre : IsPreconnected U := isPreconnected_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  exact mul_wronskian_eq_of_hasDerivAt (g := g) hopen hpre
    hE (fun z hz => (hw₁.differentiableAt (hopen.mem_nhds hz)).hasDerivAt)
    (fun z hz => ((hw₁.deriv hopen).differentiableAt (hopen.mem_nhds hz)).hasDerivAt.congr_deriv
      (by linear_combination hsol₁ z hz.1 hz.2))
    (fun z hz => (hw₂.differentiableAt (hopen.mem_nhds hz)).hasDerivAt)
    (fun z hz => ((hw₂.deriv hopen).differentiableAt (hopen.mem_nhds hz)).hasDerivAt.congr_deriv
      (by linear_combination hsol₂ z hz.1 hz.2)) hz₁ hz₂

/-- Pointwise algebraic evaluation of the weighted Wronskian for the Frobenius ansatz at `z₀ + t`
with `0 < t < r`. -/
private theorem wronskian_ansatz_eval_of_pos {z₀ α₁ α₂ c : ℂ} {N : ℕ} {r t : ℝ}
    {fs a b : ℕ → ℂ} (hvieta : α₁ + α₂ = 1 - fs 0) (hcN : c = 0 ∨ α₁ - α₂ = N)
    (ha_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    (hb_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b s * (z - z₀) ^ s)
    (ht0 : 0 < t) (htr : t < r) :
    let A₁ : ℂ → ℂ := fun u => ∑' s, a s * u ^ s
    let B : ℂ → ℂ := fun u => ∑' s, b s * u ^ s
    let w₁ : ℂ → ℂ := fun z => (z - z₀) ^ α₁ * A₁ (z - z₀)
    let w₂ : ℂ → ℂ := fun z => (z - z₀) ^ α₂ * B (z - z₀) + c * w₁ z * Complex.log (z - z₀)
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    (t : ℂ) ^ fs 0 * cexp (H t) *
        (w₁ (z₀ + t) * deriv w₂ (z₀ + t) - deriv w₁ (z₀ + t) * w₂ (z₀ + t)) =
      cexp (H t) * ((α₂ - α₁) * A₁ t * B t + t * (A₁ t * deriv B t - deriv A₁ t * B t) +
        c * (t : ℂ) ^ N * A₁ t ^ 2) := by
  intro A₁ B w₁ w₂ H
  have hts : ((t : ℝ) : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr ht0
  have htb : ‖((t : ℝ) : ℂ)‖ < r := by simpa [abs_of_pos ht0] using htr
  have ht_ne : ((t : ℝ) : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hts
  have hw₁_d1 := hasDerivAt_cpow_mul_tsum (σ := α₁) ha_sum (z := z₀ + t)
    (by simpa using hts) (by simpa using htb)
  have hψ_d1 := hasDerivAt_cpow_mul_tsum (σ := α₂) hb_sum (z := z₀ + t)
    (by simpa using hts) (by simpa using htb)
  have hdw₁ : deriv w₁ (z₀ + t) = (t : ℂ) ^ (α₁ - 1) * (α₁ * A₁ t + t * deriv A₁ t) := by
    simpa only [w₁, A₁, add_sub_cancel_left] using hw₁_d1.deriv
  have hdw₂ : deriv w₂ (z₀ + t) = (t : ℂ) ^ (α₂ - 1) * (α₂ * B t + t * deriv B t) +
      c * (deriv w₁ (z₀ + t) * Complex.log t + (t : ℂ)⁻¹ * w₁ (z₀ + t)) := by
    have hsum_d : HasDerivAt w₂ _ (z₀ + t) :=
      (hψ_d1.add ((hw₁_d1.const_mul c).mul_log_sub (z₀ := z₀)
        (by simpa using hts))).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by
          dsimp only [Pi.add_apply, w₂, w₁, A₁, B])
    rw [hsum_d.deriv, hdw₁]; dsimp only [w₁, A₁, B]; simp only [add_sub_cancel_left]; ring
  rw [hdw₂, hdw₁]; dsimp only [w₁, w₂, A₁, B]; simp only [add_sub_cancel_left]
  have hpow_add3 (x y z : ℂ) :
      (t : ℂ) ^ x * ((t : ℂ) ^ y * (t : ℂ) ^ z) = (t : ℂ) ^ (x + y + z) := by
    rw [← Complex.cpow_add _ _ ht_ne, ← Complex.cpow_add _ _ ht_ne, add_assoc]
  have hpow_one {p q : ℂ} (h : fs 0 + p + q = 0) :
      (t : ℂ) ^ fs 0 * ((t : ℂ) ^ p * (t : ℂ) ^ q) = 1 := by
    rw [hpow_add3, h, Complex.cpow_zero]
  have hp1 := hpow_one (p := α₁) (q := α₂ - 1) (by linear_combination hvieta)
  have hp2 := hpow_one (p := α₁ - 1) (q := α₂) (by linear_combination hvieta)
  have hc_pow : c * ((t : ℂ) ^ fs 0 * ((t : ℂ)⁻¹ * ((t : ℂ) ^ α₁ * (t : ℂ) ^ α₁))) =
      c * (t : ℂ) ^ N := by
    rcases hcN with rfl | hdiff
    · simp
    · rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ ht_ne, hpow_add3,
        ← Complex.cpow_natCast (t : ℂ) N]
      congr 2; linear_combination hvieta + hdiff
  linear_combination cexp (H t) * (A₁ t * (α₂ * B t + t * deriv B t)) * hp1 -
    cexp (H t) * ((α₁ * A₁ t + t * deriv A₁ t) * B t) * hp2 + cexp (H t) * A₁ t ^ 2 * hc_pow

/-- Unified Abel–Liouville Wronskian evaluation for any pair of solutions of the form
`w₁(z) = (z - z₀)^{α₁} ∑ a_s (z - z₀)^s` and
`w₂(z) = (z - z₀)^{α₂} ∑ b_s (z - z₀)^s + c * w₁(z) * log(z - z₀)` when `α₁ + α₂ = 1 - fs 0`
and either `c = 0` or `α₁ - α₂ = N`. -/
private theorem abel_liouville_wronskian_ansatz_eq {z₀ α₁ α₂ c : ℂ} {N : ℕ} {r : ℝ}
    {f g : ℂ → ℂ} {fs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hvieta : α₁ + α₂ = 1 - fs 0) (hcN : c = 0 ∨ α₁ - α₂ = N)
    (ha_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    (hb_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b s * (z - z₀) ^ s)
    (hw₁_sol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      let w₁ := fun w => (w - z₀) ^ α₁ * ∑' s, a s * (w - z₀) ^ s
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (hw₂_sol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      let w₁ := fun w => (w - z₀) ^ α₁ * ∑' s, a s * (w - z₀) ^ s
      let w₂ := fun w =>
        (w - z₀) ^ α₂ * (∑' s, b s * (w - z₀) ^ s) + c * w₁ w * Complex.log (w - z₀)
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0) :
    let w₁ : ℂ → ℂ := fun z => (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s
    let w₂ : ℂ → ℂ := fun z =>
      (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) + c * w₁ z * Complex.log (z - z₀)
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      (z - z₀) ^ fs 0 * cexp (H (z - z₀)) * (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z) =
        (α₂ - α₁) * a 0 * b 0 + c * (0 : ℂ) ^ N * a 0 ^ 2 := by
  intro w₁ w₂ H z hzs hzb
  have hr : 0 < r := (norm_nonneg (z - z₀)).trans_lt hzb
  have hconst := cpow_mul_exp_mul_wronskian_eq (w₁ := w₁) (w₂ := w₂) hf
    (fun w hw =>
      (hasDerivAt_cpow_mul_tsum ha_sum hw.1 hw.2).differentiableAt.differentiableWithinAt)
    hw₁_sol
    (fun w hw => ((hasDerivAt_cpow_mul_tsum (σ := α₂) hb_sum hw.1 hw.2).add
      (((hasDerivAt_cpow_mul_tsum (σ := α₁) ha_sum hw.1 hw.2).const_mul c).mul_log_sub
        hw.1)).differentiableAt.differentiableWithinAt)
    hw₂_sol
  have hpF := FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt fs z₀ hr
    fun w hw0 hwr => (hf w hw0 hwr).summable
  have hH_cont : ContinuousAt H 0 := by
    simpa only [sub_zero] using
      (FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_div_natCast fs 0
        (ENNReal.ofReal_pos.mpr hr) hpF.r_le).analyticAt.continuousAt
  set A₁ : ℂ → ℂ := fun u => ∑' s, a s * u ^ s; set B : ℂ → ℂ := fun u => ∑' s, b s * u ^ s
  have hA₁_an := FormalMultilinearSeries.analyticOnNhd_tsum_ofScalars_of_norm_sub_lt a z₀ hr
    fun w _ => ha_sum w
  have hB_an := FormalMultilinearSeries.analyticOnNhd_tsum_ofScalars_of_norm_sub_lt b z₀ hr
    fun w _ => hb_sum w
  -- `fun_prop` uses `hH_cont`, `hA₁_cont`, `hB_cont`, `hdA₁_cont`, and `hdB_cont`
  -- to prove `hG_cont0`.
  have hA₁_cont : ContinuousAt A₁ 0 := (hA₁_an 0 (mem_ball_self hr)).continuousAt
  have hB_cont : ContinuousAt B 0 := (hB_an 0 (mem_ball_self hr)).continuousAt
  have hdA₁_cont : ContinuousAt (deriv A₁) 0 := (hA₁_an.deriv 0 (mem_ball_self hr)).continuousAt
  have hdB_cont : ContinuousAt (deriv B) 0 := (hB_an.deriv 0 (mem_ball_self hr)).continuousAt
  set G : ℂ → ℂ := fun u =>
    cexp (H u) * ((α₂ - α₁) * A₁ u * B u + u * (A₁ u * deriv B u - deriv A₁ u * B u) +
      c * u ^ N * A₁ u ^ 2)
  have hG_cont0 : ContinuousAt G 0 := by fun_prop
  have htsum0 (d : ℕ → ℂ) : (∑' s : ℕ, d s * (0 : ℂ) ^ s) = d 0 := by
    simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul, mul_one] using
      FormalMultilinearSeries.ofScalarsSum_zero (E := ℂ) d
  have hH0 : H 0 = 0 := by dsimp [H]; rw [htsum0]; simp
  have hG0 : G 0 = (α₂ - α₁) * a 0 * b 0 + c * (0 : ℂ) ^ N * a 0 ^ 2 := by
    simp [G, hH0, A₁, B, htsum0]
  have hFG : ∀ t ∈ Ioo (0 : ℝ) r, (z - z₀) ^ fs 0 * cexp (H (z - z₀)) *
      (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z) = G (t : ℂ) := fun t ⟨ht0, htr⟩ =>
    (hconst z (z₀ + t) ⟨hzs, hzb⟩ ⟨by simpa using Complex.ofReal_mem_slitPlane.mpr ht0,
      by simpa [abs_of_pos ht0] using htr⟩).trans (by
      simpa only [G, H, w₁, w₂, A₁, B, add_sub_cancel_left] using
        wronskian_ansatz_eval_of_pos (fs := fs) hvieta hcN ha_sum hb_sum ht0 htr)
  exact tendsto_nhds_unique
    (tendsto_const_nhds.congr' (by filter_upwards [Ioo_mem_nhdsGT hr] with t ht; exact hFG t ht))
    (hG0 ▸ hG_cont0.tendsto.comp
      ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds))

private theorem eq_mul_cpow_neg_mul_cexp_neg_of_mul_eq {u p h w c : ℂ} (hu : u ≠ 0)
    (heq : u ^ p * cexp h * w = c) : w = c * u ^ (-p) * cexp (-h) := by
  have hne : u ^ p * cexp h ≠ 0 :=
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl hu)) (Complex.exp_ne_zero h)
  rw [← eq_inv_mul_iff_mul_eq₀ hne, (Commute.all _ _).mul_inv, ← Complex.cpow_neg,
    ← Complex.exp_neg] at heq
  linear_combination heq

/-- **Abel–Liouville Wronskian formula** for two pure-series solutions
`regularSingularSolution fs gs z₀ α₁` and `regularSingularSolution fs gs z₀ α₂` attached to
indicial roots `α₁`, `α₂` satisfying the positive-shift conditions `Q(α₁ + s) ≠ 0` and
`Q(α₂ + s) ≠ 0` for all `s ≥ 1`:
`w₁ z * deriv w₂ z - deriv w₁ z * w₂ z = (α₂ - α₁) * (z - z₀)^{-fs 0} * exp(-H(z - z₀))` on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, where `H(u) = ∑_{s ≥ 1} (fs s / s) u^s`. Equal roots
`α₁ = α₂` are allowed (giving Wronskian `0`). -/
theorem wronskian_regularSingular_eq {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0)
    (hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0) :
    let w₁ := regularSingularSolution fs gs z₀ α₁
    let w₂ := regularSingularSolution fs gs z₀ α₂
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z =
        (α₂ - α₁) * (z - z₀) ^ (-fs 0) * cexp (-H (z - z₀)) := by
  intro w₁ w₂ H z hzs hzb
  obtain ⟨ha₁_sum, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact]) hres₁
  obtain ⟨ha₂_sum, hw₂_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact]) hres₂
  have hw₁_op := ((isSolution_regularSingularEquation_iff hf hg _).mp hw₁_sol).2
  have hw₂_op := ((isSolution_regularSingularEquation_iff hf hg _).mp hw₂_sol).2
  rw [regularSingularSolution_eq] at hw₁_op hw₂_op
  have hId := abel_liouville_wronskian_ansatz_eq (c := 0) (N := 1) hf
    (forall_indicialPoly_eq_sub_mul_sub_iff.mp hfact).1 (Or.inl rfl) ha₁_sum ha₂_sum
    (fun w hws hwb => hw₁_op w (mem_regularSingularSlitDisc.mpr ⟨hws, hwb⟩))
    (fun w hws hwb => by
      simpa only [zero_mul, add_zero] using hw₂_op w (mem_regularSingularSlitDisc.mpr ⟨hws, hwb⟩))
    z hzs hzb
  simp only [zero_mul, add_zero, regularSingularCoeff_zero, mul_one] at hId
  dsimp only [w₁, w₂]
  rw [regularSingularSolution_eq, regularSingularSolution_eq]
  exact eq_mul_cpow_neg_mul_cexp_neg_of_mul_eq (Complex.slitPlane_ne_zero hzs) hId

/-- For two distinct indicial roots `α₁ ≠ α₂` that are both non-resonant (`Q(αᵢ + s) ≠ 0` for all
`s ≥ 1`), the two canonical series solutions attached to `α₁` and `α₂` have nowhere-vanishing
Wronskian on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_ne_zero {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0)
    (hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0)
    (hne : α₁ ≠ α₂) :
    let w₁ := regularSingularSolution fs gs z₀ α₁
    let w₂ := regularSingularSolution fs gs z₀ α₂
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  intro w₁ w₂ z hzs hzb
  rw [wronskian_regularSingular_eq hf hg hfact hres₁ hres₂ z hzs hzb]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hne.symm)
    (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.slitPlane_ne_zero hzs)))) (Complex.exp_ne_zero _)

/-- **Abel–Liouville Wronskian formula** in the resonant/logarithmic case `α₁ - α₂ = N ∈ ℕ`:
`w₁ z * deriv w₂ z - deriv w₁ z * w₂ z` equals
`(if N = 0 then 1 else -N) * (z - z₀)^{-fs 0} * exp(-H(z - z₀))` on the slit punctured disc,
where `H(u) = ∑_{s ≥ 1} (fs s / s) u^s`. -/
theorem wronskian_regularSingular_second_eq {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    let w₁ := regularSingularSolution fs gs z₀ α₁
    let w₂ := regularSingularSecondSolution fs gs z₀ α₂ N
    let H : ℂ → ℂ := fun u => ∑' s : ℕ, (if s = 0 then (0 : ℂ) else fs s / s) * u ^ s
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z =
        (if N = 0 then (1 : ℂ) else -(N : ℂ)) * (z - z₀) ^ (-fs 0) * cexp (-H (z - z₀)) := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  intro w₁ w₂ H z hzs hzb
  set a := regularSingularCoeff fs gs (α₂ + N)
  set b := regularSingularSecondCoeff fs gs α₂ N
  set c := regularSingularLogMultiplier fs gs α₂ N
  obtain ⟨ha_sum, hw₁_sol, -⟩ := regularSingularCoeff_solution_add_nat hf hg hfact
  obtain ⟨hb_sum, hw₂_sol⟩ := regularSingular_second_solution hf hg hfact hdiff
  have hw₁_op := ((isSolution_regularSingularEquation_iff hf hg _).mp hw₁_sol).2
  have hw₂_op := ((isSolution_regularSingularEquation_iff hf hg _).mp hw₂_sol).2
  rw [regularSingularSolution_eq] at hw₁_op
  rw [regularSingularSecondSolution_eq, regularSingularSolution_eq] at hw₂_op
  have hId := abel_liouville_wronskian_ansatz_eq (c := c) (N := N) hf
    (forall_indicialPoly_eq_sub_mul_sub_iff.mp hfact).1 (Or.inr hdiff) ha_sum hb_sum
    (fun w hws hwb => hw₁_op w (mem_regularSingularSlitDisc.mpr ⟨hws, hwb⟩))
    (fun w hws hwb => by
      simpa only [b, c] using hw₂_op w (mem_regularSingularSlitDisc.mpr ⟨hws, hwb⟩))
    z hzs hzb
  have hdiff' : α₂ - (α₂ + N) = -(N : ℂ) := by ring
  have ha0 : a 0 = 1 := regularSingularCoeff_zero fs gs (α₂ + N)
  have hconst : (α₂ - (α₂ + N)) * a 0 * b 0 + c * (0 : ℂ) ^ N * a 0 ^ 2 =
      if N = 0 then (1 : ℂ) else -(N : ℂ) := by
    rw [hdiff', ha0, mul_one, one_pow, mul_one]
    rcases eq_or_ne N 0 with rfl | hN0
    · have hc0 : c = 1 := regularSingularLogMultiplier_zero fs gs α₂
      simp [hc0]
    · have hb0 : b 0 = 1 :=
        regularSingularSecondCoeff_zero_of_pos fs gs α₂ (Nat.pos_of_ne_zero hN0)
      simp [hN0, hb0, zero_pow hN0]
  dsimp only [w₁, w₂]
  rw [regularSingularSolution_eq, regularSingularSecondSolution_eq, regularSingularSolution_eq]
  exact eq_mul_cpow_neg_mul_cexp_neg_of_mul_eq (Complex.slitPlane_ne_zero hzs) (hId.trans hconst)

/-- When `α₁ - α₂ = N ∈ ℕ`, the primary series solution `w₁` and the second solution `w₂` have
nowhere-vanishing Wronskian on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. -/
theorem wronskian_regularSingular_second_ne_zero {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    let w₁ := regularSingularSolution fs gs z₀ α₁
    let w₂ := regularSingularSecondSolution fs gs z₀ α₂ N
    ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  intro w₁ w₂ z hzs hzb
  rw [wronskian_regularSingular_second_eq hf hg hfact hdiff z hzs hzb]
  refine mul_ne_zero (mul_ne_zero ?_
    (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.slitPlane_ne_zero hzs)))) (Complex.exp_ne_zero _)
  split_ifs with hN0
  · exact one_ne_zero
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hN0)

/-- **Existence of a fundamental pair of `LinearEquation` solutions at every regular singularity**:
on `regularSingularSlitDisc z₀ r`, `regularSingularEquation hf hg` always possesses two solutions
with nowhere-vanishing Wronskian. -/
theorem exists_regularSingular_fundamental_pair {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z)) :
    ∃ w₁ w₂ : ℂ → ℂ,
      (regularSingularEquation hf hg).IsSolution w₁ ∧
      (regularSingularEquation hf hg).IsSolution w₂ ∧
      ∀ z ∈ regularSingularSlitDisc z₀ r,
        w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  obtain ⟨α₁, α₂, hre, hfact⟩ := exists_indicialPoly_roots (fs 0) (gs 0)
  have hres₁ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) ≠ 0 :=
    fun _ hs => indicialPoly_add_nat_ne_zero_of_re_le hfact hre hs
  have hw₁ := (regularSingularCoeff_solution hf hg (by simp [hfact]) hres₁).2
  by_cases hnat : ∃ N : ℕ, α₁ - α₂ = N
  · obtain ⟨N, hN⟩ := hnat
    exact ⟨_, _, hw₁, (regularSingular_second_solution hf hg hfact hN).2, fun z hz =>
      let h := mem_regularSingularSlitDisc.mp hz
      wronskian_regularSingular_second_ne_zero hf hg hfact hN z h.1 h.2⟩
  · have hnat' := not_exists.mp hnat
    have hres₂ : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0 := fun s hs =>
      (indicialPoly_add_nat_ne_zero_iff hfact).mpr ⟨by omega, hnat' s⟩
    exact ⟨_, _, hw₁, (regularSingularCoeff_solution hf hg (by simp [hfact]) hres₂).2, fun z hz =>
      let h := mem_regularSingularSlitDisc.mp hz
      wronskian_regularSingular_ne_zero hf hg hfact hres₁ hres₂
        (fun h0 => hnat' 0 (by simp [h0])) z h.1 h.2⟩

end TauCeti
