/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.Log.Deriv
import TauCeti.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Formal logarithms of zero-free complex power series

A zero-free analytic power series has a convergent formal logarithm on the same disk.
The normalized analytic logarithm has the formal logarithm as its Taylor series, so
exponentiating the evaluated formal logarithm recovers the original analytic sum.

## Main results

* `PowerSeries.summable_norm_coeff_logOf_mul_pow_of_zeroFree`: absolute convergence of the
  formal logarithm throughout a zero-free convergence disk.
* `PowerSeries.exp_tsum_coeff_logOf_mul_pow_of_zeroFree`: exponentiation recovers the original
  power series.
* `PowerSeries.le_radius_ofScalars_logOf_of_zeroFree` and
  `PowerSeries.differentiableOn_tsum_coeff_logOf_mul_pow_of_zeroFree`: the formal logarithm
  converges, and is holomorphic, throughout a zero-free disk of convergence.
* `PowerSeries.hasSum_coeff_logOf_mul_pow_of_slitPlane`: on a disk that the original series maps
  into the slit plane, the evaluated formal logarithm is the principal logarithm.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

/-- The formal logarithm converges absolutely throughout every zero-free disk on which the
original power series converges. -/
theorem summable_norm_coeff_logOf_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    Summable fun n : ℕ ↦ ‖coeff n (logOf f) * z ^ n‖ := by
  rw [← summable_nat_add_iff 1]
  refine (summable_norm_coeff_logDeriv_mul_pow_of_zeroFree f hf0 hr hne hz).mul_left ‖z‖
    |>.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  have hcast : (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by norm_num
  have hn : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [hcast, Complex.norm_natCast]
    norm_num
  rw [coeff_logDeriv, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, pow_succ]
  calc
    ‖coeff (n + 1) (logOf f)‖ * (‖z‖ ^ n * ‖z‖) =
        ‖coeff (n + 1) (logOf f)‖ * ‖z‖ ^ n * ‖z‖ * 1 := by ring
    _ ≤ ‖coeff (n + 1) (logOf f)‖ * ‖z‖ ^ n * ‖z‖ * ‖(n : ℂ) + 1‖ :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ‖z‖ * (‖coeff (n + 1) (logOf f)‖ * ‖(n : ℂ) + 1‖ * ‖z‖ ^ n) := by ring

private theorem coeff_logOf_eq_iteratedDeriv_of_deriv_eq (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1)
    (hfr : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (L₀ : ℂ → ℂ) (hL₀zero : L₀ 0 = 0)
    (hderiv : deriv L₀ =ᶠ[𝓝 0]
      _root_.logDeriv (FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f))
    (n : ℕ) :
    coeff n (logOf f) = iteratedDeriv n L₀ 0 / n.factorial := by
  cases n with
  | zero => simp [constantCoeff_logOf hf0, hL₀zero]
  | succ n =>
      have hb := coeff_logDeriv_eq_iteratedDeriv f hf0 hfr n
      rw [coeff_logDeriv] at hb
      rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq]
      push_cast [Nat.factorial_succ] at hb ⊢
      field_simp at hb ⊢
      exact hb

/-- **The evaluated formal logarithm exponentiates to the original power series.** If a complex
power series has constant coefficient one and is zero-free in a disk of convergence, then its
formal logarithm converges throughout that disk and its exponential is the analytic sum of the
original series. Apply this theorem with an explicit radius `r`; the left-hand side does not
determine it for simplification. -/
theorem exp_tsum_coeff_logOf_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    Complex.exp (∑' n : ℕ, coeff n (logOf f) * z ^ n) =
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z := by
  let F := FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f
  let G := _root_.logDeriv F
  -- Choose nested disks: the outer disk supports a logarithm, and the inner one supports
  -- its Taylor expansion at zero and contains the evaluation point.
  obtain ⟨R₂, hzR₂, hR₂r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hz
  obtain ⟨R₁, hzR₁, hR₁R₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hzR₂
  have hR₂pos : 0 < R₂ := by
    have : (0 : ENNReal) < (R₂ : ENNReal) :=
      (bot_le : (0 : ENNReal) ≤ ‖z‖ₑ).trans_lt hzR₂
    exact_mod_cast this
  have hR₂posE : (0 : ENNReal) < (R₂ : ENNReal) := by exact_mod_cast hR₂pos
  have hfr : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius :=
    hR₂posE.trans (hR₂r.trans_le hr)
  have hFseries :=
    ((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).hasFPowerSeriesOnBall hfr).mono
      hR₂posE (hR₂r.le.trans hr)
  have hFd : DifferentiableOn ℂ F (Metric.ball 0 R₂) := by
    intro w hw
    have hw' : w ∈ Metric.eball (0 : ℂ) (R₂ : ENNReal) := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
      exact NNReal.coe_lt_coe.mp (by simpa using Metric.mem_ball.mp hw)
    exact (hFseries.analyticAt_of_mem hw').differentiableAt.differentiableWithinAt
  have hFzero : (0 : ℂ) ∉ F '' Metric.ball 0 R₂ := by
    rintro ⟨w, hw, hw0⟩
    apply hne w
    · have hwR₂ : ‖w‖ₑ < (R₂ : ENNReal) := by
        rw [enorm_lt_coe]
        exact NNReal.coe_lt_coe.mp (by simpa using Metric.mem_ball.mp hw)
      exact hwR₂.trans hR₂r
    · exact hw0
  have hsc : IsSimplyConnected (Metric.ball (0 : ℂ) R₂) := by
    have : ContractibleSpace (Metric.ball (0 : ℂ) R₂) :=
      Metric.contractibleSpace_ball hR₂pos
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hLd, hLexp⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp
    hsc Metric.isOpen_ball hFd hFzero
  -- Normalize the analytic logarithm at zero; this removes the integral multiple of 2πi.
  let L₀ : ℂ → ℂ := fun w ↦ L w - L 0
  have hzeroBall : (0 : ℂ) ∈ Metric.ball 0 R₂ := Metric.mem_ball_self hR₂pos
  have hF0 : F 0 = 1 := by
    simpa [F, FormalMultilinearSeries.ofScalarsSum_zero, constantCoeff] using hf0
  have hLexp0 : Complex.exp (L 0) = 1 := by
    rw [← hF0]
    exact hLexp hzeroBall
  have hL₀d : DifferentiableOn ℂ L₀ (Metric.ball 0 R₂) :=
    hLd.sub (differentiableOn_const (c := L 0))
  have hL₀exp : Set.EqOn (Complex.exp ∘ L₀) F (Metric.ball 0 R₂) := by
    intro w hw
    simp only [Function.comp_apply, L₀, Complex.exp_sub, hLexp0, div_one]
    exact hLexp hw
  have hderiv : deriv L₀ =ᶠ[𝓝 0] G := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzeroBall] with w hw
    have hLdw : DifferentiableAt ℂ L w := (hLd w hw).differentiableAt
      (Metric.isOpen_ball.mem_nhds hw)
    have hsub : deriv L₀ w = deriv L w := (hLdw.hasDerivAt.sub_const (L 0)).deriv
    rw [hsub]
    exact TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp Metric.isOpen_ball hLd hLexp hw
  have hL₀a : AnalyticAt ℂ L₀ 0 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [Metric.isOpen_ball.mem_nhds hzeroBall] with w hw
    exact (hL₀d w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
  -- The coefficient lemma identifies this normalized logarithm with the formal log.
  have hcoeff : (fun n ↦ coeff n (logOf f)) =
      fun n ↦ iteratedDeriv n L₀ 0 / n.factorial := by
    funext n
    exact coeff_logOf_eq_iteratedDeriv_of_deriv_eq f hf0 hfr L₀ (by simp [L₀]) hderiv n
  have hformal : (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n (logOf f)) =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ iteratedDeriv n L₀ 0 / n.factorial) := by
    rw [hcoeff]
  -- Exchange the Taylor radius with the inner disk, then evaluate the series at z.
  have hTaylor := hL₀a.hasFPowerSeriesAt
  rw [← hformal] at hTaylor
  have hR₁pos : 0 < R₁ := by
    have : (0 : ENNReal) < (R₁ : ENNReal) :=
      (bot_le : (0 : ENNReal) ≤ ‖z‖ₑ).trans_lt hzR₁
    exact_mod_cast this
  have hclosed : Metric.closedBall (0 : ℂ) R₁ ⊆ Metric.ball 0 R₂ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right]
    exact hw.trans_lt (by exact_mod_cast hR₁R₂)
  have hR₁series := (hL₀d.mono hclosed).hasFPowerSeriesOnBall hR₁pos
  obtain ⟨r₀, hr₀⟩ := hTaylor
  have hlogSeries := hr₀.exchange_radius hR₁series
  have hzBall : z ∈ Metric.eball (0 : ℂ) (R₁ : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hzR₁
  have hsum : HasSum (fun n : ℕ ↦ coeff n (logOf f) * z ^ n) (L₀ z) := by
    simpa [mul_comm] using hlogSeries.hasSum hzBall
  rw [hsum.tsum_eq]
  exact hL₀exp (by
    rw [Metric.mem_ball, dist_zero_right]
    exact_mod_cast hzR₂)


/-- **The formal logarithm converges on every zero-free disk of convergence.** Its radius of
convergence is at least the radius of any disk inside the disk of convergence of `f` on which the
analytic sum of `f` has no zero. -/
theorem le_radius_ofScalars_logOf_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0) :
    r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n (logOf f)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun t ht ↦ ?_
  apply FormalMultilinearSeries.le_radius_of_summable
  have h := summable_norm_coeff_logOf_mul_pow_of_zeroFree f hf0 hr hne
    (z := ((t : ℝ) : ℂ)) (by simpa [enorm_eq_nnnorm] using ht)
  simpa [FormalMultilinearSeries.ofScalars_norm] using h

/-- The evaluated formal logarithm is holomorphic on every zero-free disk of convergence. -/
theorem differentiableOn_tsum_coeff_logOf_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∑' n : ℕ, coeff n (logOf f) * z ^ n)
      (Metric.eball 0 r) := by
  rcases eq_zero_or_pos r with rfl | hr0
  · exact fun z hz ↦ absurd hz (by simp)
  have hlog := le_radius_ofScalars_logOf_of_zeroFree f hf0 hr hne
  refine ((((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n (logOf f)).hasFPowerSeriesOnBall
    (hr0.trans_le hlog)).differentiableOn).mono (Metric.eball_subset_eball hlog)).congr
    fun z _ ↦ ?_
  simp only [FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- **The evaluated formal logarithm is the principal logarithm on a disk mapped into the slit
plane.** If the analytic sum of `f` sends a disk inside its disk of convergence into
`Complex.slitPlane`, then on that disk the formal logarithm of `f` sums to the principal value
`Complex.log` of the analytic sum, rather than to some other logarithm of it. -/
theorem hasSum_coeff_logOf_mul_pow_of_slitPlane (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hslit : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ∈ Complex.slitPlane)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    HasSum (fun n : ℕ ↦ coeff n (logOf f) * z ^ n)
      (Complex.log (FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z)) := by
  let F := FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f
  let Λ : ℂ → ℂ := fun w ↦ ∑' n : ℕ, coeff n (logOf f) * w ^ n
  let U := Metric.eball (0 : ℂ) r
  have hne : ∀ w : ℂ, ‖w‖ₑ < r → F w ≠ 0 := fun w hw ↦ Complex.slitPlane_ne_zero (hslit w hw)
  have hmem : ∀ {w : ℂ}, w ∈ U → ‖w‖ₑ < r := fun hw ↦ by
    simpa only [U, Metric.mem_eball, edist_zero_right] using hw
  have hr0 : 0 < r := zero_le.trans_lt hz
  have hFd : DifferentiableOn ℂ F U :=
    (((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).hasFPowerSeriesOnBall
      (hr0.trans_le hr)).differentiableOn).mono (Metric.eball_subset_eball hr)
  have hΛd : DifferentiableOn ℂ Λ U :=
    differentiableOn_tsum_coeff_logOf_mul_pow_of_zeroFree f hf0 hr hne
  have hLd : DifferentiableOn ℂ (fun w ↦ Complex.log (F w)) U := fun w hw ↦
    ((hFd w hw).differentiableAt (Metric.isOpen_eball.mem_nhds hw)).clog
      (hslit w (hmem hw)) |>.differentiableWithinAt
  -- `Λ` and `log ∘ F` are two holomorphic logarithms of `F` on the disk, both vanishing at `0`.
  have hΛexp : Set.EqOn (Complex.exp ∘ Λ) F U := fun w hw ↦
    exp_tsum_coeff_logOf_mul_pow_of_zeroFree f hf0 hr hne (hmem hw)
  have hderiv : Set.EqOn (deriv Λ) (deriv fun w ↦ Complex.log (F w)) U := fun w hw ↦ by
    rw [TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp Metric.isOpen_eball hΛd hΛexp hw,
      logDeriv_apply, ((((hFd w hw).differentiableAt
        (Metric.isOpen_eball.mem_nhds hw)).hasDerivAt).clog (hslit w (hmem hw))).deriv]
  have h0 : Λ 0 = Complex.log (F 0) := by
    have hF0 : F 0 = 1 := by
      simpa [F, FormalMultilinearSeries.ofScalarsSum_zero, constantCoeff] using hf0
    rw [hF0, Complex.log_one]
    simp only [Λ]
    rw [tsum_eq_single 0 fun n hn ↦ by simp [hn]]
    simpa [constantCoeff] using constantCoeff_logOf hf0
  have heq := Metric.isOpen_eball.eqOn_of_deriv_eq (convex_eball (0 : ℂ) r).isPreconnected
    hΛd hLd hderiv (Metric.mem_eball_self hr0) h0
  have hsum := (summable_norm_coeff_logOf_mul_pow_of_zeroFree f hf0 hr hne hz).of_norm.hasSum
  have hz' : ∑' n : ℕ, coeff n (logOf f) * z ^ n = Complex.log (F z) :=
    heq (by simpa only [U, Metric.mem_eball, edist_zero_right] using hz)
  rwa [hz'] at hsum

end PowerSeries
