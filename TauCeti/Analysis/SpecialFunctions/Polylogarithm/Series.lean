/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Open-disc power series of principal polylogarithms

On the open unit disc `{z : ℂ | ‖z‖ < 1}`, the principal polylogarithm `TauCeti.Polylog.polylog n`
is represented in every integer weight `n : ℤ` by the convergent power series
`∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`. Convergence is absolute on the open disc, uniform on every
closed subdisc of radius `r < 1`, and locally uniform on `Metric.ball 0 1`.

Packaging the coefficients into a `FormalMultilinearSeries` gives `TauCeti.Polylog.polylogSeries n`,
which has exact radius of convergence `1` and represents `polylog n` on `Metric.eball 0 1`. Reading
off the linear term shows that `polylog n` has complex derivative `1` at `0` in every integer
weight, completing the derivative formula on the full principal domain `ℂ ∖ [1, ∞)`.

## Main declarations

* `TauCeti.Polylog.summable_norm_polylog_series`, `TauCeti.Polylog.summable_polylog_series`:
  absolute summability of `k ↦ z ^ (k + 1) / (k + 1) ^ n` for `‖z‖ < 1`.
* `TauCeti.Polylog.hasSum_polylog`, `TauCeti.Polylog.polylog_eq_tsum`: the disc-series
  identification `HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z)` for `‖z‖ < 1`.
* `TauCeti.Polylog.tendstoUniformlyOn_polylog_series`,
  `TauCeti.Polylog.tendstoLocallyUniformlyOn_polylog_series`: uniform convergence on closed
  subdiscs and locally uniform convergence on the open unit disc.
* `TauCeti.Polylog.polylogSeries`, `TauCeti.Polylog.radius_polylogSeries`,
  `TauCeti.Polylog.hasFPowerSeriesOnBall_polylog`: the formal power series of `polylog n` at `0`
  and its radius of convergence `1`.
* `TauCeti.Polylog.hasDerivAt_polylog_zero`, `TauCeti.Polylog.deriv_polylog_zero`: the complex
  derivative of `polylog n` at `0` equals `1` in every integer weight.
* `TauCeti.Polylog.hasDerivAt_polylog`, `TauCeti.Polylog.deriv_polylog`: unified derivative of
  `polylog n` at every point of `{z : ℂ | 1 - z ∈ Complex.slitPlane}`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (1)–(3), p. 50.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, introduction, p. 5.
-/

public section

open Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Polylog

/-! ### Absolute summability and geometric-polynomial majorants -/

private lemma norm_seriesTerm_le (n : ℤ) {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (k : ℕ) :
    ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖ ≤ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ (k + 1) := by
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hexp : -n ≤ ((-n).toNat : ℤ) := by omega
  have hzpow : (((k + 1 : ℕ) : ℝ) ^ n)⁻¹ ≤ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat := by
    rw [← zpow_neg, ← zpow_natCast]
    exact zpow_le_zpow_right₀ hk1 hexp
  have hpow : ‖z‖ ^ (k + 1) ≤ r ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg z) hz (k + 1)
  have hnorm_denom : ‖(k + 1 : ℂ) ^ n‖ = ((k + 1 : ℕ) : ℝ) ^ n := by
    rw [norm_zpow, ← Nat.cast_add_one, Complex.norm_natCast]
  calc ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖
      = (((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * ‖z‖ ^ (k + 1) := by
        rw [norm_div, norm_pow, hnorm_denom, div_eq_inv_mul]
    _ ≤ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ (k + 1) := by
        gcongr

private lemma summable_majorant (n : ℤ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ (k + 1) :=
  (summable_nat_add_iff (f := fun k : ℕ ↦ (k : ℝ) ^ (-n).toNat * r ^ k) 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one (-n).toNat (by rwa [Real.norm_of_nonneg hr0]))

/-- For every integer weight `n` and `‖z‖ < 1`, the polylogarithm series converges absolutely. -/
theorem summable_norm_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_seriesTerm_le n le_rfl)
    (summable_majorant n (norm_nonneg z) hz)

/-- For every integer weight `n` and `‖z‖ < 1`, the polylogarithm power series is summable. -/
theorem summable_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (summable_norm_polylog_series n hz).of_norm

/-! ### Termwise calculus of the disc series and identification with `polylog` -/

private lemma hasDerivAt_seriesSum_succ (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (n + 1))
      (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ n) z := by
  set r : ℝ := (‖z‖ + 1) / 2
  have hr_gt : ‖z‖ < r := by grind
  have hr1 : r < 1 := by grind
  have hr0 : 0 < r := (norm_nonneg z).trans_lt hr_gt
  have hu : Summable fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ k := by
    refine ((summable_majorant n hr0.le hr1).mul_left r⁻¹).congr fun k ↦ ?_
    rw [pow_succ]
    field_simp [hr0.ne']
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (k : ℕ) (w : ℂ) ↦ w ^ (k + 1) / (k + 1 : ℂ) ^ (n + 1))
    (g' := fun (k : ℕ) (w : ℂ) ↦ w ^ k / (k + 1 : ℂ) ^ n)
    (t := Metric.ball (0 : ℂ) r) (y₀ := 0)
    hu Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected (fun k y _ ↦ ?_)
    (fun k y hy ↦ ?_) (Metric.mem_ball_self hr0)
    (summable_zero.congr fun _ ↦ by simp) (by simpa using hr_gt)
  · have hk0 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    refine ((hasDerivAt_pow (k + 1) y).div_const ((k + 1 : ℂ) ^ (n + 1))).congr_deriv ?_
    rw [Nat.cast_add, Nat.cast_one, zpow_add_one₀ hk0, mul_comm ((k + 1 : ℂ) ^ n)]
    exact mul_div_mul_left (y ^ k) ((k + 1 : ℂ) ^ n) hk0
  · have hyr : ‖y‖ ≤ r := (by simpa using hy : ‖y‖ < r).le
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hexp : -n ≤ ((-n).toNat : ℤ) := by omega
    have hzpow : (((k + 1 : ℕ) : ℝ) ^ n)⁻¹ ≤ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat := by
      rw [← zpow_neg, ← zpow_natCast]
      exact zpow_le_zpow_right₀ hk1 hexp
    have hpow : ‖y‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg y) hyr k
    have hnorm_denom : ‖(k + 1 : ℂ) ^ n‖ = ((k + 1 : ℕ) : ℝ) ^ n := by
      rw [norm_zpow, ← Nat.cast_add_one, Complex.norm_natCast]
    calc ‖y ^ k / (k + 1 : ℂ) ^ n‖
        = (((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * ‖y‖ ^ k := by
          rw [norm_div, norm_pow, hnorm_denom, div_eq_inv_mul]
      _ ≤ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ k := by gcongr

private lemma mul_deriv_seriesSum_succ (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (n + 1)) z =
      ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n := by
  rw [(hasDerivAt_seriesSum_succ n hz).deriv, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  rw [pow_succ', mul_div_assoc']

private lemma hasDerivAt_seriesSum_zero (n : ℤ) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n) 1 0 := by
  have h := hasDerivAt_seriesSum_succ (n - 1) (z := 0) (by simp)
  rw [sub_add_cancel] at h
  refine h.congr_deriv ?_
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

private lemma polylog_zero_weight_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    polylog 0 z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ (0 : ℤ) := by
  have hgeom : ∑' k : ℕ, z ^ k = (1 - z)⁻¹ := (hasSum_geometric_of_norm_lt_one hz).tsum_eq
  calc polylog 0 z
      = z * (1 - z)⁻¹ := by rw [polylog_zero_weight, div_eq_mul_inv]
    _ = z * ∑' k : ℕ, z ^ k := by rw [hgeom]
    _ = ∑' k : ℕ, z * z ^ k := tsum_mul_left.symm
    _ = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ (0 : ℤ) := by
        refine tsum_congr fun k ↦ ?_
        simp [pow_succ']

private lemma polylog_neg_nat_eq_tsum (r : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog (-(r : ℤ)) z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ)) := by
  induction r generalizing z with
  | zero => simpa using polylog_zero_weight_eq_tsum hz
  | succ r ih =>
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz
    have heq : polylog (-(r : ℤ)) =ᶠ[𝓝 z]
        fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ)) :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz_ball)
        fun w hw ↦ ih (by simpa using hw)
    have hrec := mul_deriv_seriesSum_succ (-((r + 1 : ℕ) : ℤ)) hz
    have hcast : (-((r + 1 : ℕ) : ℤ)) + 1 = -(r : ℤ) := by omega
    rw [hcast] at hrec
    rw [polylog_neg_nat_succ, heq.deriv_eq, hrec]

private lemma polylog_nat_eq_tsum (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog m z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ (m : ℤ) := by
  induction m generalizing z with
  | zero => simpa using polylog_zero_weight_eq_tsum hz
  | succ m ih =>
    set S : ℂ → ℂ := fun w ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ ((m + 1 : ℕ) : ℤ)
    have hf_diff : DifferentiableOn ℂ (polylog (m + 1 : ℕ)) (Metric.ball 0 1) := by
      intro w hw
      have hmem : 1 - w ∈ Complex.slitPlane :=
        sub_eq_add_neg (1 : ℂ) w ▸ Complex.mem_slitPlane_of_norm_lt_one (by simpa using hw)
      exact (differentiableAt_polylog _ hmem).differentiableWithinAt
    have hS_diff : DifferentiableOn ℂ S (Metric.ball 0 1) := by
      intro w hw
      have hw' : ‖w‖ < 1 := by simpa using hw
      have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      simpa [S, hcast] using
        (hasDerivAt_seriesSum_succ (m : ℤ) hw').differentiableAt.differentiableWithinAt
    have hderiv_ne : ∀ w ∈ Metric.ball (0 : ℂ) 1, w ≠ 0 →
        deriv (polylog (m + 1 : ℕ)) w = deriv S w := by
      intro w hw hw0
      have hw' : ‖w‖ < 1 := by simpa using hw
      have hmem : 1 - w ∈ Complex.slitPlane :=
        sub_eq_add_neg (1 : ℂ) w ▸ Complex.mem_slitPlane_of_norm_lt_one (by simpa using hw')
      have h1 := deriv_polylog_of_ne_zero (m + 1 : ℕ) hmem hw0
      have hsub : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
      rw [h1, hsub, ih hw']
      have hrec := mul_deriv_seriesSum_succ (m : ℤ) hw'
      have hcast : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at hrec
      exact (eq_div_of_mul_eq hw0 (by simpa [S, mul_comm] using hrec)).symm
    have hderiv_eq : Set.EqOn (deriv (polylog (m + 1 : ℕ))) (deriv S) (Metric.ball 0 1) := by
      intro w hw
      rcases eq_or_ne w 0 with rfl | hw0
      · have hc1 : ContinuousAt (deriv (polylog (m + 1 : ℕ))) 0 :=
          ((hf_diff.analyticOnNhd Metric.isOpen_ball) 0
            (Metric.mem_ball_self zero_lt_one)).deriv.continuousAt
        have hc2 : ContinuousAt (deriv S) 0 :=
          ((hS_diff.analyticOnNhd Metric.isOpen_ball) 0
            (Metric.mem_ball_self zero_lt_one)).deriv.continuousAt
        have hev : deriv (polylog (m + 1 : ℕ)) =ᶠ[𝓝[≠] (0 : ℂ)] deriv S := by
          filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one),
            self_mem_nhdsWithin] with u hu hu0
          exact hderiv_ne u hu hu0
        exact tendsto_nhds_unique_of_eventuallyEq
          (hc1.tendsto.mono_left nhdsWithin_le_nhds)
          (hc2.tendsto.mono_left nhdsWithin_le_nhds) hev
      · exact hderiv_ne w hw hw0
    have h0 : polylog (m + 1 : ℕ) 0 = S 0 := by simp [S]
    exact Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) 1).isPreconnected
      hf_diff hS_diff hderiv_eq (Metric.mem_ball_self zero_lt_one) h0 (by simpa using hz)

/-- On the open unit disc `‖z‖ < 1`, `polylog n z` equals the sum of its power series
`∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n` in every integer weight `n : ℤ`. -/
theorem polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n := by
  cases n with
  | ofNat m => exact polylog_nat_eq_tsum m hz
  | negSucc r => exact polylog_neg_nat_eq_tsum (r + 1) hz

/-- Disc-series representation of `polylog n` in every integer weight `n : ℤ` on `‖z‖ < 1`. -/
theorem hasSum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  rw [polylog_eq_tsum n hz]
  exact (summable_polylog_series n hz).hasSum

/-- Disc-series representation of `polylog` in natural weight `n : ℕ` on `‖z‖ < 1`, written with
natural-exponent powers `(k + 1) ^ n`. -/
theorem hasSum_polylog_nat (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  simpa using hasSum_polylog (n : ℤ) hz

/-! ### Uniform and locally uniform convergence on the disc -/

/-- On every closed subdisc `Metric.closedBall 0 r` with `r < 1`, the partial sums of the
polylogarithm power series converge uniformly to `polylog n`. -/
theorem tendstoUniformlyOn_polylog_series (n : ℤ) {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn (fun (N : ℕ) (z : ℂ) ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (Metric.closedBall 0 r) := by
  set r' : ℝ := max r 0
  have hr'0 : 0 ≤ r' := le_max_right r 0
  have hr'1 : r' < 1 := max_lt hr zero_lt_one
  have hunif := tendstoUniformlyOn_tsum_nat (summable_majorant n hr'0 hr'1)
    (s := Metric.closedBall (0 : ℂ) r') fun k z hz ↦
      norm_seriesTerm_le n (by simpa using hz) k
  refine (hunif.mono (Metric.closedBall_subset_closedBall (le_max_left r 0))).congr_right ?_
  intro z hz
  exact (polylog_eq_tsum n ((by simpa using hz : ‖z‖ ≤ r).trans_lt hr)).symm

/-- On every closed subdisc `Metric.closedBall 0 r` with `r < 1`, the polylogarithm series sums
uniformly to `polylog n`. -/
theorem hasSumUniformlyOn_polylog_closedBall (n : ℤ) {r : ℝ} (hr : r < 1) :
    HasSumUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) (Metric.closedBall 0 r) := by
  set r' : ℝ := max r 0
  have hr'0 : 0 ≤ r' := le_max_right r 0
  have hr'1 : r' < 1 := max_lt hr zero_lt_one
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  have hunif := tendstoUniformlyOn_tsum (summable_majorant n hr'0 hr'1)
    (s := Metric.closedBall (0 : ℂ) r') fun k z hz ↦
      norm_seriesTerm_le n (by simpa using hz) k
  refine (hunif.mono (Metric.closedBall_subset_closedBall (le_max_left r 0))).congr_right ?_
  intro z hz
  exact (polylog_eq_tsum n ((by simpa using hz : ‖z‖ ≤ r).trans_lt hr)).symm

/-- On the open unit disc `Metric.ball 0 1`, the partial sums of the polylogarithm power series
converge locally uniformly to `polylog n`. -/
theorem tendstoLocallyUniformlyOn_polylog_series (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (z : ℂ) ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (Metric.ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨z₀, hz₀K, hz₀max⟩ := hKc.exists_isMaxOn hKne continuous_norm.continuousOn
    have hz₀1 : ‖z₀‖ < 1 := by simpa using hK hz₀K
    exact (tendstoUniformlyOn_polylog_series n hz₀1).mono fun z hz ↦ by
      simpa using hz₀max hz

/-- On the open unit disc `Metric.ball 0 1`, the polylogarithm series sums locally uniformly to
`polylog n`. -/
theorem hasSumLocallyUniformlyOn_polylog_ball (n : ℤ) :
    HasSumLocallyUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) (Metric.ball 0 1) := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨z₀, hz₀K, hz₀max⟩ := hKc.exists_isMaxOn hKne continuous_norm.continuousOn
    have hz₀1 : ‖z₀‖ < 1 := by simpa using hK hz₀K
    exact (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp
      (hasSumUniformlyOn_polylog_closedBall n hz₀1)).mono fun z hz ↦ by
      simpa using hz₀max hz

/-! ### Formal power series at zero and radius of convergence -/

/-- The formal multilinear power series of `polylog n` at `0`, with scalar coefficients `0` in
degree `0` and `1 / k ^ n` in positive degree `k`. -/
noncomputable def polylogSeries (n : ℤ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun k : ℕ ↦ if k = 0 then 0 else ((k : ℂ) ^ n)⁻¹

/-- Definitional expansion of `polylogSeries n` via `FormalMultilinearSeries.ofScalars`. -/
theorem polylogSeries_def (n : ℤ) :
    polylogSeries n =
      FormalMultilinearSeries.ofScalars ℂ fun k : ℕ ↦ if k = 0 then 0 else ((k : ℂ) ^ n)⁻¹ :=
  (rfl)

/-- The `k`-th scalar coefficient of `polylogSeries n` is `0` at `k = 0` and `((k : ℂ) ^ n)⁻¹`
for `k ≠ 0`. -/
theorem coeff_polylogSeries (n : ℤ) (k : ℕ) :
    (polylogSeries n).coeff k = if k = 0 then 0 else ((k : ℂ) ^ n)⁻¹ := by
  simp [polylogSeries_def]

/-- The constant coefficient of `polylogSeries n` vanishes. -/
@[simp] theorem coeff_polylogSeries_zero (n : ℤ) :
    (polylogSeries n).coeff 0 = 0 := by
  simp [coeff_polylogSeries]

/-- In positive degree `k + 1`, the scalar coefficient of `polylogSeries n` is `((k + 1) ^ n)⁻¹`. -/
@[simp] theorem coeff_polylogSeries_succ (n : ℤ) (k : ℕ) :
    (polylogSeries n).coeff (k + 1) = ((k + 1 : ℂ) ^ n)⁻¹ := by
  simp [coeff_polylogSeries]

/-- Evaluating `polylogSeries n` in degree `0` gives `0`. -/
theorem polylogSeries_zero_apply (n : ℤ) (v : Fin 0 → ℂ) :
    polylogSeries n 0 v = 0 := by
  simp

/-- Evaluating `polylogSeries n` in degree `k + 1` at the constant vector `fun _ ↦ z` gives
`z ^ (k + 1) / (k + 1) ^ n`. -/
theorem polylogSeries_succ_apply_const (n : ℤ) (k : ℕ) (z : ℂ) :
    polylogSeries n (k + 1) (fun _ ↦ z) = z ^ (k + 1) / (k + 1 : ℂ) ^ n := by
  rw [polylogSeries_def, FormalMultilinearSeries.ofScalars_apply_eq]
  simp [div_eq_inv_mul]

private lemma one_le_radius_polylogSeries (n : ℤ) :
    (1 : ℝ≥0∞) ≤ (polylogSeries n).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r _ hr1 ↦ ?_
  have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  rw [← summable_nat_add_iff (f := fun k : ℕ ↦ ‖polylogSeries n k‖ * (r : ℝ) ^ k) 1]
  refine (summable_norm_polylog_series n (z := (r : ℂ)) (by simpa using hr1')).congr fun k ↦ ?_
  rw [polylogSeries_def, FormalMultilinearSeries.ofScalars_norm]
  simp [div_eq_inv_mul]

/-- In every integer weight `n : ℤ`, `polylogSeries n` has exact radius of convergence `1`. -/
@[simp] theorem radius_polylogSeries (n : ℤ) :
    (polylogSeries n).radius = 1 := by
  refine le_antisymm ?_ (one_le_radius_polylogSeries n)
  by_contra! hgt
  obtain ⟨r, hr1, hrrad⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hgt
  have hr1' : (1 : ℝ) < r := by exact_mod_cast hr1
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr1'
  have hsum : Summable fun k : ℕ ↦ ‖polylogSeries n (k + 1)‖ * (r : ℝ) ^ (k + 1) :=
    (summable_nat_add_iff (f := fun k : ℕ ↦ ‖polylogSeries n k‖ * (r : ℝ) ^ k) 1).mpr
      ((polylogSeries n).summable_norm_mul_pow hrrad)
  have htend0 : Tendsto (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * (r : ℝ) ^ (k + 1))
      atTop (𝓝 0) := by
    refine hsum.tendsto_atTop_zero.congr fun k ↦ ?_
    rw [polylogSeries_def, FormalMultilinearSeries.ofScalars_norm]
    simp only [Nat.succ_ne_zero, ↓reduceIte, norm_inv, norm_zpow, Complex.norm_natCast]
  have hrinv : ‖(r : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
    exact inv_lt_one_of_one_lt₀ hr1'
  have hdual : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ n.toNat * ((r : ℝ)⁻¹) ^ (k + 1))
      atTop (𝓝 0) :=
    ((summable_nat_add_iff (f := fun k : ℕ ↦ (k : ℝ) ^ n.toNat * ((r : ℝ)⁻¹) ^ k) 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one n.toNat hrinv)).tendsto_atTop_zero
  have hprod0 : Tendsto
      (fun k : ℕ ↦ ((((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * (r : ℝ) ^ (k + 1)) *
        (((k + 1 : ℕ) : ℝ) ^ n.toNat * ((r : ℝ)⁻¹) ^ (k + 1)))
      atTop (𝓝 0) := by
    simpa using htend0.mul hdual
  have hge1 : ∀ k : ℕ, (1 : ℝ) ≤
      ((((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * (r : ℝ) ^ (k + 1)) *
        (((k + 1 : ℕ) : ℝ) ^ n.toNat * ((r : ℝ)⁻¹) ^ (k + 1)) := by
    intro k
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hpow_cancel : (r : ℝ) ^ (k + 1) * ((r : ℝ)⁻¹) ^ (k + 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hr0.ne', one_pow]
    calc (1 : ℝ)
        = ((k + 1 : ℕ) : ℝ) ^ (0 : ℤ) := (zpow_zero _).symm
      _ ≤ ((k + 1 : ℕ) : ℝ) ^ ((n.toNat : ℤ) - n) := zpow_le_zpow_right₀ hk1 (by omega)
      _ = (((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * ((k + 1 : ℕ) : ℝ) ^ n.toNat := by
          rw [sub_eq_neg_add, zpow_add₀ (by positivity), zpow_neg, zpow_natCast]
      _ = ((((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * (r : ℝ) ^ (k + 1)) *
            (((k + 1 : ℕ) : ℝ) ^ n.toNat * ((r : ℝ)⁻¹) ^ (k + 1)) := by
          calc (((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * ((k + 1 : ℕ) : ℝ) ^ n.toNat
              = ((((k + 1 : ℕ) : ℝ) ^ n)⁻¹ * ((k + 1 : ℕ) : ℝ) ^ n.toNat) *
                  ((r : ℝ) ^ (k + 1) * ((r : ℝ)⁻¹) ^ (k + 1)) := by rw [hpow_cancel, mul_one]
            _ = _ := by ring
  have h1le0 : (1 : ℝ) ≤ 0 := ge_of_tendsto hprod0 (Eventually.of_forall hge1)
  linarith

/-- On `Metric.eball 0 1`, `polylog n` is represented by its formal power series `polylogSeries n`
at `0`. -/
theorem hasFPowerSeriesOnBall_polylog (n : ℤ) :
    HasFPowerSeriesOnBall (polylog n) (polylogSeries n) 0 1 where
  r_le := one_le_radius_polylogSeries n
  r_pos := zero_lt_one
  hasSum := by
    intro z hz
    have hz' : ‖z‖ < 1 := by
      rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one] at hz
    rw [zero_add, ← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, polylogSeries_zero_apply, sub_zero]
    exact (hasSum_polylog n hz').congr_fun fun k ↦ polylogSeries_succ_apply_const n k z

/-- At `0`, `polylog n` has formal power series `polylogSeries n` in every integer weight
`n : ℤ`. -/
theorem hasFPowerSeriesAt_polylog_zero (n : ℤ) :
    HasFPowerSeriesAt (polylog n) (polylogSeries n) 0 :=
  (hasFPowerSeriesOnBall_polylog n).hasFPowerSeriesAt

/-! ### Derivative at zero and unified derivative on the principal domain -/

/-- Every integer-weight polylogarithm has complex derivative `1` at `0`. -/
theorem hasDerivAt_polylog_zero (n : ℤ) :
    HasDerivAt (polylog n) 1 0 := by
  have heq : polylog n =ᶠ[𝓝 (0 : ℂ)] fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
      fun w hw ↦ polylog_eq_tsum n (by simpa using hw)
  exact (hasDerivAt_seriesSum_zero n).congr_of_eventuallyEq heq

/-- The complex derivative of `polylog n` at `0` equals `1` in every integer weight `n : ℤ`. -/
@[simp] theorem deriv_polylog_zero (n : ℤ) :
    deriv (polylog n) 0 = 1 :=
  (hasDerivAt_polylog_zero n).deriv

/-- Unified `HasDerivAt` formula for `polylog n` across the entire principal domain `ℂ ∖ [1, ∞)`:
its complex derivative is `1` at `z = 0` and `polylog (n - 1) z / z` for `z ≠ 0`. -/
theorem hasDerivAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog n) (if z = 0 then 1 else polylog (n - 1) z / z) z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp only [↓reduceIte]
    exact hasDerivAt_polylog_zero n
  · simp only [hz0, ↓reduceIte]
    exact hasDerivAt_polylog_of_ne_zero n hz hz0

/-- Unified complex derivative of `polylog n` on the principal domain `ℂ ∖ [1, ∞)`. -/
theorem deriv_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    deriv (polylog n) z = if z = 0 then 1 else polylog (n - 1) z / z :=
  (hasDerivAt_polylog n hz).deriv

/-! ### Special-value series checks -/

/-- At `z = 1 / 2`, the weight-zero disc series `∑_{k ≥ 0} (1 / 2) ^ (k + 1)` sums to `1`,
matching `polylog 0 (1 / 2) = 1`. -/
theorem hasSum_polylog_zero_weight_half :
    HasSum (fun k : ℕ ↦ (1 / 2 : ℂ) ^ (k + 1)) 1 := by
  have h := hasSum_polylog 0 (z := (1 / 2 : ℂ)) (by norm_num)
  rw [polylog_zero_weight_half] at h
  exact h.congr_fun fun k ↦ by simp

/-- At `z = 1 / 2`, the weight-`(-1)` disc series `∑_{k ≥ 0} (k + 1) * (1 / 2) ^ (k + 1)` sums to
`2`, matching `polylog (-1) (1 / 2) = 2`. -/
theorem hasSum_polylog_neg_one_half :
    HasSum (fun k : ℕ ↦ (k + 1 : ℂ) * (1 / 2 : ℂ) ^ (k + 1)) 2 := by
  have h := hasSum_polylog (-1) (z := (1 / 2 : ℂ)) (by norm_num)
  rw [polylog_neg_one_half] at h
  refine h.congr_fun fun k ↦ ?_
  rw [zpow_neg_one, div_inv_eq_mul, mul_comm]

end TauCeti.Polylog
