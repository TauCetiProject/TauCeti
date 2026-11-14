/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Integrals.Log

/-!
# The unit-disc power series of integer-weight polylogarithms

On the open unit disc `‖z‖ < 1`, the principal polylogarithm `TauCeti.Polylog.polylog n z` of any
integer weight `n : ℤ` expands as the power series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`, with
absolute and locally uniform convergence on `Metric.ball 0 1` and uniform convergence on every
closed disc `Metric.closedBall 0 r` of radius `r < 1`.

For weights `n ≥ 2` we expand `-Complex.log (1 - t * z)` inside the defining radial integral,
justify termwise integration by dominated convergence against
`|Real.log t| ^ (n - 2) * ‖z‖ ^ (j + 1)`, and evaluate each logarithmic moment via
`TauCeti.integral_pow_mul_neg_log_pow`. Weight `1` is `TauCeti.Polylog.hasSum_polylog_one`,
weight `0` is the geometric series, and negative weights follow inductively by applying the Euler
operator `z * d/dz` termwise to the series. From the termwise derivative we read off
`deriv (polylog n) 0 = 1` for every `n : ℤ`.

## Main declarations

* `TauCeti.Polylog.summable_norm_polylogSeries`, `TauCeti.Polylog.summable_polylogSeries`:
  absolute and unconditional summability of `k ↦ z ^ (k + 1) / (k + 1) ^ n` for `‖z‖ < 1`.
* `TauCeti.Polylog.hasSum_polylog`, `TauCeti.Polylog.polylog_eq_tsum`: the disc-series
  identification on `‖z‖ < 1` in every integer weight.
* `TauCeti.Polylog.hasSumUniformlyOn_polylog_closedBall`,
  `TauCeti.Polylog.hasSumLocallyUniformlyOn_polylog_ball`: uniform convergence on closed subdiscs
  `r < 1` and locally uniform convergence on `Metric.ball 0 1`.
* `TauCeti.Polylog.hasDerivAt_polylog_of_norm_lt_one`, `TauCeti.Polylog.hasSum_deriv_polylog`:
  termwise differentiation of `polylog n` on `‖z‖ < 1`.
* `TauCeti.Polylog.hasDerivAt_polylog_zero`, `TauCeti.Polylog.deriv_polylog_zero`:
  `polylog n` has complex derivative `1` at `0` for every `n : ℤ`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (1), p. 50.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, introduction, p. 5.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.Polylog

/-- Shifted polynomial-times-geometric series `k ↦ (k + 1) ^ m * r ^ (k + 1)` are summable for
`0 ≤ r < 1`. -/
private lemma summable_nat_add_one_pow_mul_geometric (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ ↦ (k + 1 : ℝ) ^ m * r ^ (k + 1) := by
  have h := (summable_nat_add_iff 1).mpr
    (summable_norm_pow_mul_geometric_of_norm_lt_one m (r := r) (by rwa [Real.norm_of_nonneg hr0]))
  refine h.congr fun k ↦ ?_
  rw [Nat.cast_add, Nat.cast_one, norm_mul, norm_pow, norm_pow, Real.norm_of_nonneg hr0,
    Real.norm_of_nonneg (by positivity)]

/-- For `k : ℕ` and `n : ℤ`, `(k + 1) ^ (-n)` is bounded above by `(k + 1) ^ (-n).toNat`. -/
private lemma nat_add_one_zpow_neg_le_pow_toNat (n : ℤ) (k : ℕ) :
    (k + 1 : ℝ) ^ (-n) ≤ (k + 1 : ℝ) ^ (-n).toNat := by
  have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ k.zero_le
  rcases le_or_gt 0 (-n) with hn | hn
  · rw [← zpow_natCast, Int.toNat_of_nonneg hn]
  · rw [Int.toNat_of_nonpos hn.le, pow_zero]
    exact zpow_le_one_of_nonpos₀ hk1 hn.le

/-- Uniform polynomial-times-geometric bound on the `k`-th polylogarithm series term on a closed
disc of radius `r ≥ 0`. -/
private lemma norm_polylogSeriesTerm_le (n : ℤ) (k : ℕ) {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖ ≤ (k + 1 : ℝ) ^ (-n).toNat * r ^ (k + 1) := by
  have hnorm_base : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)
  rw [norm_div, norm_pow, norm_zpow, hnorm_base, div_eq_inv_mul, ← zpow_neg]
  exact mul_le_mul (nat_add_one_zpow_neg_le_pow_toNat n k)
    (pow_le_pow_left₀ (norm_nonneg z) hz (k + 1)) (by positivity) (by positivity)

/-- On the open unit disc, the polylogarithm series `∑ k, z ^ (k + 1) / (k + 1) ^ n` converges
absolutely in every integer weight. -/
theorem summable_norm_polylogSeries (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ norm_polylogSeriesTerm_le n k le_rfl)
    (summable_nat_add_one_pow_mul_geometric (-n).toNat (norm_nonneg z) hz)

/-- On the open unit disc, the polylogarithm series converges in every integer weight. -/
theorem summable_polylogSeries (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (summable_norm_polylogSeries n hz).of_norm

/-- Summability of the termwise-differentiated polylogarithm series on `‖z‖ < 1`. -/
private lemma summable_norm_deriv_polylogSeries (n : ℤ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ ↦ (k + 1 : ℝ) ^ ((-n).toNat + 1) * r ^ k := by
  rcases eq_or_lt_of_le hr0 with rfl | hrpos
  · refine summable_of_ne_finset_zero (s := {0}) fun k hk ↦ ?_
    have hk0 : k ≠ 0 := by simpa using hk
    simp [zero_pow hk0]
  · refine ((summable_nat_add_one_pow_mul_geometric ((-n).toNat + 1) hr0 hr1).mul_left r⁻¹).congr
      fun k ↦ ?_
    rw [pow_succ' r k]
    field_simp [hrpos.ne']

/-- Uniform bound on the `k`-th differentiated polylogarithm series term on `‖z‖ ≤ r`. -/
private lemma norm_deriv_polylogSeriesTerm_le (n : ℤ) (k : ℕ) {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    ‖(k + 1 : ℂ) * z ^ k / (k + 1 : ℂ) ^ n‖ ≤ (k + 1 : ℝ) ^ ((-n).toNat + 1) * r ^ k := by
  have hnorm_k : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)
  rw [norm_div, norm_mul, norm_pow, norm_zpow, hnorm_k, div_eq_mul_inv, ← zpow_neg]
  have hpow : ‖z‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg z) hz k
  calc (k + 1 : ℝ) * ‖z‖ ^ k * (k + 1 : ℝ) ^ (-n)
      ≤ (k + 1 : ℝ) * r ^ k * (k + 1 : ℝ) ^ (-n).toNat :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
          (nat_add_one_zpow_neg_le_pow_toNat n k) (by positivity)
          (mul_nonneg (by positivity) (pow_nonneg ((norm_nonneg z).trans hz) k))
    _ = (k + 1 : ℝ) ^ ((-n).toNat + 1) * r ^ k := by rw [pow_succ]; ring

/-- Termwise differentiation of the polylogarithm power series on `‖z‖ < 1`. -/
private lemma hasDerivAt_tsum_polylogSeries (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (∑' k : ℕ, (k + 1 : ℂ) * z ^ k / (k + 1 : ℂ) ^ n) z := by
  set r : ℝ := (‖z‖ + 1) / 2 with hr_def
  have hr0 : 0 < r := by linarith [norm_nonneg z]
  have hr1 : r < 1 := by linarith
  have hzr : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hunif : TendstoUniformlyOn
      (fun (s : Finset ℕ) (w : ℂ) ↦ ∑ k ∈ s, (k + 1 : ℂ) * w ^ k / (k + 1 : ℂ) ^ n)
      (fun w : ℂ ↦ ∑' k : ℕ, (k + 1 : ℂ) * w ^ k / (k + 1 : ℂ) ^ n) atTop (Metric.ball 0 r) :=
    tendstoUniformlyOn_tsum (summable_norm_deriv_polylogSeries n hr0.le hr1) fun k w hw ↦
      norm_deriv_polylogSeriesTerm_le n k (mem_ball_zero_iff.mp hw).le
  refine hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hunif
    (Eventually.of_forall fun s w _ ↦ HasDerivAt.fun_sum fun k _ ↦ ?_)
    (fun w hw ↦ (summable_polylogSeries n ((mem_ball_zero_iff.mp hw).trans hr1)).hasSum) hzr
  simpa [Nat.add_sub_cancel] using (hasDerivAt_pow (k + 1) w).div_const ((k + 1 : ℂ) ^ n)

/-- Applying the Euler operator `z * d/dz` to the weight-`n` power series lowers the weight
by `1`. -/
private lemma mul_deriv_tsum_polylogSeries (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n) z =
      ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ (n - 1) := by
  rw [(hasDerivAt_tsum_polylogSeries n hz).deriv, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hzpow : (k + 1 : ℂ) ^ n = (k + 1 : ℂ) ^ (n - 1) * (k + 1 : ℂ) := by
    rw [← zpow_add_one₀ hk, sub_add_cancel]
  rw [hzpow, mul_div_assoc', ← mul_assoc, mul_comm z (k + 1 : ℂ), mul_assoc, ← pow_succ',
    mul_comm (k + 1 : ℂ), mul_div_mul_right _ _ hk]

/-- Pointwise norm bound on the `j`-th Taylor integrand of `polylog (k + 2)` on `(0, 1]`. -/
private lemma norm_radialSeriesTerm_le (k j : ℕ) {z : ℂ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖((-Real.log t : ℝ) : ℂ) ^ k * (((t : ℂ) * z) ^ (j + 1) / (j + 1 : ℂ)) / (t : ℂ)‖ ≤
      |Real.log t| ^ k * ‖z‖ ^ (j + 1) := by
  have ht0 : 0 < t := ht.1
  have hj1 : (1 : ℝ) ≤ (j + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ j.zero_le
  have hnorm_j : ‖(j + 1 : ℂ)‖ = (j + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (j + 1)
  rw [norm_div, norm_mul, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_neg, Complex.norm_real, Real.norm_of_nonneg ht0.le, hnorm_j]
  have hpow : (t * ‖z‖) ^ (j + 1) / (j + 1 : ℝ) / t ≤ ‖z‖ ^ (j + 1) := by
    rw [div_le_iff₀ ht0, div_le_iff₀ (by positivity), mul_pow, pow_succ t j]
    calc t ^ j * t * ‖z‖ ^ (j + 1)
        = t ^ j * (‖z‖ ^ (j + 1) * t) := by ring
      _ ≤ (j + 1 : ℝ) * (‖z‖ ^ (j + 1) * t) :=
          mul_le_mul_of_nonneg_right ((pow_le_one₀ ht0.le ht.2).trans hj1) (by positivity)
      _ = ‖z‖ ^ (j + 1) * t * (j + 1 : ℝ) := by ring
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Evaluating the `j`-th radial moment integral in `polylog (k + 2)`. -/
private lemma integral_radialSeriesTerm (k j : ℕ) (z : ℂ) :
    (k.factorial : ℂ)⁻¹ *
        (∫ t : ℝ in 0..1,
          ((-Real.log t : ℝ) : ℂ) ^ k * (((t : ℂ) * z) ^ (j + 1) / (j + 1 : ℂ)) / (t : ℂ)) =
      z ^ (j + 1) / (j + 1 : ℂ) ^ ((k + 2 : ℕ) : ℤ) := by
  have hcongr :
      (∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (((t : ℂ) * z) ^ (j + 1) / (j + 1 : ℂ)) / (t : ℂ)) =
      ∫ t : ℝ in 0..1,
        (z ^ (j + 1) / (j + 1 : ℂ)) * (((t ^ j * (-Real.log t) ^ k : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    push_cast
    rw [mul_pow, pow_succ (t : ℂ) j]
    field_simp [ht0]
  rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_pow_mul_neg_log_pow j k, zpow_natCast, show k + 2 = (k + 1) + 1 from rfl, pow_succ]
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hj : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  push_cast
  field_simp [hfac, hj]
  ring

/-- Disc-series representation in weights at least two, by termwise radial integration. -/
private lemma hasSum_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ ↦ z ^ (j + 1) / (j + 1 : ℂ) ^ ((k + 2 : ℕ) : ℤ))
      (polylog (k + 2 : ℕ) z) := by
  let F : ℕ → ℝ → ℂ := fun j t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (((t : ℂ) * z) ^ (j + 1) / (j + 1 : ℂ)) / (t : ℂ)
  let bound : ℕ → ℝ → ℝ := fun j t ↦ |Real.log t| ^ k * ‖z‖ ^ (j + 1)
  have hsum_geom : Summable fun j : ℕ ↦ ‖z‖ ^ (j + 1) := by
    simpa only [pow_succ'] using (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖z‖
  have hbound_int : IntervalIntegrable (fun t : ℝ ↦ ∑' j : ℕ, bound j t) volume 0 1 := by
    refine (((intervalIntegrable_log_pow k).norm).mul_const (∑' j : ℕ, ‖z‖ ^ (j + 1))).congr
      fun t _ ↦ ?_
    simp only [bound, tsum_mul_left, Real.norm_eq_abs, abs_pow]
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence bound
    (fun j ↦ (by fun_prop : Measurable (F j)).aestronglyMeasurable)
    (fun j ↦ ae_of_all _ fun t ht ↦ by
      rw [uIoc_of_le zero_le_one] at ht
      exact norm_radialSeriesTerm_le k j ht)
    (ae_of_all _ fun t _ ↦ hsum_geom.mul_left _)
    hbound_int
    (ae_of_all _ fun t ht ↦ by
      rw [uIoc_of_le zero_le_one] at ht
      have htz : ‖(t : ℂ) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
      exact ((Complex.hasSum_taylorSeries_neg_log' htz).mul_left
        (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ))
  rw [polylog_nat_add_two]
  exact (hint.mul_left (k.factorial : ℂ)⁻¹).congr_fun fun j ↦ (integral_radialSeriesTerm k j z).symm

/-- Disc-series representation in nonpositive weights, by induction on Euler derivatives. -/
private lemma hasSum_polylog_neg_nat (r : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ))) (polylog (-(r : ℤ)) z) := by
  induction r generalizing z with
  | zero =>
    rw [Nat.cast_zero, neg_zero, polylog_zero_weight, div_eq_mul_inv]
    refine ((hasSum_geometric_of_norm_lt_one hz).mul_left z).congr_fun fun k ↦ ?_
    simp [pow_succ']
  | succ r ih =>
    have hlocal : polylog (-(r : ℤ)) =ᶠ[𝓝 z]
        fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ)) := by
      have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 z :=
        Metric.isOpen_ball.mem_nhds (by simpa using hz)
      filter_upwards [hball] with w hw
      exact (ih (by simpa using hw)).tsum_eq.symm
    have heq : polylog (-((r + 1 : ℕ) : ℤ)) z =
        ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ (-((r + 1 : ℕ) : ℤ)) := by
      rw [polylog_neg_nat_succ, hlocal.deriv_eq, mul_deriv_tsum_polylogSeries _ hz]
      refine tsum_congr fun k ↦ ?_
      push_cast
      ring_nf
    rw [heq]
    exact (summable_polylogSeries _ hz).hasSum

/-- **Disc series of the polylogarithm**: for every integer weight `n : ℤ` and every `z : ℂ` in
the open unit disc `‖z‖ < 1`, `polylog n z = ∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`. -/
theorem hasSum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · simpa using hasSum_polylog_neg_nat 0 hz
    · simpa using hasSum_polylog_one hz
    · exact hasSum_polylog_nat_add_two k hz
  | negSucc r =>
    have hn : Int.negSucc r = -((r + 1 : ℕ) : ℤ) := rfl
    rw [hn]
    exact hasSum_polylog_neg_nat (r + 1) hz

/-- `tsum` form of `TauCeti.Polylog.hasSum_polylog` on `‖z‖ < 1`. -/
theorem polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (hasSum_polylog n hz).tsum_eq.symm

/-- On every closed disc `Metric.closedBall 0 r` of radius `r < 1`, the polylogarithm power series
converges uniformly to `polylog n`. -/
theorem hasSumUniformlyOn_polylog_closedBall (n : ℤ) {r : ℝ} (hr : r < 1) :
    HasSumUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) (Metric.closedBall 0 r) := by
  set r' : ℝ := max r 0
  have hr'0 : 0 ≤ r' := le_max_right r 0
  have hr'1 : r' < 1 := max_lt hr zero_lt_one
  have hsum : HasSumUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (fun z ↦ ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n) (Metric.closedBall 0 r) :=
    HasSumUniformlyOn.of_norm_le_summable
      (summable_nat_add_one_pow_mul_geometric (-n).toNat hr'0 hr'1) fun k z hz ↦
        norm_polylogSeriesTerm_le n k
          ((by simpa using hz : ‖z‖ ≤ r).trans (le_max_left r 0))
  refine hsum.congr_right fun z hz ↦ ?_
  have hz1 : ‖z‖ < 1 := (by simpa using hz : ‖z‖ ≤ r).trans_lt hr
  exact (polylog_eq_tsum n hz1).symm

/-- On the open unit disc `Metric.ball 0 1`, the polylogarithm power series converges locally
uniformly to `polylog n`. -/
theorem hasSumLocallyUniformlyOn_polylog_ball (n : ℤ) :
    HasSumLocallyUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) (Metric.ball 0 1) := by
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun z hz ↦ ?_
  have hz1 : ‖z‖ < 1 := by simpa using hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr_def
  have hr1 : r < 1 := by linarith
  have hmem : Metric.closedBall (0 : ℂ) r ∈ 𝓝[Metric.ball 0 1] z :=
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds_of_mem (by
      rw [Metric.mem_ball, dist_zero_right]
      linarith))
  exact ⟨Metric.closedBall 0 r, hmem, hasSumUniformlyOn_polylog_closedBall n hr1⟩

/-- Termwise complex derivative of `polylog n` on the open unit disc `‖z‖ < 1`. -/
theorem hasDerivAt_polylog_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog n) (∑' k : ℕ, (k + 1 : ℂ) * z ^ k / (k + 1 : ℂ) ^ n) z := by
  have hlocal : (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n) =ᶠ[𝓝 z] polylog n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hz : z ∈ Metric.ball (0 : ℂ) 1)]
      with w hw
    exact (polylog_eq_tsum n (by simpa using hw)).symm
  exact (hasDerivAt_tsum_polylogSeries n hz).congr_of_eventuallyEq hlocal.symm

/-- Power-series expansion of `deriv (polylog n)` on the open unit disc `‖z‖ < 1`. -/
theorem hasSum_deriv_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ (k + 1 : ℂ) * z ^ k / (k + 1 : ℂ) ^ n) (deriv (polylog n) z) := by
  rw [(hasDerivAt_polylog_of_norm_lt_one n hz).deriv]
  exact (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ norm_deriv_polylogSeriesTerm_le n k le_rfl)
    (summable_norm_deriv_polylogSeries n (norm_nonneg z) hz)).of_norm.hasSum

/-- Every integer-weight polylogarithm has complex derivative `1` at the origin. -/
theorem hasDerivAt_polylog_zero (n : ℤ) : HasDerivAt (polylog n) 1 0 := by
  have h := hasDerivAt_polylog_of_norm_lt_one n (z := 0) (by simp)
  have htsum : (∑' k : ℕ, (k + 1 : ℂ) * (0 : ℂ) ^ k / (k + 1 : ℂ) ^ n) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro k hk
      simp [zero_pow hk]
  rwa [htsum] at h

/-- The complex derivative of `polylog n` at `0` is `1` in every integer weight. -/
@[simp] theorem deriv_polylog_zero (n : ℤ) : deriv (polylog n) 0 = 1 :=
  (hasDerivAt_polylog_zero n).deriv

end TauCeti.Polylog
