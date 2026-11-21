/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower

/-!
# The power series of integer-weight polylogarithms on the open unit disc

On the open unit disc `‖z‖ < 1`, the principal polylogarithm `Liₙ(z)` of every integer weight
`n : ℤ` expands as the Dirichlet-type power series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`, with
complex integer power `(k + 1 : ℂ) ^ n`. The convergence is absolute on the open disc, uniform on
every closed subdisc `‖z‖ ≤ r` with `r < 1`, and locally uniform on `Metric.ball 0 1`.

This germ identification provides the local analytic expansion of `polylog n` around `0`: its
term-by-term derivative gives `deriv (polylog n) 0 = 1` in every integer weight and supplies the
open-disc Euler differential relation that analytically continues across `{z | 1 - z ∈ slitPlane}`.

## Main results

* `TauCeti.Polylog.hasSum_polylog` and `TauCeti.Polylog.polylog_eq_tsum`:
  `HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z)` for `‖z‖ < 1`.
* `TauCeti.Polylog.hasSum_norm_polylog`: absolute convergence on the open unit disc, identifying
  the sum of norms with `(polylog n ‖z‖).re`.
* `TauCeti.Polylog.hasSumUniformlyOn_polylog`,
  `TauCeti.Polylog.hasSumLocallyUniformlyOn_polylog`,
  `TauCeti.Polylog.tendstoUniformlyOn_polylog_closedBall`, and
  `TauCeti.Polylog.tendstoLocallyUniformlyOn_polylog_ball`: uniform convergence on closed subdiscs
  `r < 1` and locally uniform convergence on `Metric.ball 0 1` (both for unconditional `Finset`
  sums and ordered partial sums).
* `TauCeti.Polylog.hasFPowerSeriesOnBall_polylog`: native formal power-series expansion of
  `polylog n` on `Metric.eball 0 1`.
* `TauCeti.Polylog.hasDerivAt_polylog_tsum_of_norm_lt_one`,
  `TauCeti.Polylog.hasSum_deriv_polylog`, `TauCeti.Polylog.deriv_polylog_eq_tsum`,
  `TauCeti.Polylog.hasDerivAt_polylog_add_one_tsum`,
  `TauCeti.Polylog.hasSum_deriv_polylog_add_one`,
  `TauCeti.Polylog.deriv_polylog_add_one_eq_tsum`,
  `TauCeti.Polylog.hasDerivAt_polylog_zero`, and `TauCeti.Polylog.deriv_polylog_zero`:
  termwise derivative and its convergent series on the open unit disc, and complex
  derivative `1` at `0` for all `n : ℤ`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (1), p. 50.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, introduction, p. 5.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology NNReal ENNReal

namespace TauCeti.Polylog

private lemma inv_factorial_mul_integral_radialTerm (k j : ℕ) (z : ℂ) :
    (Nat.factorial k : ℂ)⁻¹ *
        (∫ t : ℝ in 0..1, ((t ^ j * (-Real.log t) ^ k : ℝ) : ℂ) * (z ^ (j + 1) / (j + 1 : ℂ))) =
      z ^ (j + 1) / (j + 1 : ℂ) ^ (k + 2) := by
  have hreal :
      (∫ t : ℝ in 0..1, ((t ^ j * (-Real.log t) ^ k : ℝ) : ℂ) * (z ^ (j + 1) / (j + 1 : ℂ))) =
        ((∫ t : ℝ in 0..1, t ^ j * (-Real.log t) ^ k : ℝ) : ℂ) * (z ^ (j + 1) / (j + 1 : ℂ)) := by
    simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  have hkf : (Nat.factorial k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hj0 : (j + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero j
  rw [hreal, TauCeti.integral_pow_mul_neg_log_pow j k]
  push_cast
  rw [pow_succ, pow_succ]
  field_simp [hkf, hj0]
  ring

private theorem hasSum_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ ↦ z ^ (j + 1) / (j + 1 : ℂ) ^ (k + 2)) (polylog (k + 2 : ℕ) z) := by
  let F : ℕ → ℝ → ℂ := fun j t ↦
    ((t ^ j * (-Real.log t) ^ k : ℝ) : ℂ) * (z ^ (j + 1) / (j + 1 : ℂ))
  let bound : ℕ → ℝ → ℝ := fun j t ↦ |Real.log t| ^ k * ‖z‖ ^ (j + 1)
  have hgeom : Summable (fun j : ℕ ↦ ‖z‖ ^ (j + 1)) := by
    simpa only [pow_succ'] using (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖z‖
  have hmeas : ∀ j, AEStronglyMeasurable (F j) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    fun j ↦ (by fun_prop : Measurable (F j)).aestronglyMeasurable
  have hbound : ∀ j, ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → ‖F j t‖ ≤ bound j t := by
    intro j
    refine ae_of_all _ fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht1 : t ^ j ≤ 1 := pow_le_one₀ ht.1.le ht.2
    have hj1 : (1 : ℝ) ≤ j + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hcast : ‖(j + 1 : ℂ)‖ = (j + 1 : ℝ) := by
      exact_mod_cast Complex.norm_natCast (j + 1)
    simp only [F, bound, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht.1, abs_neg, norm_div, norm_pow, hcast]
    calc t ^ j * |Real.log t| ^ k * (‖z‖ ^ (j + 1) / (j + 1 : ℝ))
        ≤ 1 * |Real.log t| ^ k * (‖z‖ ^ (j + 1) / 1) := by gcongr
      _ = |Real.log t| ^ k * ‖z‖ ^ (j + 1) := by ring
  have hbound_sum : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → Summable (fun j ↦ bound j t) :=
    ae_of_all _ fun t _ ↦ hgeom.mul_left (|Real.log t| ^ k)
  have hbound_int : IntervalIntegrable (fun t ↦ ∑' j, bound j t) volume 0 1 := by
    have hlog : IntervalIntegrable (fun t : ℝ ↦ |Real.log t| ^ k) volume 0 1 := by
      simpa only [Real.norm_eq_abs, abs_pow] using (intervalIntegrable_log_pow k).norm
    simpa only [bound, tsum_mul_left] using hlog.mul_const (∑' j : ℕ, ‖z‖ ^ (j + 1))
  have hpoint : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      HasSum (fun j ↦ F j t)
        (((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)) := by
    refine ae_of_all _ fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have htz : ‖(t : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    convert ((Complex.hasSum_taylorSeries_neg_log' htz).mul_left
      (((-Real.log t : ℝ) : ℂ) ^ k / (t : ℂ))) using 1
    · ext j
      simp only [F, mul_pow, pow_succ, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg]
      field_simp [ht0]
    · ring
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    bound hmeas hbound hbound_sum hbound_int hpoint
  rw [polylog_nat_add_two]
  simpa only [F, inv_factorial_mul_integral_radialTerm k] using
    hint.mul_left (Nat.factorial k : ℂ)⁻¹

private theorem hasDerivAt_tsum_div_zpow_and_summable (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ (n - 1)) z ∧
      Summable (fun k : ℕ ↦ z ^ k / (k + 1 : ℂ) ^ (n - 1)) := by
  set R : ℝ := (‖z‖ + 1) / 2 with hR_def
  have hR0 : 0 < R := by rw [hR_def]; linarith [norm_nonneg z]
  have hzR : ‖z‖ < R := by rw [hR_def]; linarith
  have hR1 : R < 1 := by rw [hR_def]; linarith
  let g : ℕ → ℂ → ℂ := fun k w ↦ w ^ (k + 1) / (k + 1 : ℂ) ^ n
  let g' : ℕ → ℂ → ℂ := fun k w ↦ w ^ k / (k + 1 : ℂ) ^ (n - 1)
  let u : ℕ → ℝ := fun k ↦ R⁻¹ * ((k + 1 : ℝ) ^ (1 - n).toNat * R ^ (k + 1))
  have hu : Summable u := by
    have hgeom : Summable (fun m : ℕ ↦ (m : ℝ) ^ (1 - n).toNat * R ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one (1 - n).toNat
        (by rw [Real.norm_of_nonneg hR0.le]; exact hR1)
    refine (((summable_nat_add_iff 1).mpr hgeom).congr fun k ↦ ?_).mul_left R⁻¹
    push_cast
    ring
  have hderiv_term (k : ℕ) (w : ℂ) : HasDerivAt (g k) (g' k w) w := by
    have hk0 : (k + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero k
    convert (hasDerivAt_pow (k + 1) w).div_const ((k + 1 : ℂ) ^ n) using 1
    simp only [g', Nat.add_sub_cancel, zpow_sub₀ hk0, zpow_one]
    push_cast
    field_simp [hk0]
  have hbound_term (k : ℕ) (w : ℂ) (hw : w ∈ ball (0 : ℂ) R) : ‖g' k w‖ ≤ u k := by
    have hwR : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
    have hk1 : (1 : ℝ) ≤ k + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hcast : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by exact_mod_cast Complex.norm_natCast (k + 1)
    have hk_pow : ((k + 1 : ℝ) ^ (n - 1))⁻¹ ≤ (k + 1 : ℝ) ^ (1 - n).toNat := by
      rw [← zpow_neg, neg_sub, ← zpow_natCast]
      exact zpow_le_zpow_right₀ hk1 (Int.self_le_toNat (1 - n))
    simp only [g', u, div_eq_inv_mul, norm_mul, norm_inv, norm_zpow, norm_pow, hcast]
    calc ((k + 1 : ℝ) ^ (n - 1))⁻¹ * ‖w‖ ^ k
        ≤ (k + 1 : ℝ) ^ (1 - n).toNat * R ^ k := by gcongr
      _ = R⁻¹ * ((k + 1 : ℝ) ^ (1 - n).toNat * R ^ (k + 1)) := by
          rw [pow_succ']
          field_simp [hR0.ne']
  have hg0 : Summable (fun k ↦ g k 0) := by
    simp only [g, zero_pow (Nat.succ_ne_zero _), zero_div]
    exact summable_zero
  exact ⟨hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball 0 R).isPreconnected
      (fun k w _ ↦ hderiv_term k w) hbound_term (mem_ball_self hR0) hg0 (mem_ball_zero_iff.mpr hzR),
    Summable.of_norm_bounded hu fun k ↦ hbound_term k z (mem_ball_zero_iff.mpr hzR)⟩

private theorem hasSum_polylog_neg_nat (r : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ))) (polylog (-(r : ℤ)) z) := by
  induction r generalizing z with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, zpow_zero, div_one, polylog_zero_weight]
    rw [div_eq_mul_inv]
    simpa only [pow_succ'] using (hasSum_geometric_of_norm_lt_one hz).mul_left z
  | succ r ih =>
    obtain ⟨htsum_deriv, hg'_sum⟩ := hasDerivAt_tsum_div_zpow_and_summable (-(r : ℤ)) hz
    have hloc : (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ))) =ᶠ[𝓝 z]
        polylog (-(r : ℤ)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
      exact (ih (mem_ball_zero_iff.mp hw)).tsum_eq
    have hpoly_deriv :
        deriv (polylog (-(r : ℤ))) z = ∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ (-(r : ℤ) - 1) :=
      (htsum_deriv.congr_of_eventuallyEq hloc.symm).deriv
    rw [polylog_neg_nat_succ, hpoly_deriv]
    convert hg'_sum.hasSum.mul_left z using 1
    ext k
    push_cast
    rw [neg_add', ← mul_div_assoc, ← pow_succ']

/-- **Disc-series expansion of integer-weight polylogarithms.** For every integer weight `n : ℤ`
and every `z` in the open unit disc `‖z‖ < 1`, the series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`
converges to `polylog n z`. -/
theorem hasSum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · simpa using hasSum_polylog_neg_nat 0 hz
    · simpa using hasSum_polylog_one hz
    · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hasSum_polylog_nat_add_two k hz
  | negSucc r =>
    have h := hasSum_polylog_neg_nat (r + 1) hz
    rwa [Nat.cast_add_one, ← Int.negSucc_eq] at h

/-- On the open unit disc `‖z‖ < 1`, `polylog n z` equals the sum of its power series. -/
theorem polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (hasSum_polylog n hz).tsum_eq.symm

/-- The polylogarithm disc series converges absolutely for `‖z‖ < 1`, and the sum of the norms of
its terms equals `(polylog n ‖z‖).re`. -/
theorem hasSum_norm_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) (polylog n ‖z‖).re := by
  have hz' : ‖(‖z‖ : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hz
  refine (Complex.reCLM.hasSum (hasSum_polylog n hz')).congr_fun fun k ↦ ?_
  have hreal : ((‖z‖ ^ (k + 1) / (k + 1 : ℝ) ^ n : ℝ) : ℂ) =
      (‖z‖ : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n := by simp
  have hnorm_k : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by exact_mod_cast Complex.norm_natCast (k + 1)
  rw [Complex.reCLM_apply, ← hreal, Complex.ofReal_re]
  simp [norm_zpow, hnorm_k]

/-- The power series of `polylog n` converges unconditionally and uniformly on every closed subdisc
`Metric.closedBall 0 r` of radius `r < 1`. -/
theorem hasSumUniformlyOn_polylog (n : ℤ) {r : ℝ} (hr : r < 1) :
    HasSumUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n)
      (closedBall 0 r) := by
  have hmax1 : max r 0 < 1 := max_lt hr zero_lt_one
  have hmax' : ‖((max r 0 : ℝ) : ℂ)‖ < 1 := by
    rwa [Complex.norm_real, Real.norm_of_nonneg (le_max_right r 0)]
  have hu : Summable (fun k : ℕ ↦ ‖((max r 0 : ℝ) : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n‖) :=
    (hasSum_norm_polylog n hmax').summable
  refine (HasSumUniformlyOn.of_norm_le_summable hu fun k z hz ↦ ?_).congr_right fun z hz ↦ ?_
  · rw [mem_closedBall_zero_iff] at hz
    simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (le_max_right r 0)]
    gcongr
    exact hz.trans (le_max_left r 0)
  · exact (polylog_eq_tsum n ((mem_closedBall_zero_iff.mp hz).trans_lt hr)).symm

/-- The power series of `polylog n` converges unconditionally and locally uniformly on the open
unit disc `Metric.ball 0 1`. -/
theorem hasSumLocallyUniformlyOn_polylog (n : ℤ) :
    HasSumLocallyUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n)
      (ball 0 1) := by
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun z hz ↦ ?_
  obtain ⟨r, hzr, hr1⟩ := exists_between (mem_ball_zero_iff.mp hz)
  exact ⟨closedBall 0 r,
    nhdsWithin_le_nhds (closedBall_mem_nhds_of_mem (mem_ball_zero_iff.mpr hzr)),
    hasSumUniformlyOn_polylog n hr1⟩

/-- On every closed subdisc `Metric.closedBall 0 r` with `r < 1`, the partial sums of the
polylogarithm power series converge uniformly to `polylog n`. -/
theorem tendstoUniformlyOn_polylog_closedBall (n : ℤ) {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn
      (fun N (z : ℂ) ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (closedBall 0 r) :=
  (hasSumUniformlyOn_polylog n hr).tendstoUniformlyOn_finsetRange

/-- On the open unit disc `Metric.ball 0 1`, the partial sums of the polylogarithm power series
converge locally uniformly to `polylog n`. -/
theorem tendstoLocallyUniformlyOn_polylog_ball (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun N (z : ℂ) ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (ball 0 1) :=
  (hasSumLocallyUniformlyOn_polylog n).tendstoLocallyUniformlyOn_finsetRange

/-- On the open unit disc `Metric.eball 0 1`, `polylog n` is represented by the scalar formal
multilinear series with constant term `0` and `(k + 1)`-st coefficient `((k + 1 : ℂ) ^ n)⁻¹`. -/
theorem hasFPowerSeriesOnBall_polylog (n : ℤ) :
    HasFPowerSeriesOnBall (polylog n)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun m : ℕ ↦ match m with | 0 => (0 : ℂ) | k + 1 => ((k + 1 : ℂ) ^ n)⁻¹)) 0 1 := by
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_, zero_lt_one, fun {y} hy ↦ ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_summable_norm
    rw [← summable_nat_add_iff 1]
    have hr1 : ((r : ℝ) : ℝ) < 1 := by exact_mod_cast hr
    have hr' : ‖((r : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg]
      exact hr1
    refine (hasSum_norm_polylog n hr').summable.congr fun k ↦ ?_
    simp only [FormalMultilinearSeries.ofScalars_norm, div_eq_inv_mul, norm_mul, norm_inv,
      norm_pow, Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg]
  · simp only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] at hy
    rw [zero_add, ← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, FormalMultilinearSeries.ofScalars_apply_eq,
      pow_zero, smul_eq_mul, zero_mul, sub_zero, inv_mul_eq_div]
    exact hasSum_polylog n hy

/-- On the open unit disc `‖z‖ < 1` (including `z = 0`), `polylog n` has complex derivative given
by the differentiated power series `∑_{k ≥ 0} z ^ k / (k + 1) ^ (n - 1)`. -/
theorem hasDerivAt_polylog_tsum_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog n) (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ (n - 1)) z := by
  have hloc : (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n) =ᶠ[𝓝 z] polylog n := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
    exact (polylog_eq_tsum n (mem_ball_zero_iff.mp hw)).symm
  exact (hasDerivAt_tsum_div_zpow_and_summable n hz).1.congr_of_eventuallyEq hloc.symm

/-- On the open unit disc `‖z‖ < 1` (including `z = 0`), the differentiated power series
`∑_{k ≥ 0} z ^ k / (k + 1) ^ (n - 1)` converges to `deriv (polylog n) z`. -/
theorem hasSum_deriv_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ k / (k + 1 : ℂ) ^ (n - 1)) (deriv (polylog n) z) := by
  rw [(hasDerivAt_polylog_tsum_of_norm_lt_one n hz).deriv]
  exact (hasDerivAt_tsum_div_zpow_and_summable n hz).2.hasSum

/-- Power-series expansion of `deriv (polylog n) z` on the open unit disc `‖z‖ < 1`. -/
theorem deriv_polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (polylog n) z = ∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ (n - 1) :=
  (hasSum_deriv_polylog n hz).tsum_eq.symm

/-- On the open unit disc `‖z‖ < 1`, `polylog (n + 1)` has complex derivative
`∑_{k ≥ 0} z ^ k / (k + 1) ^ n`. -/
theorem hasDerivAt_polylog_add_one_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog (n + 1)) (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ n) z := by
  simpa only [add_sub_cancel_right] using hasDerivAt_polylog_tsum_of_norm_lt_one (n + 1) hz

/-- Power-series expansion (`HasSum` form) of `deriv (polylog (n + 1)) z` on the open unit disc
`‖z‖ < 1`. -/
theorem hasSum_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ k / (k + 1 : ℂ) ^ n) (deriv (polylog (n + 1)) z) := by
  simpa only [add_sub_cancel_right] using hasSum_deriv_polylog (n + 1) hz

/-- Power-series expansion of `deriv (polylog (n + 1)) z` on the open unit disc `‖z‖ < 1`. -/
theorem deriv_polylog_add_one_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (polylog (n + 1)) z = ∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ n :=
  (hasSum_deriv_polylog_add_one n hz).tsum_eq.symm

/-- Every integer-weight polylogarithm has complex derivative `1` at `0`. -/
theorem hasDerivAt_polylog_zero (n : ℤ) : HasDerivAt (polylog n) 1 0 := by
  have h := hasDerivAt_polylog_tsum_of_norm_lt_one n (z := 0) (by simp)
  have hval : (∑' k : ℕ, (0 : ℂ) ^ k / (k + 1 : ℂ) ^ (n - 1)) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro k hk
      simp [zero_pow hk]
  rwa [hval] at h

/-- Every integer-weight polylogarithm has `deriv (polylog n) 0 = 1`. -/
@[simp] theorem deriv_polylog_zero (n : ℤ) : deriv (polylog n) 0 = 1 :=
  (hasDerivAt_polylog_zero n).deriv

/-- The first partial sum `1 / 2` of the dilogarithm series at `z = 1 / 2` approximates
`polylog 2 (1 / 2)` within `1 / 8`. -/
theorem norm_polylog_two_half_sub_half_le :
    ‖polylog 2 (1 / 2) - 1 / 2‖ ≤ 1 / 8 := by
  have hhalf : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have htail : HasSum (fun k : ℕ ↦ (1 / 2 : ℂ) ^ (k + 2) / (k + 2 : ℂ) ^ (2 : ℤ))
      (polylog 2 (1 / 2) - 1 / 2) := by
    have h := (hasSum_nat_add_iff' 1).mpr (hasSum_polylog 2 hhalf)
    simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, one_zpow, div_one] at h
    convert h using 1
    ext k
    simp only [Nat.add_assoc, zpow_two]
    push_cast
    ring
  have hgeom : HasSum (fun k : ℕ ↦ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k) (1 / 8 : ℝ) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 16 : ℝ) using 1
    norm_num
  have hterm_le (k : ℕ) :
      ‖(1 / 2 : ℂ) ^ (k + 2) / (k + 2 : ℂ) ^ (2 : ℤ)‖ ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k := by
    have hk_sq : (4 : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hnorm_half : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    have hnorm_k : ‖(k + 2 : ℂ)‖ = (k : ℝ) + 2 := by
      exact_mod_cast Complex.norm_natCast (k + 2)
    rw [zpow_ofNat, norm_div, norm_pow, norm_pow, hnorm_half, hnorm_k]
    calc (1 / 2 : ℝ) ^ (k + 2) / ((k : ℝ) + 2) ^ 2
        ≤ (1 / 2 : ℝ) ^ (k + 2) / 4 := by gcongr
      _ = (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k := by ring
  have hnorm_sum : Summable (fun k : ℕ ↦ ‖(1 / 2 : ℂ) ^ (k + 2) / (k + 2 : ℂ) ^ (2 : ℤ)‖) :=
    hgeom.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le
  rw [← htail.tsum_eq]
  exact (norm_tsum_le_tsum_norm hnorm_sum).trans
    ((Summable.tsum_le_tsum hterm_le hnorm_sum hgeom.summable).trans hgeom.tsum_eq.le)

end TauCeti.Polylog
