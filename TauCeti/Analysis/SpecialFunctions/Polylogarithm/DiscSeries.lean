/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# The power series of integer-weight polylogarithms on the unit disc

On the open unit disc `‖z‖ < 1`, the principal polylogarithm `Liₙ(z)` of every integer weight
`n : ℤ` expands as the Dirichlet-type power series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`, with
complex integer power `(k + 1 : ℂ) ^ n`; in weight `n ≥ 2` the expansion holds on the whole closed
unit disc `‖z‖ ≤ 1`. The convergence is absolute on the open disc and, in weight `n ≥ 2`, on the
closed disc, where the termwise integration of the radial integral is dominated by the series at
`z = 1`. It is uniform on every closed subdisc `‖z‖ ≤ r` with `r < 1`, and locally uniform on
`Metric.ball 0 1`.

This germ identification provides the local analytic expansion of `polylog n` around `0`: its
term-by-term derivative gives `deriv (polylog n) 0 = 1` in every integer weight and supplies the
open-disc Euler differential relation that analytically continues across `{z | 1 - z ∈ slitPlane}`.

## Main results

* `TauCeti.Polylog.hasSum_polylog` and `TauCeti.Polylog.polylog_eq_tsum`:
  `HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z)` for `‖z‖ < 1`.
* `TauCeti.Polylog.hasSum_polylog_of_norm_le_one` and
  `TauCeti.Polylog.polylog_eq_tsum_of_norm_le_one`: the same expansion on the closed unit disc
  `‖z‖ ≤ 1` in weight `n ≥ 2`.
* `TauCeti.Polylog.hasSum_norm_polylog` and `TauCeti.Polylog.hasSum_norm_polylog_of_norm_le_one`:
  absolute convergence on the open unit disc, and on the closed unit disc in weight `n ≥ 2`,
  identifying the sum of norms with `(polylog n ‖z‖).re`.
* `TauCeti.Polylog.tendstoUniformlyOn_polylog_closedBall` and
  `TauCeti.Polylog.tendstoLocallyUniformlyOn_polylog_ball`: uniform convergence on closed subdiscs
  `r < 1` and locally uniform convergence on `Metric.ball 0 1`.
* `TauCeti.Polylog.hasFPowerSeriesOnBall_polylog`: native formal power-series expansion of
  `polylog n` on `Metric.eball 0 1`.
* `TauCeti.Polylog.hasDerivAt_polylog_tsum_of_norm_lt_one`,
  `TauCeti.Polylog.hasSum_deriv_polylog`, `TauCeti.Polylog.hasDerivAt_polylog_zero`, and
  `TauCeti.Polylog.deriv_polylog_zero`: termwise derivative and its convergent series on the open
  unit disc, and complex derivative `1` at `0` for all `n : ℤ`.

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

/-- On `(0, 1)`, the terms `t ^ j |log t| ^ k / (j + 1)` of the termwise-integrated series at
`z = 1` sum to the norm of the radial integrand at `z = 1`. -/
private lemma hasSum_radialMajorant (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun j : ℕ ↦ |Real.log t| ^ k * (t ^ (j + 1) / (j + 1)) / t)
      ‖((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * 1)) / t‖ := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht.2
  have hlog : ‖Complex.log (1 - (t : ℂ) * 1)‖ = -Real.log (1 - t) := by
    have h := Complex.ofReal_log h1t.le
    push_cast at h
    simp [← h, abs_of_nonpos (Real.log_nonpos h1t.le (by linarith [ht.1]))]
  simp only [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht.1, hlog]
  exact ((Real.hasSum_pow_div_log_of_abs_lt_one (by rw [abs_of_pos ht.1]; exact ht.2)).mul_left
    (|Real.log t| ^ k)).div_const t

/-- Termwise integration of the radial integral on the closed unit disc. The terms of the
series at `z = 1`, `t ^ j |log t| ^ k / (j + 1)`, dominate the terms at every `‖z‖ ≤ 1`; their sum
is the norm of the radial integrand at `z = 1`, which is integrable. -/
private theorem hasSum_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun j : ℕ ↦ z ^ (j + 1) / (j + 1 : ℂ) ^ (k + 2)) (polylog (k + 2 : ℕ) z) := by
  let F : ℕ → ℝ → ℂ := fun j t ↦
    ((t ^ j * (-Real.log t) ^ k : ℝ) : ℂ) * (z ^ (j + 1) / (j + 1 : ℂ))
  let bound : ℕ → ℝ → ℝ := fun j t ↦ |Real.log t| ^ k * (t ^ (j + 1) / (j + 1)) / t
  have hmeas : ∀ j, AEStronglyMeasurable (F j) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    fun j ↦ (by fun_prop : Measurable (F j)).aestronglyMeasurable
  have hbound : ∀ j, ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → ‖F j t‖ ≤ bound j t := by
    intro j
    refine ae_of_all _ fun t ht ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hcast : ‖(j + 1 : ℂ)‖ = (j + 1 : ℝ) := by
      exact_mod_cast Complex.norm_natCast (j + 1)
    have hzj : ‖z‖ ^ (j + 1) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
    simp only [F, bound, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht.1, abs_neg, norm_div, norm_pow, hcast]
    calc t ^ j * |Real.log t| ^ k * (‖z‖ ^ (j + 1) / (j + 1 : ℝ))
        ≤ t ^ j * |Real.log t| ^ k * (1 / (j + 1 : ℝ)) := by
          gcongr
          exact mul_nonneg (pow_nonneg ht.1.le j) (by positivity)
      _ = |Real.log t| ^ k * (t ^ (j + 1) / (j + 1)) / t := by
          field_simp [ht.1.ne']
          ring
  have hne : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by
    simpa using (countable_singleton (1 : ℝ)).ae_notMem volume
  have hbound_sum : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → Summable (fun j ↦ bound j t) := by
    filter_upwards [hne] with t ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    exact (hasSum_radialMajorant k ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩).summable
  have hbound_int : IntervalIntegrable (fun t ↦ ∑' j, bound j t) volume 0 1 :=
    (intervalIntegrable_radialIntegrand k 1).norm.congr_uIoo fun t ht ↦
      ((hasSum_radialMajorant k (by rwa [uIoo_of_le zero_le_one] at ht)).tsum_eq).symm
  have hpoint : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      HasSum (fun j ↦ F j t)
        (((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)) := by
    filter_upwards [hne] with t ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    have htz : ‖(t : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      exact (mul_le_of_le_one_right ht.1.le hz).trans_lt (lt_of_le_of_ne ht.2 ht1)
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
    · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hasSum_polylog_nat_add_two k hz.le
  | negSucc r =>
    have h := hasSum_polylog_neg_nat (r + 1) hz
    rwa [Nat.cast_add_one, ← Int.negSucc_eq] at h

/-- **Closed-disc series of polylogarithms.** In every weight `n ≥ 2`, the disc series
`∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n` converges to `polylog n z` on the whole closed unit disc
`‖z‖ ≤ 1`, including the boundary point `z = 1`. -/
theorem hasSum_polylog_of_norm_le_one {n : ℤ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k + 2 : ℕ) := ⟨(n - 2).toNat, by omega⟩
  simpa only [zpow_natCast] using hasSum_polylog_nat_add_two k hz

/-- On the open unit disc `‖z‖ < 1`, `polylog n z` equals the sum of its power series. -/
theorem polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (hasSum_polylog n hz).tsum_eq.symm

/-- In weight `n ≥ 2`, on the closed unit disc `‖z‖ ≤ 1`, `polylog n z` equals the sum of its
power series. -/
theorem polylog_eq_tsum_of_norm_le_one {n : ℤ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (hasSum_polylog_of_norm_le_one hn hz).tsum_eq.symm

/-- Taking real parts of the disc series at the real point `‖z‖` gives the sum of the norms of
the terms at `z`. -/
private lemma hasSum_norm_of_hasSum_polylog_norm {n : ℤ} {z : ℂ}
    (h : HasSum (fun k : ℕ ↦ (‖z‖ : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n ‖z‖)) :
    HasSum (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) (polylog n ‖z‖).re := by
  refine (Complex.reCLM.hasSum h).congr_fun fun k ↦ ?_
  have hreal : ((‖z‖ ^ (k + 1) / (k + 1 : ℝ) ^ n : ℝ) : ℂ) =
      (‖z‖ : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n := by simp
  have hnorm_k : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by exact_mod_cast Complex.norm_natCast (k + 1)
  rw [Complex.reCLM_apply, ← hreal, Complex.ofReal_re]
  simp [norm_zpow, hnorm_k]

/-- The polylogarithm disc series converges absolutely for `‖z‖ < 1`, and the sum of the norms of
its terms equals `(polylog n ‖z‖).re`. -/
theorem hasSum_norm_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) (polylog n ‖z‖).re :=
  hasSum_norm_of_hasSum_polylog_norm <| hasSum_polylog n <| by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hz

/-- In weight `n ≥ 2`, the polylogarithm disc series converges absolutely on the closed unit disc
`‖z‖ ≤ 1`, and the sum of the norms of its terms equals `(polylog n ‖z‖).re`. -/
theorem hasSum_norm_polylog_of_norm_le_one {n : ℤ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) (polylog n ‖z‖).re :=
  hasSum_norm_of_hasSum_polylog_norm <| hasSum_polylog_of_norm_le_one hn <| by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hz

/-- On every closed subdisc `Metric.closedBall 0 r` with `r < 1`, the partial sums of the
polylogarithm power series converge uniformly to `polylog n`. -/
theorem tendstoUniformlyOn_polylog_closedBall (n : ℤ) {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn
      (fun N (z : ℂ) ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (closedBall 0 r) := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · rw [closedBall_eq_empty.mpr hr0]
    exact tendstoUniformlyOn_empty
  have hr' : ‖(r : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hr0]
  have hu : Summable (fun k : ℕ ↦ ‖(r : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n‖) :=
    (hasSum_norm_polylog n hr').summable
  have hunif := tendstoUniformlyOn_tsum_nat hu (s := closedBall (0 : ℂ) r)
    (f := fun k (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) fun k z hz ↦ by
      rw [mem_closedBall_zero_iff] at hz
      simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
      gcongr
  refine hunif.congr_right fun z hz ↦ ?_
  exact (polylog_eq_tsum n ((mem_closedBall_zero_iff.mp hz).trans_lt hr)).symm

/-- On the open unit disc `Metric.ball 0 1`, the partial sums of the polylogarithm power series
converge locally uniformly to `polylog n`. -/
theorem tendstoLocallyUniformlyOn_polylog_ball (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun N (z : ℂ) ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (ball 0 1) := by
  intro u hu z hz
  rw [mem_ball_zero_iff] at hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr_def
  have hzr : z ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, hr_def]
    linarith
  have hr1 : r < 1 := by rw [hr_def]; linarith
  exact ⟨closedBall 0 r,
    mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds_of_mem hzr),
    tendstoUniformlyOn_polylog_closedBall n hr1 u hu⟩

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
