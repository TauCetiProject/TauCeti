/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower

/-!
# The power series of integer-weight polylogarithms on the open unit disc

On the open unit disc `‖z‖ < 1`, every integer-weight principal polylogarithm `Liₙ(z)` is given by
the classical power series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`, with absolute convergence at each
point, uniform convergence on closed subdiscs `‖z‖ ≤ r < 1`, and locally uniform convergence on the
open disc.

For weights `n = m + 2 ≥ 2`, expanding `-Log (1 - t z)` in its Taylor series on `t ∈ (0, 1]` and
integrating term by term against `(-log t) ^ m / t` reduces each coefficient to the logarithmic
moment `∫ t in 0..1, t ^ k * (-log t) ^ m = m! / (k + 1) ^ (m + 1)`
(`TauCeti.integral_pow_mul_neg_log_pow`). Weight `1` is Mathlib's logarithm series, and nonpositive
weights `n = -r` follow by induction on `r` from the geometric series `z / (1 - z) = ∑ z ^ (k + 1)`
via termwise Euler differentiation `z d/dz` on subdiscs of the open unit disc. Termwise
differentiation at the origin then shows that every integer weight satisfies `(Liₙ)'(0) = 1`,
without dividing by `z`.

## Main declarations

* `TauCeti.Polylog.summable_norm_pow_div_zpow` and `TauCeti.Polylog.summable_pow_div_zpow`:
  absolute and ordinary summability of `z ^ (k + 1) / (k + 1) ^ n` on `‖z‖ < 1`.
* `TauCeti.Polylog.hasSum_polylog` and `TauCeti.Polylog.polylog_eq_tsum`:
  `HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z)` for every `n : ℤ` and
  `‖z‖ < 1`.
* `TauCeti.Polylog.hasSumUniformlyOn_polylog` and
  `TauCeti.Polylog.hasSumLocallyUniformlyOn_polylog`: uniform convergence on closed subdiscs
  `‖z‖ ≤ r < 1` and locally uniform convergence on `Metric.ball 0 1`.
* `TauCeti.Polylog.hasDerivAt_polylog_zero` and `TauCeti.Polylog.deriv_polylog_zero`:
  `HasDerivAt (polylog n) 1 0` and `deriv (polylog n) 0 = 1` for every `n : ℤ`.
* `TauCeti.Polylog.mul_deriv_polylog_add_one_of_norm_lt_one`:
  `z * deriv (polylog (n + 1)) z = polylog n z` on `‖z‖ < 1`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (1), p. 50.
* Don Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*
  (2007), Part I, introduction, p. 5.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.Polylog

/-- Uniform polynomial bound on `‖(k + 1 : ℂ) ^ n‖⁻¹` for any integer weight `n`. -/
private lemma inv_norm_nat_add_one_zpow_le (n : ℤ) (k : ℕ) :
    ‖(k + 1 : ℂ) ^ n‖⁻¹ ≤ ((k : ℝ) + 1) ^ (-n).toNat := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hnorm : ‖(k + 1 : ℂ) ^ n‖ = ((k : ℝ) + 1) ^ n := by
    rw [norm_zpow]
    norm_cast
  rw [hnorm, ← zpow_neg]
  rcases le_or_gt n 0 with hn | hn
  · have hcast : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (neg_nonneg.2 hn)
    conv_lhs => rw [← hcast, zpow_natCast]
  · have htoNat : (-n).toNat = 0 := Int.toNat_of_nonpos (neg_nonpos.2 hn.le)
    rw [htoNat, pow_zero]
    exact zpow_le_one_of_nonpos₀ hk1 (neg_nonpos.2 hn.le)

/-- Pointwise polynomial-geometric majorant for `z ^ (k + 1) / (k + 1) ^ n` when `‖z‖ ≤ r`. -/
private lemma norm_pow_div_zpow_le (n : ℤ) {r : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) (k : ℕ) :
    ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖ ≤ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ (k + 1) := by
  rw [norm_div, norm_pow, div_eq_mul_inv, mul_comm]
  push_cast
  exact mul_le_mul (inv_norm_nat_add_one_zpow_le n k)
    (pow_le_pow_left₀ (norm_nonneg z) hz (k + 1)) (pow_nonneg (norm_nonneg z) _)
    (by positivity)

/-- For every `n : ℤ` and `‖z‖ < 1`, the polylogarithm disc series converges absolutely. -/
theorem summable_norm_pow_div_zpow (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) := by
  have hznorm : ‖‖z‖‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg z)]
  have hmaj : Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * ‖z‖ ^ (k + 1)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (-n).toNat (r := ‖z‖) hznorm).comp_injective
      (add_left_injective 1)
  exact hmaj.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_pow_div_zpow_le n le_rfl)

/-- For every `n : ℤ` and `‖z‖ < 1`, the polylogarithm disc series is summable. -/
theorem summable_pow_div_zpow (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) :=
  (summable_norm_pow_div_zpow n hz).of_norm

/-- On the open unit disc `‖z‖ < 1`, `w ↦ ∑' k, w ^ (k + 1) / (k + 1) ^ (n + 1)` has complex
derivative `∑' k, z ^ k / (k + 1) ^ n`. -/
theorem hasDerivAt_tsum_pow_div_zpow (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (n + 1))
      (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ n) z := by
  set r : ℝ := (‖z‖ + 1) / 2 with hr_def
  have hr0 : 0 < r := by rw [hr_def]; linarith [norm_nonneg z]
  have hr1 : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0.le, hr_def]; linarith
  have hzr : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, hr_def]
    linarith
  have hu : Summable (fun k : ℕ ↦ r⁻¹ * (((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ (k + 1))) :=
    ((summable_pow_mul_geometric_of_norm_lt_one (-n).toNat (r := r) hr1).comp_injective
      (add_left_injective 1)).mul_left r⁻¹
  have hg : ∀ k : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      HasDerivAt (fun w : ℂ ↦ w ^ (k + 1) / (k + 1 : ℂ) ^ (n + 1))
        (y ^ k / (k + 1 : ℂ) ^ n) y := by
    intro k y _
    have hkne : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    convert (hasDerivAt_pow (k + 1) y).div_const ((k + 1 : ℂ) ^ (n + 1)) using 1
    rw [zpow_add_one₀ hkne n]
    push_cast
    field_simp [hkne]
  have hg' : ∀ k : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      ‖y ^ k / (k + 1 : ℂ) ^ n‖ ≤ r⁻¹ * (((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ (k + 1)) := by
    intro k y hy
    have hyr : ‖y‖ ≤ r := by
      rw [Metric.mem_ball, dist_zero_right] at hy
      exact hy.le
    rw [norm_div, norm_pow, div_eq_mul_inv, mul_comm]
    calc ‖(k + 1 : ℂ) ^ n‖⁻¹ * ‖y‖ ^ k
        ≤ ((k : ℝ) + 1) ^ (-n).toNat * r ^ k :=
          mul_le_mul (inv_norm_nat_add_one_zpow_le n k)
            (pow_le_pow_left₀ (norm_nonneg y) hyr k) (pow_nonneg (norm_nonneg y) _)
            (by positivity)
      _ = r⁻¹ * (((k + 1 : ℕ) : ℝ) ^ (-n).toNat * r ^ (k + 1)) := by
          push_cast
          rw [pow_succ]
          field_simp [hr0.ne']
  have h0sum : Summable (fun k : ℕ ↦ (0 : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ (n + 1)) := by simp
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected hg hg' (Metric.mem_ball_self hr0) h0sum hzr

/-- Evaluation of the `k`-th radial moment `(m!)⁻¹ * ∫₀¹ (z ^ (k + 1) / (k + 1)) t ^ k (-log t) ^ m`
to `z ^ (k + 1) / (k + 1) ^ (m + 2)`. -/
private lemma integral_pow_div_mul_pow_mul_neg_log_pow (m k : ℕ) (z : ℂ) :
    z ^ (k + 1) / (k + 1 : ℂ) ^ ((m + 2 : ℕ) : ℤ) =
      (Nat.factorial m : ℂ)⁻¹ *
        ∫ t : ℝ in 0..1, (z ^ (k + 1) / (k + 1 : ℂ)) * ((t ^ k * (-Real.log t) ^ m : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    TauCeti.integral_pow_mul_neg_log_pow k m, zpow_natCast]
  have hfac : (Nat.factorial m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hkne : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  have hexp : ((k : ℂ) + 1) ^ (m + 2) = ((k : ℂ) + 1) * ((k : ℂ) + 1) ^ (m + 1) := by ring
  rw [hexp]
  field_simp [hfac, hkne]

/-- Disc-series identification for weights `m + 2 ≥ 2` via dominated termwise integration of
`-Log (1 - t z)` against `(-log t) ^ m / t`. -/
private lemma hasSum_polylog_nat_add_two (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ ((m + 2 : ℕ) : ℤ))
      (polylog (m + 2 : ℕ) z) := by
  set F : ℕ → ℝ → ℂ := fun k t ↦
    (z ^ (k + 1) / (k + 1 : ℂ)) * ((t ^ k * (-Real.log t) ^ m : ℝ) : ℂ)
  set bound : ℕ → ℝ → ℝ := fun k t ↦ ‖z‖ ^ (k + 1) * |Real.log t| ^ m
  have hz_sum : Summable (fun k : ℕ ↦ ‖z‖ ^ (k + 1)) :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).comp_injective (add_left_injective 1)
  have hdom : HasSum (fun k : ℕ ↦ ∫ t : ℝ in 0..1, F k t)
      (∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ m * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound
      (fun k ↦ (by fun_prop : Measurable (F k)).aestronglyMeasurable) ?_ ?_ ?_ ?_
    · intro k
      refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have htk : t ^ k ≤ 1 := pow_le_one₀ ht0.le ht1
      dsimp only [F, bound]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_pow, abs_neg, abs_of_pos ht0]
      have hnormk : ‖(k + 1 : ℂ)‖ = (k : ℝ) + 1 := by norm_cast
      rw [hnormk]
      calc (‖z‖ ^ (k + 1) / ((k : ℝ) + 1)) * (t ^ k * |Real.log t| ^ m)
          ≤ ‖z‖ ^ (k + 1) * (1 * |Real.log t| ^ m) := by
            refine mul_le_mul (div_le_self (by positivity) hk1)
              (mul_le_mul_of_nonneg_right htk (by positivity)) (by positivity) (by positivity)
        _ = ‖z‖ ^ (k + 1) * |Real.log t| ^ m := by ring
    · exact ae_of_all _ fun t _ ↦ hz_sum.mul_right _
    · have hlog : IntervalIntegrable (fun t : ℝ ↦ |Real.log t| ^ m) volume 0 1 := by
        simpa [Real.norm_eq_abs, abs_pow] using (TauCeti.intervalIntegrable_log_pow m).norm
      simpa only [bound, tsum_mul_right] using hlog.const_mul (∑' k : ℕ, ‖z‖ ^ (k + 1))
    · refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have ht0 : 0 < t := ht.1
      have htz : ‖(t : ℂ) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
      have h1 := ((hasSum_polylog_one htz).mul_left (((-Real.log t : ℝ) : ℂ) ^ m)).div_const
        (t : ℂ)
      rw [polylog_one] at h1
      refine h1.congr_fun fun k ↦ ?_
      have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
      dsimp only [F]
      push_cast
      rw [mul_pow ((t : ℂ)) z (k + 1), pow_succ (t : ℂ) k]
      field_simp [htc]
  rw [polylog_nat_add_two]
  exact (hdom.mul_left (Nat.factorial m : ℂ)⁻¹).congr_fun fun k ↦
    integral_pow_div_mul_pow_mul_neg_log_pow m k z

/-- Disc-series identification for nonpositive weights `-(r : ℤ)` by induction on `r` via termwise
Euler differentiation of the geometric series. -/
private lemma hasSum_polylog_neg_nat (r : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ))) (polylog (-(r : ℤ)) z) := by
  induction r generalizing z with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, zpow_zero, div_one, polylog_zero_weight]
    rw [div_eq_mul_inv]
    simpa only [pow_succ'] using (hasSum_geometric_of_norm_lt_one hz).mul_left z
  | succ r ih =>
    have heq : (fun w : ℂ ↦ polylog (-(r : ℤ)) w) =ᶠ[𝓝 z]
        fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hz : z ∈ Metric.ball 0 1)]
        with w hw
      exact (ih (by simpa using hw)).tsum_eq.symm
    have hderiv := hasDerivAt_tsum_pow_div_zpow (-((r + 1 : ℕ) : ℤ)) hz
    have hexp : -((r + 1 : ℕ) : ℤ) + 1 = -(r : ℤ) := by push_cast; ring
    rw [hexp] at hderiv
    rw [polylog_neg_nat_succ, heq.deriv_eq, hderiv.deriv, ← tsum_mul_left]
    convert (summable_pow_div_zpow (-((r + 1 : ℕ) : ℤ)) hz).hasSum using 1
    congr 1
    ext k
    rw [← mul_div_assoc, pow_succ']

/-- On the open unit disc `‖z‖ < 1`, every integer-weight principal polylogarithm `Liₙ(z)` is the
sum of `z ^ (k + 1) / (k + 1) ^ n`. -/
theorem hasSum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  cases n with
  | ofNat n =>
    rcases n with _ | _ | m
    · simpa using hasSum_polylog_neg_nat 0 hz
    · simpa using hasSum_polylog_one hz
    · exact hasSum_polylog_nat_add_two m hz
  | negSucc r =>
    simpa [Int.negSucc_eq] using hasSum_polylog_neg_nat (r + 1) hz

/-- For every `n : ℤ` and `‖z‖ < 1`, `polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1) ^ n`. -/
theorem polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (hasSum_polylog n hz).tsum_eq.symm

/-- Natural-weight form of `hasSum_polylog`, with natural-number powers in the denominator. -/
theorem hasSum_polylog_nat (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  simpa using hasSum_polylog (n : ℤ) hz

/-- For any nonzero integer weight `n ≠ 0` and `‖z‖ < 1`, starting the series at `k = 0` gives the
same sum `polylog n z`, since `(0 : ℂ) ^ n = 0` kills the `k = 0` term. -/
theorem hasSum_polylog_zero_index {n : ℤ} (hn : n ≠ 0) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ k / (k : ℂ) ^ n) (polylog n z) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, zero_zpow n hn, div_zero, sub_zero]
  simpa [Nat.cast_add, Nat.cast_one] using hasSum_polylog n hz

/-- For every `n : ℤ` and `r < 1`, the polylogarithm power series converges uniformly to
`polylog n` on the closed subdisc `Metric.closedBall 0 r`. -/
theorem hasSumUniformlyOn_polylog (n : ℤ) {r : ℝ} (hr : r < 1) :
    HasSumUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) (Metric.closedBall 0 r) := by
  set r' : ℝ := max r 0
  have hr'1 : ‖r'‖ < 1 := by
    rw [Real.norm_of_nonneg (le_max_right r 0)]
    exact max_lt hr zero_lt_one
  have hunif : HasSumUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (fun z ↦ ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n) (Metric.closedBall 0 r') :=
    HasSumUniformlyOn.of_norm_le_summable
      ((summable_pow_mul_geometric_of_norm_lt_one (-n).toNat (r := r') hr'1).comp_injective
        (add_left_injective 1))
      fun k z hz ↦ norm_pow_div_zpow_le n (by simpa using hz) k
  refine (hunif.mono (Metric.closedBall_subset_closedBall (le_max_left r 0))).congr_right
    fun z hz ↦ ?_
  have hz1 : ‖z‖ < 1 := (mem_closedBall_zero_iff.1 hz).trans_lt hr
  exact (polylog_eq_tsum n hz1).symm

/-- For every `n : ℤ`, the polylogarithm power series converges locally uniformly to `polylog n`
on the open unit disc `Metric.ball 0 1`. -/
theorem hasSumLocallyUniformlyOn_polylog (n : ℤ) :
    HasSumLocallyUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) (Metric.ball 0 1) := by
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun z hz ↦ ?_
  have hz1 : ‖z‖ < 1 := by simpa using hz
  refine ⟨Metric.closedBall 0 ((‖z‖ + 1) / 2),
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds_of_mem (by simp; linarith)),
    hasSumUniformlyOn_polylog n (by linarith)⟩

/-- On the open unit disc `‖z‖ < 1`, `polylog (n + 1)` has complex derivative
`∑' k : ℕ, z ^ k / (k + 1) ^ n`. -/
theorem hasDerivAt_polylog_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog (n + 1)) (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ n) z := by
  refine (hasDerivAt_tsum_pow_div_zpow n hz).congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hz : z ∈ Metric.ball 0 1)]
    with w hw
  exact polylog_eq_tsum (n + 1) (by simpa using hw)

/-- Every integer-weight polylogarithm has complex derivative `1` at the origin. -/
theorem hasDerivAt_polylog_zero (n : ℤ) : HasDerivAt (polylog n) 1 0 := by
  have h := hasDerivAt_polylog_of_norm_lt_one (n - 1) (z := 0) (by simp)
  rw [sub_add_cancel] at h
  convert h using 1
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

/-- The derivative of `polylog n` at `0` is `1` for every `n : ℤ`. -/
@[simp] theorem deriv_polylog_zero (n : ℤ) : deriv (polylog n) 0 = 1 :=
  (hasDerivAt_polylog_zero n).deriv

/-- On the open unit disc `‖z‖ < 1`, every integer weight satisfies the Euler differential
recursion `z * deriv (polylog (n + 1)) z = polylog n z`. -/
theorem mul_deriv_polylog_add_one_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  rw [(hasDerivAt_polylog_of_norm_lt_one n hz).deriv, ← tsum_mul_left, polylog_eq_tsum n hz]
  congr 1 with k
  rw [← mul_div_assoc, pow_succ']

/-- At `z = 1 / 2` in weight `0`, the disc series reduces to `∑_{k ≥ 0} 2 ^ (-(k + 1)) = 1`,
agreeing with `polylog 0 (1 / 2) = 1`. -/
theorem hasSum_polylog_zero_weight_half :
    HasSum (fun k : ℕ ↦ ((2 : ℂ)⁻¹) ^ (k + 1)) 1 := by
  have h := hasSum_polylog 0 (z := (1 / 2 : ℂ)) (by norm_num)
  rw [polylog_zero_weight_half] at h
  simpa [one_div] using h

/-- At `z = 1 / 2` in weight `-1`, the disc series reduces to
`∑_{k ≥ 0} (k + 1) * 2 ^ (-(k + 1)) = 2`, agreeing with `polylog (-1) (1 / 2) = 2`. -/
theorem hasSum_polylog_neg_one_half :
    HasSum (fun k : ℕ ↦ (k + 1 : ℂ) * ((2 : ℂ)⁻¹) ^ (k + 1)) 2 := by
  have h := hasSum_polylog (-1) (z := (1 / 2 : ℂ)) (by norm_num)
  rw [polylog_neg_one_half] at h
  refine h.congr_fun fun k ↦ ?_
  rw [zpow_neg_one, div_inv_eq_mul, mul_comm, one_div]

/-- At `z = 1 / 2` in weight `2`, the first partial sum `1 / 2` approximates `Li₂(1 / 2)` within
`1 / 8`. -/
theorem norm_polylog_two_half_sub_half_le :
    ‖polylog 2 (1 / 2) - 1 / 2‖ ≤ 1 / 8 := by
  have hz : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hnhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  have htail := (hasSum_nat_add_iff' 1).2 (hasSum_polylog_nat 2 hz)
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, one_pow, div_one] at htail
  have htail' : HasSum (fun k : ℕ ↦ (1 / 2 : ℂ) ^ (k + 1 + 1) / ((k + 1 : ℕ) + 1 : ℂ) ^ 2)
      (polylog 2 (1 / 2) - 1 / 2) := htail
  rw [← htail'.tsum_eq]
  have hgeom : HasSum (fun k : ℕ ↦ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (k + 2)) (1 / 8 : ℝ) := by
    have hg := ((hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left ((1 / 2 : ℝ) ^ 2)).mul_left (1 / 4 : ℝ)
    convert hg using 1
    · ext k; ring
    · norm_num
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact ((summable_norm_pow_div_zpow 2 hz).comp_injective (add_left_injective 1)).congr
      fun k ↦ by simp [Nat.add_assoc]
  · rw [← hgeom.tsum_eq]
    refine Summable.tsum_le_tsum (fun k ↦ ?_) ?_ hgeom.summable
    · have hsq : (4 : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      have hnormk : ‖((k + 1 : ℕ) + 1 : ℂ) ^ 2‖ = ((k : ℝ) + 2) ^ 2 := by
        rw [norm_pow]
        have hc : ((k + 1 : ℕ) + 1 : ℂ) = ((k + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [hc, Complex.norm_natCast]
        push_cast
        ring
      rw [norm_div, norm_pow, hnormk, hnhalf, Nat.add_assoc, div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (by rw [one_div]; exact inv_anti₀ (by positivity) hsq) (by positivity)
    · exact ((summable_norm_pow_div_zpow 2 hz).comp_injective (add_left_injective 1)).congr
        fun k ↦ by simp [Nat.add_assoc]

end TauCeti.Polylog
