/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower

/-!
# Power series of principal polylogarithms on the open unit disc

On the open unit disc `‖z‖ < 1`, the principal polylogarithm `TauCeti.Polylog.polylog` of every
integer weight `n` expands as the classical power series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`,
with absolute convergence at each point of the open disc and uniform convergence on every closed
subdisc `‖z‖ ≤ r` (`r < 1`).

In weights `n ≥ 2` the series is obtained from the logarithmic radial integral by expanding
`-Complex.log (1 - t z)` in powers of `t z`, exchanging sum and integral via dominated convergence
against `|log t| ^ (n - 2)`, and evaluating the resulting logarithmic moments with
`TauCeti.integral_pow_mul_neg_log_pow`. Weight one is Mathlib's logarithm series, and nonpositive
weights follow from the geometric series in weight zero by iterating the Euler operator `z d/dz`
term by term on the open disc. Evaluating the termwise derivative at the origin gives
`deriv (polylog n) 0 = 1` for every integer weight `n`, without dividing by `z`.

## Main declarations

* `TauCeti.Polylog.summable_norm_polylogSeries` and `TauCeti.Polylog.summable_polylogSeries`:
  absolute convergence of the polylogarithm series on `‖z‖ < 1` in every integer weight.
* `TauCeti.Polylog.hasSum_polylog` and `TauCeti.Polylog.tsum_polylog`: identification of the disc
  series with `polylog n z` for `‖z‖ < 1`.
* `TauCeti.Polylog.tendstoUniformlyOn_polylog`: uniform convergence of the partial sums to
  `polylog n` on closed subdiscs `Metric.closedBall 0 r` with `r < 1`.
* `TauCeti.Polylog.hasDerivAt_polylog_of_norm_lt_one`, `TauCeti.Polylog.hasDerivAt_polylog_zero`,
  `TauCeti.Polylog.deriv_polylog_zero`, and
  `TauCeti.Polylog.mul_deriv_polylog_add_one_of_norm_lt_one`: termwise derivative on the open disc,
  complex derivative `1` at the origin, and the Euler recursion on the open disc.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (1), p. 50.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, introduction, p. 5.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti.Polylog

private lemma summable_pow_mul_geometric_succ (m : ℕ) {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    Summable (fun k : ℕ ↦ (k + 1 : ℝ) ^ m * R ^ (k + 1)) := by
  have hnorm : ‖R‖ < 1 := by rwa [Real.norm_of_nonneg hR0]
  have h := (summable_nat_add_iff 1).2
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) m hnorm)
  exact h.congr fun k ↦ by push_cast; rfl

private lemma norm_polylogSeriesTerm_le (n : ℤ) (k : ℕ) {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖ ≤ (k + 1 : ℝ) ^ (-n).toNat * R ^ (k + 1) := by
  have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hnorm_base : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by
    rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
  rw [norm_div, norm_pow, norm_zpow, hnorm_base]
  have hzpow : ‖z‖ ^ (k + 1) ≤ R ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg z) hz (k + 1)
  rcases le_or_gt 0 n with hn | hn
  · have htoNat : (-n).toNat = 0 := Int.toNat_of_nonpos (neg_nonpos.2 hn)
    rw [htoNat, pow_zero, one_mul]
    exact (div_le_self (by positivity) (one_le_zpow₀ hk1 hn)).trans hzpow
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, n = -((r + 1 : ℕ) : ℤ) :=
      ⟨(-n - 1).toNat, by omega⟩
    have htoNat : (- -((r + 1 : ℕ) : ℤ)).toNat = r + 1 := by simp
    rw [htoNat, zpow_neg, zpow_natCast, div_inv_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hzpow (by positivity)

/-- The polylogarithm power series converges absolutely at every point of the open unit disc,
in every integer weight `n`. For negative weights the polynomial factor `(k + 1) ^ (-n)` is
absorbed by `‖z‖ ^ (k + 1)`. -/
theorem summable_norm_polylogSeries (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ norm_polylogSeriesTerm_le n k le_rfl)
    (summable_pow_mul_geometric_succ (-n).toNat (norm_nonneg z) hz)

/-- The polylogarithm power series is summable on the open unit disc in every integer weight. -/
theorem summable_polylogSeries (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) :=
  (summable_norm_polylogSeries n hz).of_norm

private lemma hasDerivAt_tsum_polylogSeries (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ (n - 1)) z := by
  set R : ℝ := (‖z‖ + 1) / 2 with hR_def
  have hR0 : 0 < R := by linarith [hR_def, norm_nonneg z]
  have hzR : ‖z‖ < R := by linarith [hR_def]
  have hR1 : R < 1 := by linarith [hR_def]
  have hu : Summable (fun k : ℕ ↦ R⁻¹ * ((k + 1 : ℝ) ^ (-(n - 1)).toNat * R ^ (k + 1))) :=
    (summable_pow_mul_geometric_succ (-(n - 1)).toNat hR0.le hR1).mul_left R⁻¹
  refine hasDerivAt_tsum_of_isPreconnected (α := ℕ) (𝕜 := ℂ) (F := ℂ)
    (g := fun k (w : ℂ) ↦ w ^ (k + 1) / (k + 1 : ℂ) ^ n)
    (g' := fun k (w : ℂ) ↦ w ^ k / (k + 1 : ℂ) ^ (n - 1))
    (y₀ := 0) hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected (fun k w _ ↦ ?_) (fun k w hw ↦ ?_)
    (Metric.mem_ball_self hR0) ?_ (by simpa using hzR)
  · have hk0 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hd := ((hasDerivAt_pow (k + 1) w).div_const ((k + 1 : ℂ) ^ n))
    refine hd.congr_deriv ?_
    rw [Nat.add_sub_cancel, div_eq_mul_inv, div_eq_mul_inv, zpow_sub₀ hk0, zpow_one, inv_div]
    push_cast
    ring
  · have hwR : ‖w‖ ≤ R := (by simpa using hw : ‖w‖ < R).le
    have hterm : ‖w ^ k / (k + 1 : ℂ) ^ (n - 1)‖ * R ≤
        (k + 1 : ℝ) ^ (-(n - 1)).toNat * R ^ (k + 1) := by
      rcases eq_or_ne w 0 with rfl | hw0
      · rcases eq_or_ne k 0 with rfl | hk
        · simp
        · rw [zero_pow hk, zero_div, norm_zero, zero_mul]
          positivity
      · have hmul : ‖w ^ k / (k + 1 : ℂ) ^ (n - 1)‖ * ‖w‖ =
            ‖w ^ (k + 1) / (k + 1 : ℂ) ^ (n - 1)‖ := by
          rw [pow_succ, norm_div, norm_div, norm_mul, div_mul_eq_mul_div]
        calc
          ‖w ^ k / (k + 1 : ℂ) ^ (n - 1)‖ * R
              = ‖w ^ k / (k + 1 : ℂ) ^ (n - 1)‖ * ‖w‖ * (R / ‖w‖) := by
                  field_simp [norm_ne_zero_iff.2 hw0]
          _ = ‖w ^ (k + 1) / (k + 1 : ℂ) ^ (n - 1)‖ * (R / ‖w‖) := by rw [hmul]
          _ ≤ ((k + 1 : ℝ) ^ (-(n - 1)).toNat * ‖w‖ ^ (k + 1)) * (R / ‖w‖) := by
                gcongr
                exact norm_polylogSeriesTerm_le (n - 1) k le_rfl
          _ = (k + 1 : ℝ) ^ (-(n - 1)).toNat * (‖w‖ ^ k * R) := by
                rw [pow_succ]
                field_simp [norm_ne_zero_iff.2 hw0]
          _ ≤ (k + 1 : ℝ) ^ (-(n - 1)).toNat * (R ^ k * R) := by
                gcongr
          _ = (k + 1 : ℝ) ^ (-(n - 1)).toNat * R ^ (k + 1) := by rw [← pow_succ]
    calc
      ‖w ^ k / (k + 1 : ℂ) ^ (n - 1)‖
          = R⁻¹ * (‖w ^ k / (k + 1 : ℂ) ^ (n - 1)‖ * R) := by field_simp [hR0.ne']
      _ ≤ R⁻¹ * ((k + 1 : ℝ) ^ (-(n - 1)).toNat * R ^ (k + 1)) := by gcongr
  · exact summable_polylogSeries n (by simp)

private lemma mul_deriv_tsum_polylogSeries (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n) z =
      ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ (n - 1) := by
  rw [(hasDerivAt_tsum_polylogSeries n hz).deriv, ← tsum_mul_left]
  congr 1 with k
  rw [mul_div_assoc', mul_comm z, ← pow_succ]

private lemma hasSum_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun m : ℕ ↦ z ^ (m + 1) / (m + 1 : ℂ) ^ ((k + 2 : ℕ) : ℤ))
      (polylog (k + 2 : ℕ) z) := by
  let F : ℕ → ℝ → ℂ := fun m t ↦
    ((t ^ m * (-Real.log t) ^ k : ℝ) : ℂ) * (z ^ (m + 1) / (m + 1 : ℂ))
  let bound : ℕ → ℝ → ℝ := fun m t ↦ ‖z‖ ^ (m + 1) * |Real.log t| ^ k
  have hgeom : Summable (fun m : ℕ ↦ ‖z‖ ^ (m + 1)) := by
    simpa only [pow_succ'] using (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖z‖
  have hint_sum : HasSum (fun m : ℕ ↦ ∫ t : ℝ in 0..1, F m t)
      (∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound
      (fun m ↦ (by fun_prop : Measurable (F m)).aestronglyMeasurable)
      (fun m ↦ ?_) ?_ ?_ ?_
    · refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have ht0 : 0 ≤ t := ht.1.le
      have htm : t ^ m ≤ 1 := pow_le_one₀ ht0 ht.2
      have hm1 : (1 : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hnorm_m : ‖(m + 1 : ℂ)‖ = (m + 1 : ℝ) := by
        rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
      dsimp only [F, bound]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 m),
        abs_pow, abs_neg, norm_div, norm_pow, hnorm_m]
      calc
        t ^ m * |Real.log t| ^ k * (‖z‖ ^ (m + 1) / (m + 1 : ℝ))
            ≤ 1 * |Real.log t| ^ k * (‖z‖ ^ (m + 1) / 1) := by
                gcongr
        _ = ‖z‖ ^ (m + 1) * |Real.log t| ^ k := by ring
    · exact ae_of_all _ fun t _ ↦ hgeom.mul_right (|Real.log t| ^ k)
    · have htsum : (fun t : ℝ ↦ ∑' m : ℕ, bound m t) =
          fun t : ℝ ↦ (∑' m : ℕ, ‖z‖ ^ (m + 1)) * ‖Real.log t ^ k‖ := by
        ext t
        rw [tsum_mul_right, Real.norm_eq_abs, abs_pow]
      rw [htsum]
      exact (TauCeti.intervalIntegrable_log_pow k).norm.const_mul _
    · refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have htz : ‖(t : ℂ) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
      have hlog := ((Complex.hasSum_taylorSeries_neg_log' htz).mul_left
        (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ)
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.1.ne'
      refine hlog.congr_fun fun m ↦ ?_
      dsimp only [F]
      push_cast
      rw [mul_pow, pow_succ ((t : ℂ)) m]
      field_simp [ht_ne]
  have hscaled := hint_sum.mul_left (k.factorial : ℂ)⁻¹
  rw [← polylog_nat_add_two k z] at hscaled
  refine hscaled.congr_fun fun m ↦ ?_
  have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hm1 : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  dsimp only [F]
  rw [zpow_natCast, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    TauCeti.integral_pow_mul_neg_log_pow m k]
  push_cast
  have hpow : (m + 1 : ℂ) ^ (k + 2) = (m + 1 : ℂ) ^ (k + 1) * (m + 1 : ℂ) := by
    rw [pow_succ]
  rw [hpow]
  field_simp [hkf, hm1]

private lemma tsum_polylog_neg_nat (r : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ))) = polylog (-(r : ℤ)) z := by
  induction r generalizing z with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, zpow_zero, div_one, polylog_zero_weight]
    have h := (hasSum_geometric_of_norm_lt_one hz).mul_left z
    simpa only [pow_succ', div_eq_mul_inv] using h.tsum_eq
  | succ r ih =>
    have hev : (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ))) =ᶠ[𝓝 z]
        polylog (-(r : ℤ)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hz : z ∈ Metric.ball 0 1)]
        with w hw
      exact ih (by simpa using hw)
    rw [polylog_neg_nat_succ r z, ← hev.deriv_eq, mul_deriv_tsum_polylogSeries (-(r : ℤ)) hz]
    congr 1 with k
    congr 2
    push_cast
    ring

/-- On the open unit disc `‖z‖ < 1`, the principal polylogarithm of every integer weight `n` is the
sum of `z ^ (k + 1) / (k + 1) ^ n`. -/
theorem hasSum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · have h := tsum_polylog_neg_nat 0 hz
      simp only [Nat.cast_zero, neg_zero] at h
      exact h ▸ (summable_polylogSeries 0 hz).hasSum
    · simpa using hasSum_polylog_one hz
    · exact hasSum_polylog_nat_add_two k hz
  | negSucc r =>
    have h := tsum_polylog_neg_nat (r + 1) hz
    have hcast : -((r + 1 : ℕ) : ℤ) = Int.negSucc r := rfl
    rw [hcast] at h
    exact h ▸ (summable_polylogSeries (Int.negSucc r) hz).hasSum

/-- Infinite-sum form of the polylogarithm disc series on `‖z‖ < 1` in every integer weight. -/
theorem tsum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n) = polylog n z :=
  (hasSum_polylog n hz).tsum_eq

/-- On every closed subdisc `‖z‖ ≤ r` with `r < 1`, the partial sums of the polylogarithm power
series converge uniformly to `polylog n`. When `r < 0` the closed ball is empty and the statement
holds vacuously. -/
theorem tendstoUniformlyOn_polylog (n : ℤ) {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn (fun N z ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (Metric.closedBall 0 r) := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · rw [Metric.closedBall_eq_empty.2 hr0]
    exact tendstoUniformlyOn_empty
  · have hunif := tendstoUniformlyOn_tsum_nat
      (f := fun k (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (s := Metric.closedBall (0 : ℂ) r)
      (summable_pow_mul_geometric_succ (-n).toNat hr0 hr)
      (fun k z hz ↦ norm_polylogSeriesTerm_le n k (by simpa using hz))
    refine hunif.congr_right fun z hz ↦ ?_
    have hz1 : ‖z‖ < 1 := (by simpa using hz : ‖z‖ ≤ r).trans_lt hr
    exact tsum_polylog n hz1

/-- On the open unit disc `‖z‖ < 1`, `polylog n` is complex differentiable with derivative given
by the termwise derivative `∑' k : ℕ, z ^ k / (k + 1) ^ (n - 1)` of its power series. -/
theorem hasDerivAt_polylog_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog n) (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ (n - 1)) z := by
  have hev : (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n) =ᶠ[𝓝 z] polylog n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hz : z ∈ Metric.ball 0 1)]
      with w hw
    exact tsum_polylog n (by simpa using hw)
  exact (hasDerivAt_tsum_polylogSeries n hz).congr_of_eventuallyEq hev.symm

/-- Every integer-weight polylogarithm has complex derivative `1` at the origin, read off from the
linear coefficient `z / 1 ^ n = z` of the disc series without dividing by `z`. -/
theorem hasDerivAt_polylog_zero (n : ℤ) : HasDerivAt (polylog n) 1 0 := by
  have hd := hasDerivAt_polylog_of_norm_lt_one n (z := 0) (by simp)
  have h0 : (∑' k : ℕ, (0 : ℂ) ^ k / (k + 1 : ℂ) ^ (n - 1)) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro k hk
      simp [zero_pow hk]
  rwa [h0] at hd

/-- The derivative of `polylog n` at `0` is `1` in every integer weight. -/
@[simp] theorem deriv_polylog_zero (n : ℤ) : deriv (polylog n) 0 = 1 :=
  (hasDerivAt_polylog_zero n).deriv

/-- On the open unit disc `‖z‖ < 1`, the Euler operator `z d/dz` lowers the integer weight of
`polylog` by one, including at `z = 0`. -/
theorem mul_deriv_polylog_add_one_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  rw [(hasDerivAt_polylog_of_norm_lt_one (n + 1) hz).deriv, add_sub_cancel_right, ← tsum_mul_left,
    ← tsum_polylog n hz]
  congr 1 with k
  rw [mul_div_assoc', mul_comm z, ← pow_succ]

/-- At `z = 1 / 2`, the weight-zero disc series `∑_{k ≥ 0} (1 / 2) ^ (k + 1)` sums to `1`,
matching the rational normalization `polylog 0 (1 / 2) = 1`. -/
theorem hasSum_polylog_zero_weight_half :
    HasSum (fun k : ℕ ↦ (1 / 2 : ℂ) ^ (k + 1)) 1 := by
  have h := hasSum_polylog 0 (z := (1 / 2 : ℂ)) (by norm_num)
  rw [polylog_zero_weight_half] at h
  exact h.congr_fun fun k ↦ by simp

/-- At `z = 1 / 2`, the weight-minus-one disc series `∑_{k ≥ 0} (k + 1) (1 / 2) ^ (k + 1)` sums
to `2`, matching the Euler derivative `polylog (-1) (1 / 2) = 2`. -/
theorem hasSum_polylog_neg_one_half :
    HasSum (fun k : ℕ ↦ (k + 1 : ℂ) * (1 / 2 : ℂ) ^ (k + 1)) 2 := by
  have h := hasSum_polylog (-1) (z := (1 / 2 : ℂ)) (by norm_num)
  rw [polylog_neg_one_half] at h
  refine h.congr_fun fun k ↦ ?_
  rw [zpow_neg_one, div_inv_eq_mul, mul_comm]

end TauCeti.Polylog
