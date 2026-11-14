/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower

/-!
# The power series of the polylogarithm on the unit disc

For every integer weight `n : ℤ` and every `z : ℂ` in the open unit disc `‖z‖ < 1`, the principal
polylogarithm `Liₙ(z)` is given by the absolutely and locally uniformly convergent power series

`∑_{k = 0}^∞ z ^ (k + 1) / (k + 1) ^ n`.

In weights `n ≥ 2`, expanding `-Log (1 - t z)` in its Taylor series and integrating term by term
against `(-log t) ^ (n - 2) / t` via the logarithmic moment `∫₀¹ t ^ k * (-log t) ^ m dt =
m! / (k + 1) ^ (m + 1)` recovers each coefficient. Weight one is Mathlib's logarithm series, and
nonpositive weights follow by inducting with the Euler differential operator `z * d/dz` on the
geometric series `z / (1 - z) = ∑_{k = 0}^∞ z ^ (k + 1)`.

Differentiating the series term by term on the open unit disc gives `HasDerivAt (polylog n) 1 0`
in every integer weight—the linear term is `z / 1 ^ n = z`—and establishes the Euler recursion
`z * deriv (polylog (n + 1)) z = polylog n z` on `Metric.ball 0 1`.

## Main declarations

* `TauCeti.Polylog.summable_norm_polylog_series`, `TauCeti.Polylog.summable_polylog_series`,
  `TauCeti.Polylog.summable_norm_deriv_polylog_series`,
  `TauCeti.Polylog.summable_deriv_polylog_series`: absolute convergence of the polylogarithm series
  and its termwise derivative on `‖z‖ < 1`.
* `TauCeti.Polylog.hasSum_polylog`, `TauCeti.Polylog.hasSum_polylog_nat`,
  `TauCeti.Polylog.polylog_eq_tsum`: the disc-series expansion in every integer weight.
* `TauCeti.Polylog.tendstoUniformlyOn_polylog_series`: uniform convergence of the partial sums on
  every closed disc `Metric.closedBall 0 r` with `r < 1`.
* `TauCeti.Polylog.hasDerivAt_polylog_of_norm_lt_one`,
  `TauCeti.Polylog.mul_deriv_polylog_add_one_of_norm_lt_one`: termwise derivative and Euler
  differential recursion on the open unit disc.
* `TauCeti.Polylog.hasDerivAt_polylog_zero`, `TauCeti.Polylog.deriv_polylog_zero`: every integer
  weight has complex derivative `1` at `0`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (1), p. 50.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, introduction, p. 5.
-/

public section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti.Polylog

/-- For `0 ≤ r < 1` and every `n : ℤ`, the real majorant `r ^ k / (k + 1) ^ n` is summable. -/
private lemma summable_pow_div_zpow (n : ℤ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ ↦ r ^ k / (k + 1 : ℝ) ^ n) := by
  cases n with
  | ofNat m =>
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      (summable_geometric_of_lt_one hr0 hr1)
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact div_le_self (pow_nonneg hr0 k) (one_le_pow₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1))
  | negSucc m =>
    rcases eq_or_lt_of_le hr0 with rfl | hrpos
    · refine summable_of_ne_finset_zero (s := {0}) fun k hk ↦ ?_
      have hk0 : k ≠ 0 := Finset.notMem_singleton.mp hk
      simp [zero_pow hk0]
    · have hgeom : Summable (fun k : ℕ ↦ (k : ℝ) ^ (m + 1) * r ^ k) :=
        summable_pow_mul_geometric_of_norm_lt_one (m + 1) (by rwa [Real.norm_of_nonneg hr0])
      have hshift : Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (m + 1) * r ^ (k + 1)) :=
        hgeom.comp_injective Nat.succ_injective
      refine (hshift.mul_left r⁻¹).congr fun k ↦ ?_
      rw [zpow_negSucc, div_inv_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp [hrpos.ne']
      ring

private lemma norm_nat_add_one_zpow (n : ℤ) (k : ℕ) :
    ‖(k + 1 : ℂ) ^ n‖ = (k + 1 : ℝ) ^ n := by
  have hc : (k + 1 : ℂ) = ((k + 1 : ℕ) : ℂ) := by push_cast; rfl
  have hr : (k + 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; rfl
  rw [hc, hr, norm_zpow, Complex.norm_natCast]

/-- The polylogarithm disc series converges absolutely at every `z` with `‖z‖ < 1`. -/
theorem summable_norm_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) := by
  refine ((summable_pow_div_zpow n (norm_nonneg z) hz).mul_left ‖z‖).congr fun k ↦ ?_
  rw [norm_div, norm_pow, norm_nat_add_one_zpow, pow_succ', mul_div_assoc]

/-- The polylogarithm disc series is summable on the open unit disc in every integer weight. -/
theorem summable_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) :=
  (summable_norm_polylog_series n hz).of_norm

/-- The termwise-differentiated polylogarithm series `z ^ k / (k + 1) ^ n` converges absolutely on
the open unit disc. -/
theorem summable_norm_deriv_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ ‖z ^ k / (k + 1 : ℂ) ^ n‖) := by
  refine (summable_pow_div_zpow n (norm_nonneg z) hz).congr fun k ↦ ?_
  rw [norm_div, norm_pow, norm_nat_add_one_zpow]

/-- The termwise-differentiated polylogarithm series `z ^ k / (k + 1) ^ n` is summable on the open
unit disc. -/
theorem summable_deriv_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ z ^ k / (k + 1 : ℂ) ^ n) :=
  (summable_norm_deriv_polylog_series n hz).of_norm

/-- Termwise complex derivative of the raw series `∑' k, w ^ (k + 1) / (k + 1) ^ (n + 1)` on the
open unit disc. -/
private lemma hasDerivAt_tsum_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (n + 1))
      (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ n) z := by
  set r : ℝ := (‖z‖ + 1) / 2 with hr_def
  have hzr : ‖z‖ < r := by linarith [hr_def]
  have hr0 : 0 ≤ r := by linarith [hr_def, norm_nonneg z]
  have hr1 : r < 1 := by linarith [hr_def]
  have hterm : ∀ k : ℕ, ∀ w : ℂ,
      HasDerivAt (fun w : ℂ ↦ w ^ (k + 1) / (k + 1 : ℂ) ^ (n + 1))
        (w ^ k / (k + 1 : ℂ) ^ n) w := by
    intro k w
    have hk0 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hd := ((hasDerivAt_pow (k + 1) w).div_const ((k + 1 : ℂ) ^ (n + 1)))
    refine hd.congr_deriv ?_
    rw [zpow_add_one₀ hk0]
    push_cast
    field_simp [hk0, zpow_ne_zero n hk0]
  refine hasDerivAt_tsum_of_isPreconnected (t := ball (0 : ℂ) r)
    (summable_pow_div_zpow n hr0 hr1) isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
    (fun k w _ ↦ hterm k w) (fun k w hw ↦ ?_)
    (mem_ball_self (by linarith [hr_def, norm_nonneg z] : 0 < r))
    (summable_polylog_series (n + 1) (by simp)) (by simpa using hzr)
  have hw' : ‖w‖ ≤ r := (mem_ball_zero_iff.mp hw).le
  rw [norm_div, norm_pow, norm_nat_add_one_zpow]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg w) hw' k)
    (zpow_nonneg (by positivity) n)

private lemma integral_pow_mul_neg_log_pow_complex (m k : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ m * ((-Real.log t : ℝ) : ℂ) ^ k =
      (k.factorial : ℂ) / (m + 1 : ℂ) ^ (k + 1) := by
  have hreal : (fun t : ℝ ↦ (t : ℂ) ^ m * ((-Real.log t : ℝ) : ℂ) ^ k) =
      fun t : ℝ ↦ ((t ^ m * (-Real.log t) ^ k : ℝ) : ℂ) := by
    ext t; push_cast; rfl
  rw [hreal, intervalIntegral.integral_ofReal, TauCeti.integral_pow_mul_neg_log_pow m k]
  push_cast
  rfl

/-- In weights `k + 2 ≥ 2`, expanding `-Log (1 - t z)` on `‖z‖ < 1` and integrating termwise
against `(-log t) ^ k / t` gives the disc series. -/
private lemma hasSum_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun m : ℕ ↦ z ^ (m + 1) / (m + 1 : ℂ) ^ (k + 2)) (polylog (k + 2 : ℕ) z) := by
  let F : ℕ → ℝ → ℂ := fun m t ↦
    (z ^ (m + 1) / (m + 1 : ℂ)) * ((t : ℂ) ^ m * ((-Real.log t : ℝ) : ℂ) ^ k)
  let bound : ℕ → ℝ → ℝ := fun m t ↦ ‖z‖ ^ (m + 1) * |Real.log t| ^ k
  have hgeom : Summable (fun m : ℕ ↦ ‖z‖ ^ (m + 1)) :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖z‖ |>.congr
      fun m ↦ (pow_succ' ‖z‖ m).symm
  have hsum_int : HasSum (fun m : ℕ ↦ ∫ t : ℝ in (0 : ℝ)..1, F m t)
      (∫ t : ℝ in (0 : ℝ)..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound
      (fun m ↦ (by fun_prop : Measurable (F m)).aestronglyMeasurable)
      (fun m ↦ ae_of_all _ fun t ht ↦ ?_)
      (ae_of_all _ fun t _ ↦ hgeom.mul_right (|Real.log t| ^ k)) ?_
      (ae_of_all _ fun t ht ↦ ?_)
    · rw [uIoc_of_le zero_le_one] at ht
      have ht0 : 0 ≤ t := ht.1.le
      have htm : t ^ m ≤ 1 := pow_le_one₀ ht0 ht.2
      have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      have hdiv : ‖z‖ ^ (m + 1) / ((m : ℝ) + 1) ≤ ‖z‖ ^ (m + 1) :=
        div_le_self (pow_nonneg (norm_nonneg z) _) hm1
      have hmcast : (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; rfl
      dsimp only [F]
      rw [norm_mul, norm_div, norm_pow, hmcast, Complex.norm_natCast, Nat.cast_add, Nat.cast_one,
        norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_neg]
      calc (‖z‖ ^ (m + 1) / ((m : ℝ) + 1)) * (t ^ m * |Real.log t| ^ k)
          ≤ ‖z‖ ^ (m + 1) * (1 * |Real.log t| ^ k) := by gcongr
        _ = bound m t := by simp [bound]
    · have htsum : (fun t : ℝ ↦ ∑' m : ℕ, bound m t) =
          fun t : ℝ ↦ (∑' m : ℕ, ‖z‖ ^ (m + 1)) * ‖Real.log t ^ k‖ := by
        ext t; simp [bound, tsum_mul_right, Real.norm_eq_abs]
      rw [htsum]
      exact (TauCeti.intervalIntegrable_log_pow k).norm.const_mul _
    · rw [uIoc_of_le zero_le_one] at ht
      have htz : ‖(t : ℂ) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
      rw [mul_div_right_comm]
      refine ((Complex.hasSum_taylorSeries_neg_log' htz).mul_left
        (((-Real.log t : ℝ) : ℂ) ^ k / (t : ℂ))).congr_fun fun m ↦ ?_
      dsimp only [F]
      rw [mul_pow, pow_succ (t : ℂ) m]
      field_simp [ht_ne]
  rw [polylog_nat_add_two]
  refine (hsum_int.mul_left ((Nat.factorial k : ℂ)⁻¹)).congr_fun fun m ↦ ?_
  have hk_ne : (Nat.factorial k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hm_ne : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  dsimp only [F]
  rw [intervalIntegral.integral_const_mul, integral_pow_mul_neg_log_pow_complex,
    pow_succ' (m + 1 : ℂ) (k + 1)]
  field_simp [hk_ne, hm_ne]

/-- In nonpositive weights `-r`, iterating the Euler operator `z * d/dz` on the geometric series
gives the disc series. -/
private lemma hasSum_polylog_neg_nat (r : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ))) (polylog (-(r : ℤ)) z) := by
  suffices ∀ r : ℕ, ∀ w : ℂ, ‖w‖ < 1 →
      polylog (-(r : ℤ)) w = ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ)) by
    rw [this r z hz]
    exact (summable_polylog_series (-(r : ℤ)) hz).hasSum
  intro r
  induction r with
  | zero =>
    intro w hw
    simp only [Nat.cast_zero, neg_zero, polylog_zero_weight, zpow_zero, div_one, pow_succ',
      tsum_mul_left]
    rw [(hasSum_geometric_of_norm_lt_one hw).tsum_eq, div_eq_mul_inv]
  | succ r ih =>
    intro w hw
    have hev : polylog (-(r : ℤ)) =ᶠ[𝓝 w]
        fun u : ℂ ↦ ∑' k : ℕ, u ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw)] with u hu
      exact ih u (mem_ball_zero_iff.mp hu)
    have hshift : (-(r : ℤ)) = (-((r + 1 : ℕ) : ℤ)) + 1 := by push_cast; ring
    have hd : HasDerivAt (polylog (-(r : ℤ)))
        (∑' k : ℕ, w ^ k / (k + 1 : ℂ) ^ (-((r + 1 : ℕ) : ℤ))) w := by
      refine (HasDerivAt.congr_of_eventuallyEq ?_ hev)
      rw [hshift]
      exact hasDerivAt_tsum_polylog_series (-((r + 1 : ℕ) : ℤ)) hw
    rw [polylog_neg_nat_succ r w, hd.deriv, ← tsum_mul_left]
    refine tsum_congr fun k ↦ ?_
    rw [mul_div_assoc', pow_succ']

/-- On the open unit disc `‖z‖ < 1`, the principal polylogarithm `Liₙ(z)` is the sum of
`z ^ (k + 1) / (k + 1) ^ n` in every integer weight `n : ℤ`. -/
theorem hasSum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · simpa using hasSum_polylog_neg_nat 0 hz
    · simpa using hasSum_polylog_one hz
    · rw [Int.ofNat_eq_natCast]
      exact (hasSum_polylog_nat_add_two k hz).congr_fun fun m ↦ by rw [zpow_natCast]
  | negSucc r =>
    simpa [Int.negSucc_eq] using hasSum_polylog_neg_nat (r + 1) hz

/-- Natural-weight form of `hasSum_polylog`, using natural powers `(k + 1) ^ n`. -/
theorem hasSum_polylog_nat (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  simpa [zpow_natCast] using hasSum_polylog (n : ℤ) hz

/-- Series formula `Liₙ(z) = ∑' k, z ^ (k + 1) / (k + 1) ^ n` on `‖z‖ < 1`. -/
theorem polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (hasSum_polylog n hz).tsum_eq.symm

/-- The partial sums of the disc series converge uniformly to `polylog n` on every closed disc of
radius `r < 1`, establishing locally uniform convergence on the open unit disc. -/
theorem tendstoUniformlyOn_polylog_series (n : ℤ) {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn (fun N z ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (closedBall (0 : ℂ) r) := by
  set r' : ℝ := max r 0
  have hr'0 : 0 ≤ r' := le_max_right r 0
  have hr'1 : r' < 1 := max_lt hr zero_lt_one
  have hunif : TendstoUniformlyOn
      (fun N z ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (fun z : ℂ ↦ ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n) atTop (closedBall (0 : ℂ) r') := by
    refine tendstoUniformlyOn_tsum_nat
      ((summable_pow_div_zpow n hr'0 hr'1).mul_left r') fun k z hz ↦ ?_
    have hz' : ‖z‖ ≤ r' := by simpa using hz
    rw [norm_div, norm_pow, norm_nat_add_one_zpow, pow_succ']
    calc ‖z‖ * ‖z‖ ^ k / (k + 1 : ℝ) ^ n
        ≤ (r' * r' ^ k) / (k + 1 : ℝ) ^ n :=
          div_le_div_of_nonneg_right
            (mul_le_mul hz' (pow_le_pow_left₀ (norm_nonneg z) hz' k) (by positivity) hr'0)
            (zpow_nonneg (by positivity) n)
      _ = r' * (r' ^ k / (k + 1 : ℝ) ^ n) := mul_div_assoc _ _ _
  refine (hunif.mono (closedBall_subset_closedBall (le_max_left r 0))).congr_right fun z hz ↦ ?_
  have hz1 : ‖z‖ < 1 := (mem_closedBall_zero_iff.mp hz).trans_lt hr
  exact (polylog_eq_tsum n hz1).symm

/-- Termwise derivative of `polylog (n + 1)` on the open unit disc:
`(d/dz) Li_{n+1}(z) = ∑' k, z ^ k / (k + 1) ^ n`. -/
theorem hasDerivAt_polylog_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog (n + 1)) (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ n) z := by
  refine (hasDerivAt_tsum_polylog_series n hz).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
  exact polylog_eq_tsum (n + 1) (mem_ball_zero_iff.mp hw)

/-- The Euler differential recursion `z * Li'_{n+1}(z) = Liₙ(z)` on the open unit disc, including
`z = 0`. -/
theorem mul_deriv_polylog_add_one_of_norm_lt_one (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  rw [(hasDerivAt_polylog_of_norm_lt_one n hz).deriv, polylog_eq_tsum n hz, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  rw [mul_div_assoc', pow_succ']

/-- Every integer-weight polylogarithm has complex derivative `1` at `0`. -/
theorem hasDerivAt_polylog_zero (n : ℤ) : HasDerivAt (polylog n) 1 0 := by
  have h := hasDerivAt_polylog_of_norm_lt_one (n - 1) (z := 0) (by simp)
  rw [sub_add_cancel] at h
  refine h.congr_deriv ?_
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

/-- Every integer-weight polylogarithm has derivative `1` at `0`. -/
@[simp] theorem deriv_polylog_zero (n : ℤ) : deriv (polylog n) 0 = 1 :=
  (hasDerivAt_polylog_zero n).deriv

/-- Weight-zero disc series at `1 / 2` sums to `1`, agreeing with `polylog_zero_weight_half`. -/
theorem hasSum_polylog_zero_weight_half :
    HasSum (fun k : ℕ ↦ ((1 / 2 : ℂ) ^ (k + 1))) 1 := by
  have h := hasSum_polylog 0 (z := 1 / 2) (by norm_num)
  rw [polylog_zero_weight_half] at h
  exact h.congr_fun fun k ↦ by simp

/-- Weight `-1` disc series at `1 / 2` sums to `2`, agreeing with `polylog_neg_one_half`. -/
theorem hasSum_polylog_neg_one_half :
    HasSum (fun k : ℕ ↦ (k + 1 : ℂ) * (1 / 2 : ℂ) ^ (k + 1)) 2 := by
  have h := hasSum_polylog (-1) (z := 1 / 2) (by norm_num)
  rw [polylog_neg_one_half] at h
  exact h.congr_fun fun k ↦ by simp [mul_comm]

end TauCeti.Polylog
