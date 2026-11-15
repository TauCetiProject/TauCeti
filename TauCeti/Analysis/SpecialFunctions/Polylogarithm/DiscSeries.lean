/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Analytic

/-!
# The unit-disc power series of integer-weight polylogarithms

Inside the open unit disc `‖z‖ < 1`, every integer-weight polylogarithm `TauCeti.Polylog.polylog n`
is represented by its classical power series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`, where the
denominator is the integer power `(k + 1 : ℂ) ^ n`. The series converges absolutely on `‖z‖ < 1`,
uniformly on every closed sub-disc of radius `r < 1`, and locally uniformly on `Metric.ball 0 1`.

Differentiating the power series termwise on `‖z‖ < 1` expresses `deriv (polylog n) z` as
`∑_{k ≥ 0} z ^ k / (k + 1) ^ (n - 1)`, resolving the removable singularity of the quotient
recursion `polylog (n - 1) z / z` at the origin; evaluating at `z = 0` shows that `polylog n` has
complex derivative `1` at `0` in every integer weight.

## Main declarations

* `TauCeti.Polylog.hasSum_polylog`, `TauCeti.Polylog.polylog_eq_tsum`: the power-series expansion
  `∑ z ^ (k + 1) / (k + 1) ^ n = polylog n z` for `‖z‖ < 1` and `n : ℤ`.
* `TauCeti.Polylog.hasSum_norm_polylog`: absolute convergence of the disc series, with norm sum
  `(polylog n ‖z‖).re`.
* `TauCeti.Polylog.hasSumUniformlyOn_polylog_closedBall`,
  `TauCeti.Polylog.hasSumLocallyUniformlyOn_polylog`: uniform convergence on closed sub-discs
  `r < 1` and locally uniform convergence on `Metric.ball 0 1`.
* `TauCeti.Polylog.hasSum_deriv_polylog`: termwise derivative series on `‖z‖ < 1`.
* `TauCeti.Polylog.hasDerivAt_polylog_zero`, `TauCeti.Polylog.deriv_polylog_zero`: every
  `polylog n` has complex derivative `1` at `0`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.1, (1), p. 50.
* Don Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*,
  Springer (2007), Part I, introduction, p. 5.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace TauCeti.Polylog

private lemma norm_pow_succ_div_zpow (n : ℤ) (z : ℂ) (k : ℕ) :
    ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖ = ‖z‖ ^ (k + 1) / (k + 1 : ℝ) ^ n := by
  rw [norm_div, norm_pow, norm_zpow, ← Complex.ofReal_natCast, ← Complex.ofReal_one,
    ← Complex.ofReal_add, Complex.norm_of_nonneg (by positivity)]

private lemma summable_pow_succ_div_zpow (n : ℤ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun k : ℕ ↦ r ^ (k + 1) / (k + 1 : ℝ) ^ n) := by
  rcases le_or_gt 0 n with hn | hn
  · refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      ((summable_geometric_of_lt_one hr0 hr).mul_left r)
    rw [← pow_succ']
    exact div_le_self (by positivity) (one_le_zpow₀ (by linarith) hn)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    have hgeom : Summable (fun j : ℕ ↦ (j : ℝ) ^ m * r ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one m (by rwa [Real.norm_of_nonneg hr0])
    refine (hgeom.comp_injective (add_left_injective 1)).congr fun k ↦ ?_
    dsimp only [Function.comp_def]
    rw [zpow_neg, div_inv_eq_mul, zpow_natCast, Nat.cast_add, Nat.cast_one, mul_comm]

private lemma hasDerivAt_tsum_pow_succ_div_zpow (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (∑' k : ℕ, z ^ k / (k + 1 : ℂ) ^ (n - 1)) z := by
  set ρ : ℝ := (1 + ‖z‖) / 2
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hρz : ‖z‖ < ρ := by dsimp [ρ]; linarith
  have hu : Summable (fun k : ℕ ↦ ρ⁻¹ * (ρ ^ (k + 1) / (k + 1 : ℝ) ^ (n - 1))) :=
    (summable_pow_succ_div_zpow (n - 1) hρ0.le hρ1).mul_left ρ⁻¹
  have hg : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) ρ →
      HasDerivAt (fun w : ℂ ↦ w ^ (k + 1) / (k + 1 : ℂ) ^ n)
        (w ^ k / (k + 1 : ℂ) ^ (n - 1)) w := by
    intro k w _
    have hc : (k + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero k
    convert ((hasDerivAt_pow (k + 1) w).div_const ((k + 1 : ℂ) ^ n)) using 1
    rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, zpow_sub₀ hc, zpow_one,
      div_div_eq_mul_div, mul_comm (w ^ k)]
  have hg' : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) ρ →
      ‖w ^ k / (k + 1 : ℂ) ^ (n - 1)‖ ≤
        ρ⁻¹ * (ρ ^ (k + 1) / (k + 1 : ℝ) ^ (n - 1)) := by
    intro k w hw
    have hwρ : ‖w‖ ≤ ρ := (mem_ball_zero_iff.mp hw).le
    have hnorm : ‖w ^ k / (k + 1 : ℂ) ^ (n - 1)‖ = ‖w‖ ^ k / (k + 1 : ℝ) ^ (n - 1) := by
      rw [norm_div, norm_pow, norm_zpow, ← Complex.ofReal_natCast, ← Complex.ofReal_one,
        ← Complex.ofReal_add, Complex.norm_of_nonneg (by positivity)]
    have hρpow : ρ⁻¹ * (ρ ^ (k + 1) / (k + 1 : ℝ) ^ (n - 1)) =
        ρ ^ k / (k + 1 : ℝ) ^ (n - 1) := by
      rw [pow_succ', ← mul_div_assoc, inv_mul_cancel_left₀ hρ0.ne']
    rw [hnorm, hρpow]
    gcongr
  have hg0 : Summable (fun k : ℕ ↦ (0 : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n) := by
    simp only [zero_pow (Nat.succ_ne_zero _), zero_div]
    exact summable_zero
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected hg hg' (Metric.mem_ball_self hρ0) hg0
    (mem_ball_zero_iff.mpr hρz)

private lemma hasSum_polylog_nat (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ (m : ℤ)) (polylog m z) := by
  induction m generalizing z with
  | zero =>
    rw [Nat.cast_zero, polylog_zero_weight, div_eq_mul_inv]
    simpa [pow_succ'] using (hasSum_geometric_of_norm_lt_one hz).mul_left z
  | succ m ih =>
    have hslit : 1 - z ∈ Complex.slitPlane :=
      Or.inl (by simp; linarith [Complex.re_le_norm z])
    have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    rw [hcast, polylog_add_one_eq_integral (m : ℤ) hslit]
    let F : ℕ → ℝ → ℂ := fun k t ↦ (z ^ (k + 1) / (k + 1 : ℂ) ^ (m : ℤ)) * (t : ℂ) ^ k
    have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := volume) (a := 0) (b := 1)
      (F := F) (f := fun t ↦ polylog m ((t : ℂ) * z) / (t : ℂ))
      (fun k _ ↦ ‖z‖ ^ (k + 1) / (k + 1 : ℝ) ^ (m : ℤ))
      (fun k ↦ (by fun_prop : Continuous (F k)).aestronglyMeasurable)
      (fun k ↦ .of_forall fun t ht ↦ by
        rw [uIoc_of_le zero_le_one] at ht
        dsimp only [F]
        rw [norm_mul, norm_pow_succ_div_zpow, norm_pow, Complex.norm_of_nonneg ht.1.le]
        exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ ht.1.le ht.2))
      (.of_forall fun _ _ ↦ summable_pow_succ_div_zpow m (norm_nonneg z) hz)
      intervalIntegrable_const
      (.of_forall fun t ht ↦ by
        rw [uIoc_of_le zero_le_one] at ht
        have htz : ‖(t : ℂ) * z‖ < 1 := by
          rw [norm_mul, Complex.norm_of_nonneg ht.1.le]
          exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
        have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
        convert (ih htz).div_const (t : ℂ) using 2 with k
        dsimp only [F]
        rw [mul_pow, pow_succ' (t : ℂ)]
        field_simp)
    convert hdom using 2 with k
    have hint_pow : ∫ t : ℝ in 0..1, (t : ℂ) ^ k = (k + 1 : ℂ)⁻¹ := by
      have hcomm := Complex.ofRealCLM.intervalIntegral_comp_comm
        (μ := volume) (a := 0) (b := 1) ((continuous_pow k).intervalIntegrable 0 1)
      simp only [Complex.ofRealCLM_apply, Complex.ofReal_pow] at hcomm
      rw [hcomm, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
      push_cast
      rw [one_div]
    dsimp only [F]
    rw [intervalIntegral.integral_const_mul, hint_pow, zpow_add_one₀ (Nat.cast_add_one_ne_zero k),
      ← div_div, div_eq_mul_inv]

private lemma hasSum_polylog_neg_nat (r : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ))) (polylog (-(r : ℤ)) z) := by
  induction r generalizing z with
  | zero => simpa using hasSum_polylog_nat 0 hz
  | succ r ih =>
    have hev : polylog (-(r : ℤ)) =ᶠ[𝓝 z]
        fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ (-(r : ℤ)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
      exact (ih (mem_ball_zero_iff.mp hw)).tsum_eq.symm
    have hd := ((hasDerivAt_tsum_pow_succ_div_zpow (-(r : ℤ)) hz).congr_of_eventuallyEq hev).deriv
    have hsum : Summable (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ (-((r + 1 : ℕ) : ℤ))) :=
      .of_norm ((summable_pow_succ_div_zpow (-((r + 1 : ℕ) : ℤ)) (norm_nonneg z) hz).congr
        fun k ↦ (norm_pow_succ_div_zpow _ z k).symm)
    rw [polylog_neg_nat_succ, hd, ← tsum_mul_left]
    have heq : (fun k : ℕ ↦ z * (z ^ k / (k + 1 : ℂ) ^ (-(r : ℤ) - 1))) =
        (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ (-((r + 1 : ℕ) : ℤ))) := by
      ext k
      have hcast : -(r : ℤ) - 1 = -((r + 1 : ℕ) : ℤ) := by omega
      rw [hcast, ← mul_div_assoc, pow_succ']
    rw [heq]
    exact hsum.hasSum

/-- **Unit-disc power series.** For every integer weight `n` and `‖z‖ < 1`, the polylogarithm
series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n` converges to `polylog n z`. -/
theorem hasSum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast]
    exact hasSum_polylog_nat m hz
  | negSucc r =>
    exact hasSum_polylog_neg_nat (r + 1) hz

/-- For `‖z‖ < 1` and `n : ℤ`, `polylog n z` equals `∑' k : ℕ, z ^ (k + 1) / (k + 1) ^ n`. -/
theorem polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (hasSum_polylog n hz).tsum_eq.symm

/-- **Absolute convergence on the open unit disc.** For `‖z‖ < 1` and `n : ℤ`, the norms of the
polylogarithm series terms have sum `(polylog n ‖z‖).re`. -/
theorem hasSum_norm_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) (polylog n ‖z‖).re := by
  have hz' : ‖(‖z‖ : ℂ)‖ < 1 := by rwa [Complex.norm_of_nonneg (norm_nonneg z)]
  have heq : (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) =
      (fun k : ℕ ↦ Complex.reCLM ((‖z‖ : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n)) := by
    ext k
    rw [norm_pow_succ_div_zpow]
    have hcast : (‖z‖ : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n =
        ((‖z‖ ^ (k + 1) / (k + 1 : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.reCLM_apply, Complex.ofReal_re]
  rw [heq]
  exact Complex.reCLM.hasSum (hasSum_polylog n hz')

/-- For every `r < 1` and `n : ℤ`, the polylogarithm power series converges uniformly to
`polylog n` on `Metric.closedBall 0 r`. -/
theorem hasSumUniformlyOn_polylog_closedBall (n : ℤ) {r : ℝ} (hr : r < 1) :
    HasSumUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) (Metric.closedBall 0 r) := by
  set ρ : ℝ := max r 0
  have hρ0 : 0 ≤ ρ := le_max_right r 0
  have hρ1 : ρ < 1 := max_lt hr zero_lt_one
  have hunif := HasSumUniformlyOn.of_norm_le_summable
    (f := fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
    (s := Metric.closedBall (0 : ℂ) r)
    (summable_pow_succ_div_zpow n hρ0 hρ1) fun k z hz ↦ by
      have hzr : ‖z‖ ≤ ρ := (mem_closedBall_zero_iff.mp hz).trans (le_max_left r 0)
      rw [norm_pow_succ_div_zpow]
      gcongr
  refine hunif.congr_right fun z hz ↦ ?_
  have hz1 : ‖z‖ < 1 := (mem_closedBall_zero_iff.mp hz).trans_lt hr
  exact (polylog_eq_tsum n hz1).symm

/-- For every `n : ℤ`, the polylogarithm power series converges locally uniformly to `polylog n`
on the open unit disc `Metric.ball 0 1`. -/
theorem hasSumLocallyUniformlyOn_polylog (n : ℤ) :
    HasSumLocallyUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) (Metric.ball 0 1) := by
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun z hz ↦ ?_
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  refine ⟨Metric.closedBall 0 ((1 + ‖z‖) / 2), ?_,
    hasSumUniformlyOn_polylog_closedBall n (by linarith)⟩
  exact nhdsWithin_le_nhds
    (Metric.closedBall_mem_nhds_of_mem (mem_ball_zero_iff.mpr (by linarith)))

/-- Termwise derivative of the polylogarithm disc series on `‖z‖ < 1`. -/
theorem hasSum_deriv_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ k / (k + 1 : ℂ) ^ (n - 1)) (deriv (polylog n) z) := by
  have hev : polylog n =ᶠ[𝓝 z] fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
    exact polylog_eq_tsum n (mem_ball_zero_iff.mp hw)
  have hd := ((hasDerivAt_tsum_pow_succ_div_zpow n hz).congr_of_eventuallyEq hev).deriv
  set ρ : ℝ := (1 + ‖z‖) / 2
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hρz : ‖z‖ ≤ ρ := by dsimp [ρ]; linarith
  have hu : Summable (fun k : ℕ ↦ ρ⁻¹ * (ρ ^ (k + 1) / (k + 1 : ℝ) ^ (n - 1))) :=
    (summable_pow_succ_div_zpow (n - 1) hρ0.le hρ1).mul_left ρ⁻¹
  have hsum : Summable (fun k : ℕ ↦ z ^ k / (k + 1 : ℂ) ^ (n - 1)) := by
    refine .of_norm_bounded hu fun k ↦ ?_
    rw [norm_div, norm_pow, norm_zpow, ← Complex.ofReal_natCast, ← Complex.ofReal_one,
      ← Complex.ofReal_add, Complex.norm_of_nonneg (by positivity), pow_succ', ← mul_div_assoc,
      inv_mul_cancel_left₀ hρ0.ne']
    gcongr
  rw [hd]
  exact hsum.hasSum

/-- Every integer-weight polylogarithm has complex derivative `1` at `0`. -/
theorem hasDerivAt_polylog_zero (n : ℤ) :
    HasDerivAt (polylog n) 1 0 := by
  have hdiff : DifferentiableAt ℂ (polylog n) 0 :=
    differentiableAt_polylog n (by simp [Complex.one_mem_slitPlane])
  have h0 : HasSum (fun k : ℕ ↦ (0 : ℂ) ^ k / (k + 1 : ℂ) ^ (n - 1)) 1 := by
    convert hasSum_ite_eq (0 : ℕ) (1 : ℂ) with k
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [hk, zero_pow hk]
  have hd : deriv (polylog n) 0 = 1 :=
    (hasSum_deriv_polylog n (z := 0) (by simp)).unique h0
  simpa [hd] using hdiff.hasDerivAt

/-- The complex derivative of `polylog n` at `0` is `1` in every integer weight. -/
@[simp]
theorem deriv_polylog_zero (n : ℤ) :
    deriv (polylog n) 0 = 1 :=
  (hasDerivAt_polylog_zero n).deriv

end TauCeti.Polylog
