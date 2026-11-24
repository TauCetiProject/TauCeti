/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Polylogarithms on the closed unit disc and their zeta values

For every integer weight `n ≥ 2`, the principal polylogarithm `Liₙ` is continuous on the closed
unit disc `‖z‖ ≤ 1`, and its disc series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n` converges to it
absolutely and uniformly there, boundary circle included. At `z = 1` this gives the zeta value
`Liₙ(1) = ζ(n)`, in particular `Li₂(1) = π² / 6`, and on the unit circle it identifies
`Liₙ(e^{2πia})` with Mathlib's exponential zeta function `HurwitzZeta.expZeta a n`. The
duplication relation `Liₙ(z²) = 2 ^ (n - 1) (Liₙ(z) + Liₙ(-z))` holds on the whole closed disc;
at `z = 1` it gives `Liₙ(-1) = (2 ^ (1 - n) - 1) ζ(n)`, in particular `Li₂(-1) = -π² / 12`.

Continuity comes from the defining radial integral: on the closed disc the principal logarithm
satisfies `‖Log (1 - t z)‖ ≤ -log (1 - t)` for `0 ≤ t < 1`, so the radial integrand at `z = 1`
dominates the integrand at every `z` of the disc, and `1 - t z` stays in the right half-plane,
where the principal logarithm is continuous. The disc series converges uniformly on the closed
disc by comparison with `∑ (k + 1) ^ (-n)`, so its sum is continuous there too. The two
continuous functions agree on the open disc, hence on its closure.

The hypothesis `2 ≤ n` cannot be dropped: in weights `n ≤ 1` the point `1` is a pole or a
logarithmic singularity of `Liₙ`.

## Main results

* `TauCeti.Polylog.continuousOn_polylog_closedBall`: `polylog n` is continuous on
  `Metric.closedBall 0 1` for `2 ≤ n`.
* `TauCeti.Polylog.hasSum_polylog_of_norm_le_one` and
  `TauCeti.Polylog.hasSum_norm_polylog_of_norm_le_one`: the disc series converges, absolutely,
  to `polylog n z` for `‖z‖ ≤ 1`; `TauCeti.Polylog.polylog_eq_tsum_of_norm_le_one` is its `tsum`
  form.
* `TauCeti.Polylog.tendstoUniformlyOn_polylog_closedBall_one`: its partial sums converge
  uniformly on `Metric.closedBall 0 1`.
* `TauCeti.Polylog.polylog_one_eq_riemannZeta` and `TauCeti.Polylog.polylog_two_one`:
  `polylog n 1 = riemannZeta n` and `polylog 2 1 = π ^ 2 / 6`.
* `TauCeti.Polylog.polylog_exp_eq_expZeta`: `polylog n (exp (2 π i a)) = expZeta a n`.
* `TauCeti.Polylog.polylog_sq_of_norm_le_one`:
  `polylog n (z ^ 2) = 2 ^ (n - 1) * (polylog n z + polylog n (-z))` for `‖z‖ ≤ 1`.
* `TauCeti.Polylog.polylog_neg_one_eq_mul_riemannZeta` and `TauCeti.Polylog.polylog_two_neg_one`:
  `polylog n (-1) = (2 ^ (1 - n) - 1) * riemannZeta n` and `polylog 2 (-1) = -(π ^ 2 / 12)`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.4, p. 51.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, §1, p. 6.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology Real

namespace TauCeti.Polylog

private theorem continuousOn_polylog_nat_add_two_closedBall (k : ℕ) :
    ContinuousOn (polylog (k + 2 : ℕ)) (closedBall 0 1) := by
  let F : ℂ → ℝ → ℂ := fun z t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)
  have hnorm {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
      ‖(t : ℂ) * z‖ ≤ t := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
    exact mul_le_of_le_one_right ht (mem_closedBall_zero_iff.mp hz)
  have hcont : ContinuousOn (fun z ↦ ∫ t in (0 : ℝ)..1, F z t) (closedBall 0 1) := by
    intro z₀ hz₀
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun t ↦ ‖F 1 t‖) ?_ ?_ (intervalIntegrable_radialIntegrand k 1).norm ?_
    · exact Eventually.of_forall fun z ↦
        (intervalIntegrable_iff.mp (intervalIntegrable_radialIntegrand k z)).aestronglyMeasurable
    · -- Domination by the integrand at `z = 1`, for `0 < t < 1`.
      filter_upwards [self_mem_nhdsWithin] with z hz
      filter_upwards [Measure.ae_ne volume 1] with t ht1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht0 : 0 < t := ht.1
      have ht1' : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hreal : Complex.log (1 - t) = Real.log (1 - t) := by
        rw [Complex.ofReal_log (by linarith), Complex.ofReal_sub, Complex.ofReal_one]
      have hlog : ‖Complex.log (1 - t * z)‖ ≤ ‖Complex.log (1 - t)‖ := by
        rw [hreal, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
        exact (Complex.norm_log_one_sub_le_neg_log_one_sub_norm
          ((hnorm ht0.le hz).trans_lt ht1')).trans
          (neg_le_neg (Real.log_le_log (by linarith) (by linarith [hnorm ht0.le hz])))
      simp only [F, norm_div, norm_mul, norm_neg, mul_one]
      gcongr
    · -- Pointwise continuity: for `0 < t < 1`, `1 - t z₀` lies in the right half-plane.
      filter_upwards [Measure.ae_ne volume 1] with t ht1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have hslit : 1 - (t : ℂ) * z₀ ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        have hre := (Complex.re_le_norm ((t : ℂ) * z₀)).trans (hnorm ht.1.le hz₀)
        rw [Complex.sub_re, Complex.one_re]
        linarith [lt_of_le_of_ne ht.2 ht1]
      have hlog : ContinuousAt (fun z ↦ Complex.log (1 - (t : ℂ) * z)) z₀ :=
        (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).clog hslit
      exact (continuousAt_const.mul hlog.neg).div_const _ |>.continuousWithinAt
  have hpoly : polylog (k + 2 : ℕ) = fun z ↦ (Nat.factorial k : ℂ)⁻¹ * ∫ t in (0 : ℝ)..1, F z t :=
    funext (polylog_nat_add_two k)
  rw [hpoly]
  exact continuousOn_const.mul hcont

/-- For every integer weight `n ≥ 2`, `polylog n` is continuous on the closed unit disc. -/
theorem continuousOn_polylog_closedBall {n : ℤ} (hn : 2 ≤ n) :
    ContinuousOn (polylog n) (closedBall 0 1) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k + 2 : ℕ) := ⟨(n - 2).toNat, by omega⟩
  exact continuousOn_polylog_nat_add_two_closedBall k

/-- **Closed-disc series of the polylogarithm.** For every integer weight `n ≥ 2` and every `z`
in the closed unit disc `‖z‖ ≤ 1`, the series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n` converges to
`polylog n z`. -/
theorem hasSum_polylog_of_norm_le_one {n : ℤ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n) (polylog n z) := by
  have hsum := summable_norm_inv_natCast_add_one_zpow ℂ hn
  have heq : EqOn (polylog n) (fun w ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (closedBall 0 1) :=
    EqOn.of_subset_closure (fun w hw ↦ polylog_eq_tsum n (mem_ball_zero_iff.mp hw))
      (continuousOn_polylog_closedBall hn)
      (continuousOn_tsum (fun k ↦ (continuous_pow (k + 1)).continuousOn.div_const _) hsum
        fun k _ hw ↦ norm_pow_div_le_norm_inv (mem_closedBall_zero_iff.mp hw) _ _)
      ball_subset_closedBall (closure_ball (0 : ℂ) one_ne_zero).ge
  have hz' : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz
  rw [heq hz']
  exact (Summable.of_norm_bounded hsum fun k ↦ norm_pow_div_le_norm_inv hz _ _).hasSum

/-- For every integer weight `n ≥ 2`, on the closed unit disc `‖z‖ ≤ 1`, `polylog n z` equals the
sum of its power series. -/
theorem polylog_eq_tsum_of_norm_le_one {n : ℤ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ n :=
  (hasSum_polylog_of_norm_le_one hn hz).tsum_eq.symm

/-- For every integer weight `n ≥ 2`, the polylogarithm disc series converges absolutely on the
closed unit disc `‖z‖ ≤ 1`, and the sum of the norms of its terms equals `(polylog n ‖z‖).re`. -/
theorem hasSum_norm_polylog_of_norm_le_one {n : ℤ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ ↦ ‖z ^ (k + 1) / (k + 1 : ℂ) ^ n‖) (polylog n ‖z‖).re := by
  have hz' : ‖(‖z‖ : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hz
  refine (Complex.reCLM.hasSum (hasSum_polylog_of_norm_le_one hn hz')).congr_fun fun k ↦ ?_
  have hreal : ((‖z‖ ^ (k + 1) / (k + 1 : ℝ) ^ n : ℝ) : ℂ) =
      (‖z‖ : ℂ) ^ (k + 1) / (k + 1 : ℂ) ^ n := by simp
  have hnorm_k : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by exact_mod_cast Complex.norm_natCast (k + 1)
  rw [Complex.reCLM_apply, ← hreal, Complex.ofReal_re]
  simp [norm_zpow, hnorm_k]

/-- For every integer weight `n ≥ 2`, the partial sums of the polylogarithm power series converge
uniformly to `polylog n` on the closed unit disc `Metric.closedBall 0 1`. -/
theorem tendstoUniformlyOn_polylog_closedBall_one {n : ℤ} (hn : 2 ≤ n) :
    TendstoUniformlyOn
      (fun N (z : ℂ) ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (closedBall 0 1) :=
  (tendstoUniformlyOn_tsum_nat (summable_norm_inv_natCast_add_one_zpow ℂ hn)
    fun _ _ hz ↦ norm_pow_div_le_norm_inv (mem_closedBall_zero_iff.mp hz) _ _).congr_right
      fun _ hz ↦ (hasSum_polylog_of_norm_le_one hn (mem_closedBall_zero_iff.mp hz)).tsum_eq

/-- **Zeta values of polylogarithms.** For every integer weight `n ≥ 2`, `Liₙ(1) = ζ(n)`. -/
theorem polylog_one_eq_riemannZeta {n : ℤ} (hn : 2 ≤ n) : polylog n 1 = riemannZeta n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  have h := (hasSum_nat_add_iff (f := fun k : ℕ ↦ 1 / (k : ℂ) ^ m) 1).mp
    (by simpa using hasSum_polylog_of_norm_le_one hn (z := 1) (by simp))
  rw [Int.cast_natCast, zeta_nat_eq_tsum_of_gt_one (by omega), h.tsum_eq]
  simp [zero_pow (by omega : m ≠ 0)]

/-- Euler's value of the dilogarithm at `1`: `Li₂(1) = ζ(2) = π ^ 2 / 6`. -/
theorem polylog_two_one : polylog 2 1 = (π : ℂ) ^ 2 / 6 := by
  rw [polylog_one_eq_riemannZeta le_rfl]
  exact_mod_cast riemannZeta_two

/-- **Polylogarithms on the unit circle.** For every integer weight `n ≥ 2` and every real `a`,
`Liₙ(e^{2πia})` is Mathlib's exponential zeta function `expZeta a n`, whose series is
`∑_{k ≥ 1} e^{2πiak} / k ^ n`. -/
theorem polylog_exp_eq_expZeta {n : ℤ} (hn : 2 ≤ n) (a : ℝ) :
    polylog n (Complex.exp (2 * π * Complex.I * a)) = HurwitzZeta.expZeta a n := by
  have hre : 1 < (n : ℂ).re := by
    rw [Complex.intCast_re]
    exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  have h := (hasSum_nat_add_iff' 1).mpr (HurwitzZeta.hasSum_expZeta_of_one_lt_re a hre)
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, Complex.exp_zero,
    Complex.zero_cpow hn0, div_zero, sub_zero] at h
  refine (hasSum_polylog_of_norm_le_one hn (by simp [Complex.norm_exp])).unique
    (h.congr_fun fun k ↦ ?_)
  rw [Complex.cpow_intCast, ← Complex.exp_natCast_mul]
  push_cast
  ring_nf

/-- **Duplication on the closed disc.** For every integer weight `n ≥ 2` and `‖z‖ ≤ 1`,
`Liₙ(z²) = 2 ^ (n - 1) (Liₙ(z) + Liₙ(-z))`, boundary circle included. -/
theorem polylog_sq_of_norm_le_one {n : ℤ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polylog n (z ^ 2) = (2 : ℂ) ^ (n - 1) * (polylog n z + polylog n (-z)) := by
  have hz2 : ‖z ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz
  -- In `Liₙ(z) + Liₙ(-z)` the even-indexed terms cancel and the odd-indexed terms double.
  have h : HasSum (fun k : ℕ ↦ z ^ (k + 1) / (k + 1 : ℂ) ^ n + (-z) ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (2 ^ (1 - n) * polylog n (z ^ 2)) := by
    have h20 : (2 : ℂ) ≠ 0 := two_ne_zero
    refine (zero_add (2 ^ (1 - n) * polylog n (z ^ 2))) ▸ HasSum.even_add_odd ?_ ?_
    · convert hasSum_zero with k
      simp [neg_pow z, pow_succ, pow_mul]
      ring
    · convert (hasSum_polylog_of_norm_le_one hn hz2).mul_left (2 ^ (1 - n)) using 2 with j
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul, pow_mul, neg_sq]
      push_cast
      rw [show (2 * j + 1 + 1 : ℂ) = 2 * (j + 1) by ring, mul_zpow, zpow_sub₀ h20, zpow_one]
      field_simp
      ring
  rw [((hasSum_polylog_of_norm_le_one hn hz).add
    (hasSum_polylog_of_norm_le_one hn (z := -z) (by rwa [norm_neg]))).unique h, ← mul_assoc,
    ← zpow_add₀ two_ne_zero]
  simp

/-- **The value at `-1`.** For every integer weight `n ≥ 2`, `Liₙ(-1) = (2 ^ (1 - n) - 1) ζ(n)`,
minus the alternating zeta value `∑_{k ≥ 1} (-1) ^ (k + 1) / k ^ n` expressed through `ζ(n)`. -/
theorem polylog_neg_one_eq_mul_riemannZeta {n : ℤ} (hn : 2 ≤ n) :
    polylog n (-1) = (2 ^ (1 - n) - 1) * riemannZeta n := by
  have h := polylog_sq_of_norm_le_one hn (z := 1) (by simp)
  rw [one_pow, polylog_one_eq_riemannZeta hn] at h
  have h2 : (2 : ℂ) ^ (1 - n) * 2 ^ (n - 1) = 1 := by
    rw [← zpow_add₀ two_ne_zero]; simp
  linear_combination -(2 : ℂ) ^ (1 - n) * h - (polylog n (-1) + riemannZeta n) * h2

/-- **The dilogarithm at `-1`.** `Li₂(-1) = -π² / 12`. -/
theorem polylog_two_neg_one : polylog 2 (-1) = -((π : ℂ) ^ 2 / 12) := by
  rw [polylog_neg_one_eq_mul_riemannZeta le_rfl]
  push_cast [riemannZeta_two]
  ring

end TauCeti.Polylog
