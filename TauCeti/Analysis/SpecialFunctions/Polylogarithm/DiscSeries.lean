/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPow
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# The open-disc power series of integer-weight polylogarithms

On the open unit disc `‖z‖ < 1`, the principal polylogarithm `TauCeti.Polylog.polylog` of every
integer weight `n : ℤ` equals the power series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`, with
absolute convergence at each point of the open disc, uniform convergence on every closed disc of
radius `r < 1`, and locally uniform convergence on `ball 0 1`.

This series unifies the three regimes of `polylog` (logarithmic radial integrals for `n ≥ 2`,
`-Complex.log (1 - z)` for `n = 1`, and iterated Euler derivatives of `z / (1 - z)` for `n ≤ 0`)
into a single analytic germ at the origin, supplying the disc identity needed to continue the
Euler differential recursion across the cut plane `{z : ℂ | 1 - z ∈ Complex.slitPlane}` and giving
the linear coefficient `deriv (polylog n) 0 = 1` in every integer weight.

## Main declarations

* `TauCeti.Polylog.hasSum_polylog`: `HasSum (fun k ↦ z ^ (k + 1) / (k + 1) ^ n) (polylog n z)` for
  `‖z‖ < 1` and every `n : ℤ`, with `tsum` form `TauCeti.Polylog.polylog_eq_tsum`.
* `TauCeti.Polylog.summable_norm_polylog_series` and `TauCeti.Polylog.summable_polylog_series`:
  absolute convergence on the open unit disc.
* `TauCeti.Polylog.hasSumUniformlyOn_polylog` and
  `TauCeti.Polylog.hasSumLocallyUniformlyOn_polylog`: uniform convergence on closed discs of radius
  `r < 1` and locally uniform convergence on `ball 0 1`.
* `TauCeti.Polylog.hasFPowerSeriesOnBall_polylog`: formal power series representation at `0` on the
  open unit ball.
* `TauCeti.Polylog.hasDerivAt_tsum_polylog_series`,
  `TauCeti.Polylog.hasDerivAt_polylog_add_one_tsum`, and
  `TauCeti.Polylog.deriv_polylog_add_one_tsum`: termwise derivative of the polylogarithm power
  series and of `polylog (n + 1)` on the open unit disc.
* `TauCeti.Polylog.hasDerivAt_polylog_zero` and `TauCeti.Polylog.deriv_polylog_zero`: every
  integer-weight polylogarithm has complex derivative `1` at `0`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (1)–(3), p. 50.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II,
  Springer (2007), Part I, introduction, p. 5.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology ENNReal NNReal

namespace TauCeti.Polylog

/-- The disc power series of `polylog n` converges absolutely at every `z` with `‖z‖ < 1`. -/
theorem summable_norm_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ ‖z ^ (k + 1) / ((k : ℂ) + 1) ^ n‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ TauCeti.norm_pow_div_natCast_add_one_zpow_le n (k + 1) k le_rfl)
    ((summable_pow_mul_geometric_of_norm_lt_one (r := ‖z‖) (-n).toNat
      (by rwa [Real.norm_of_nonneg (norm_nonneg z)])).comp_injective Nat.succ_injective)

/-- The disc power series of `polylog n` is summable at every `z` with `‖z‖ < 1`. -/
theorem summable_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ ↦ z ^ (k + 1) / ((k : ℂ) + 1) ^ n) :=
  (summable_norm_polylog_series n hz).of_norm

/-- On the open unit disc `‖z‖ < 1`, the polylogarithm power series
`w ↦ ∑' k : ℕ, w ^ (k + 1) / (k + 1) ^ (n + 1)` has complex derivative
`∑' k : ℕ, z ^ k / (k + 1) ^ n`. -/
theorem hasDerivAt_tsum_polylog_series (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / ((k : ℂ) + 1) ^ (n + 1))
      (∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ n) z := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR0 : 0 < R := (norm_nonneg z).trans_lt hzR
  set g : ℕ → ℂ → ℂ := fun k w ↦ w ^ (k + 1) / ((k : ℂ) + 1) ^ (n + 1)
  set g' : ℕ → ℂ → ℂ := fun k w ↦ w ^ k / ((k : ℂ) + 1) ^ n
  have hg_deriv : ∀ k : ℕ, ∀ w ∈ ball (0 : ℂ) R, HasDerivAt (g k) (g' k w) w := by
    intro k w _
    have hk0 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hd := (hasDerivAt_pow (k + 1) w).div_const (((k : ℂ) + 1) ^ (n + 1))
    refine hd.congr_deriv ?_
    dsimp only [g']
    rw [Nat.add_sub_cancel, Nat.cast_add_one, zpow_add_one₀ hk0, mul_comm (((k : ℂ) + 1) ^ n),
      mul_div_mul_left _ _ hk0]
  have hg'_le : ∀ k : ℕ, ∀ w ∈ ball (0 : ℂ) R,
      ‖g' k w‖ ≤ R⁻¹ * (((k + 1 : ℕ) : ℝ) ^ (-n).toNat * R ^ (k + 1)) := by
    intro k w hw
    rw [mem_ball_zero_iff] at hw
    calc ‖g' k w‖
        ≤ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * R ^ k :=
          TauCeti.norm_pow_div_natCast_add_one_zpow_le n k k hw.le
      _ = R⁻¹ * (((k + 1 : ℕ) : ℝ) ^ (-n).toNat * R ^ (k + 1)) := by
          rw [pow_succ' R k]
          field_simp [hR0.ne']
  have hu : Summable (fun k : ℕ ↦ R⁻¹ * (((k + 1 : ℕ) : ℝ) ^ (-n).toNat * R ^ (k + 1))) :=
    ((summable_pow_mul_geometric_of_norm_lt_one (r := R) (-n).toNat
      (by rwa [Real.norm_of_nonneg hR0.le])).comp_injective Nat.succ_injective).mul_left R⁻¹
  have hg0 : Summable (fun k : ℕ ↦ g k 0) := by simp [g]
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball 0 R).isPreconnected
    hg_deriv hg'_le (mem_ball_self hR0) hg0 (mem_ball_zero_iff.mpr hzR)

/-- Radial integral of a single Taylor term of `-Complex.log (1 - t z)` against
`(-Real.log t) ^ k / t`. -/
private lemma integral_radial_taylor_term (k j : ℕ) (z : ℂ) :
    (∫ t : ℝ in 0..1,
      ((-Real.log t : ℝ) : ℂ) ^ k * (((t : ℂ) * z) ^ (j + 1) / ((j : ℂ) + 1)) / (t : ℂ)) =
      (Nat.factorial k : ℂ) * (z ^ (j + 1) / ((j : ℂ) + 1) ^ (k + 2)) := by
  have hcongr :
      (∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (((t : ℂ) * z) ^ (j + 1) / ((j : ℂ) + 1)) / (t : ℂ)) =
      ∫ t : ℝ in 0..1,
        (z ^ (j + 1) / ((j : ℂ) + 1)) * (((t ^ j * (-Real.log t) ^ k : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    push_cast
    rw [mul_pow, pow_succ' (t : ℂ) j]
    field_simp [ht0]
  rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    TauCeti.integral_pow_mul_neg_log_pow j k]
  push_cast
  have hj0 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [pow_succ ((j : ℂ) + 1) (k + 1)]
  field_simp [hj0]

/-- Power-series expansion of `polylog (k + 2)` on the open unit disc. -/
private lemma hasSum_polylog_nat_add_two (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ ↦ z ^ (j + 1) / ((j : ℂ) + 1) ^ (k + 2)) (polylog (k + 2 : ℕ) z) := by
  set F : ℕ → ℝ → ℂ := fun j t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (((t : ℂ) * z) ^ (j + 1) / ((j : ℂ) + 1)) / (t : ℂ)
  have hsum_int : HasSum (fun j : ℕ ↦ ∫ t : ℝ in 0..1, F j t)
      (∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun j t ↦ |Real.log t| ^ k * ‖z‖ ^ (j + 1))
      (fun j ↦ (by fun_prop : Measurable (F j)).aestronglyMeasurable) ?_ ?_ ?_ ?_
    · intro j
      refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
      have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
      have hF_eq : F j t =
          ((-Real.log t : ℝ) : ℂ) ^ k * (t : ℂ) ^ j * z ^ (j + 1) / ((j : ℂ) + 1) := by
        dsimp only [F]
        rw [mul_pow, pow_succ' (t : ℂ) j]
        field_simp [ht0]
      rw [hF_eq, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_neg, Complex.norm_real,
        Real.norm_of_nonneg ht.1.le, ← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
      have htj : t ^ j ≤ 1 := pow_le_one₀ ht.1.le ht.2
      calc |Real.log t| ^ k * t ^ j * ‖z‖ ^ (j + 1) / ((j : ℝ) + 1)
          ≤ |Real.log t| ^ k * 1 * ‖z‖ ^ (j + 1) / 1 := by gcongr
        _ = |Real.log t| ^ k * ‖z‖ ^ (j + 1) := by ring
    · refine ae_of_all _ fun t _ ↦ ?_
      exact ((summable_geometric_of_lt_one (norm_nonneg z) hz).comp_injective
        Nat.succ_injective).mul_left (|Real.log t| ^ k)
    · have htsum : (fun t : ℝ ↦ ∑' j : ℕ, |Real.log t| ^ k * ‖z‖ ^ (j + 1)) =
          fun t : ℝ ↦ (∑' j : ℕ, ‖z‖ ^ (j + 1)) * ‖Real.log t ^ k‖ := by
        ext t
        rw [tsum_mul_left, mul_comm, Real.norm_eq_abs, abs_pow]
      rw [htsum]
      exact (TauCeti.intervalIntegrable_log_pow k).norm.const_mul _
    · refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have htz : ‖(t : ℂ) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
      exact ((Complex.hasSum_taylorSeries_neg_log' htz).mul_left
        (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ)
  have hmul := hsum_int.mul_left (Nat.factorial k : ℂ)⁻¹
  rw [← polylog_nat_add_two k z] at hmul
  refine hmul.congr_fun fun j ↦ ?_
  have hfac : (Nat.factorial k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [integral_radial_taylor_term k j z, inv_mul_cancel_left₀ hfac]

/-- Power-series expansion of nonpositive weights `-(r : ℤ)` on the open unit disc. -/
private lemma hasSum_polylog_neg_nat (r : ℕ) :
    ∀ {z : ℂ}, ‖z‖ < 1 →
      HasSum (fun k : ℕ ↦ z ^ (k + 1) / ((k : ℂ) + 1) ^ (-(r : ℤ))) (polylog (-(r : ℤ)) z) := by
  induction r with
  | zero =>
    intro z hz
    simpa [polylog_zero_weight, pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one hz).mul_left z
  | succ r ih =>
    intro z hz
    have htsum_deriv := hasDerivAt_tsum_polylog_series (-((r + 1 : ℕ) : ℤ)) hz
    rw [show -((r + 1 : ℕ) : ℤ) + 1 = -(r : ℤ) by push_cast; ring] at htsum_deriv
    have heq :
        polylog (-(r : ℤ)) =ᶠ[𝓝 z]
          fun w : ℂ ↦ ∑' k : ℕ, w ^ (k + 1) / ((k : ℂ) + 1) ^ (-(r : ℤ)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
      exact (ih (mem_ball_zero_iff.mp hw)).tsum_eq.symm
    have hderiv_eq :
        deriv (polylog (-(r : ℤ))) z =
          ∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ (-((r + 1 : ℕ) : ℤ)) :=
      (htsum_deriv.congr_of_eventuallyEq heq).deriv
    convert (summable_polylog_series (-((r + 1 : ℕ) : ℤ)) hz).hasSum using 1
    rw [polylog_neg_nat_succ r z, hderiv_eq, ← tsum_mul_left]
    exact tsum_congr fun k ↦ by rw [pow_succ', mul_div_assoc]

/-- On the open unit disc `‖z‖ < 1`, every integer-weight polylogarithm is the sum of its power
series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`. -/
theorem hasSum_polylog (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / ((k : ℂ) + 1) ^ n) (polylog n z) := by
  cases n with
  | ofNat m =>
    rcases m with _ | _ | k
    · simpa using hasSum_polylog_neg_nat 0 hz
    · simpa using hasSum_polylog_one hz
    · rw [Int.ofNat_eq_natCast]
      simp_rw [zpow_natCast]
      exact hasSum_polylog_nat_add_two k hz
  | negSucc r =>
    exact hasSum_polylog_neg_nat (r + 1) hz

/-- Series expansion `polylog n z = ∑' k : ℕ, z ^ (k + 1) / (k + 1) ^ n` on the open unit disc. -/
theorem polylog_eq_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog n z = ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) ^ n :=
  (hasSum_polylog n hz).tsum_eq.symm

/-- The power series of `polylog n` converges uniformly on every closed disc `closedBall 0 r` of
radius `r < 1`. -/
theorem hasSumUniformlyOn_polylog (n : ℤ) {r : ℝ} (hr : r < 1) :
    HasSumUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / ((k : ℂ) + 1) ^ n) (polylog n)
      (closedBall 0 r) := by
  have hmax1 : max r 0 < 1 := max_lt hr zero_lt_one
  have hu : Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * max r 0 ^ (k + 1)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (r := max r 0) (-n).toNat
      (by rwa [Real.norm_of_nonneg (le_max_right r 0)])).comp_injective Nat.succ_injective
  have hfu : ∀ k : ℕ, ∀ z ∈ closedBall (0 : ℂ) r,
      ‖z ^ (k + 1) / ((k : ℂ) + 1) ^ n‖ ≤
        ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * max r 0 ^ (k + 1) := by
    intro k z hz
    rw [mem_closedBall_zero_iff] at hz
    exact TauCeti.norm_pow_div_natCast_add_one_zpow_le n (k + 1) k (hz.trans (le_max_left r 0))
  refine (HasSumUniformlyOn.of_norm_le_summable hu hfu).congr_right fun z hz ↦ ?_
  rw [mem_closedBall_zero_iff] at hz
  exact (polylog_eq_tsum n (hz.trans_lt hr)).symm

/-- The power series of `polylog n` converges locally uniformly on the open unit disc `ball 0 1`. -/
theorem hasSumLocallyUniformlyOn_polylog (n : ℤ) :
    HasSumLocallyUniformlyOn (fun (k : ℕ) (z : ℂ) ↦ z ^ (k + 1) / ((k : ℂ) + 1) ^ n) (polylog n)
      (ball 0 1) := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKne continuous_norm.continuousOn
    have hz₀1 : ‖z₀‖ < 1 := mem_ball_zero_iff.mp (hK hz₀)
    have hsub : K ⊆ closedBall 0 ‖z₀‖ := fun z hz ↦
      mem_closedBall_zero_iff.mpr (isMaxOn_iff.mp hmax z hz)
    exact (hasSumUniformlyOn_polylog n hz₀1).tendstoUniformlyOn.mono hsub

/-- Formal power series representation of `polylog n` centered at `0` on the open unit ball. -/
theorem hasFPowerSeriesOnBall_polylog (n : ℤ) :
    HasFPowerSeriesOnBall (polylog n)
      (.ofScalars ℂ fun k : ℕ ↦ if k = 0 then 0 else (k : ℂ) ^ (-n)) 0 1 where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    have hu : Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-n).toNat * (r : ℝ) ^ (k + 1)) :=
      (summable_pow_mul_geometric_of_norm_lt_one (r := (r : ℝ)) (-n).toNat
        (by rwa [Real.norm_of_nonneg r.coe_nonneg])).comp_injective Nat.succ_injective
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_) hu
    rw [FormalMultilinearSeries.ofScalars_norm]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg r.coe_nonneg (k + 1))
    have hk : 1 ≤ ‖((k + 1 : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos k
    have h := TauCeti.norm_zpow_le_pow_toNat hk (-n)
    rwa [Complex.norm_natCast] at h
  r_pos := zero_lt_one
  hasSum := by
    intro y hy
    rw [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm] at hy
    have hy' : ‖y‖ < 1 := by exact_mod_cast hy
    rw [zero_add, ← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, FormalMultilinearSeries.ofScalars_apply_eq, ↓reduceIte,
      Nat.succ_ne_zero, smul_eq_mul, zero_mul, sub_zero]
    refine (hasSum_polylog n hy').congr_fun fun k ↦ ?_
    rw [Nat.cast_add_one, zpow_neg, div_eq_mul_inv, mul_comm]

/-- On the open unit disc `‖z‖ < 1`, `polylog (n + 1)` has complex derivative
`∑' k : ℕ, z ^ k / (k + 1) ^ n`. -/
theorem hasDerivAt_polylog_add_one_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polylog (n + 1)) (∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ n) z := by
  refine (hasDerivAt_tsum_polylog_series n hz).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
  exact polylog_eq_tsum (n + 1) (mem_ball_zero_iff.mp hw)

/-- Power-series expansion of `deriv (polylog (n + 1)) z` on the open unit disc `‖z‖ < 1`. -/
theorem deriv_polylog_add_one_tsum (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (polylog (n + 1)) z = ∑' k : ℕ, z ^ k / ((k : ℂ) + 1) ^ n :=
  (hasDerivAt_polylog_add_one_tsum n hz).deriv

/-- Every integer-weight polylogarithm has complex derivative `1` at the origin. -/
theorem hasDerivAt_polylog_zero (n : ℤ) : HasDerivAt (polylog n) 1 0 := by
  have hd := hasDerivAt_polylog_add_one_tsum (n - 1) (z := 0) (by simp)
  rw [sub_add_cancel] at hd
  refine hd.congr_deriv ?_
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

/-- The complex derivative of `polylog n` at `0` is `1` in every integer weight. -/
@[simp] theorem deriv_polylog_zero (n : ℤ) : deriv (polylog n) 0 = 1 :=
  (hasDerivAt_polylog_zero n).deriv

end TauCeti.Polylog
