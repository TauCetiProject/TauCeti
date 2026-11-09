/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.RingTheory.Norm.RCLike

/-!
# Additive Haar measures on real normed spaces

In a finite-dimensional real normed space, the real measure of a positive-radius ball is its radius
raised to the dimension times the real measure of the unit ball, independently of its centre;
equivalently, `n / r` times the measure of the ball of radius `r` is `n rⁿ⁻¹` times the measure of
the unit ball, where `n` is the dimension, and this is the derivative in `r` of the measure of the
ball. It agrees with the measure of the closed ball, which
therefore differs from the open ball by a null set. A set inside a closed ball with the measure of a
ball of the same radius likewise agrees with it up to a null set. In a nontrivial space, concentric
balls are ordered by measure as by radius, so the points `x` whose centered ball of radius `‖x‖` has
measure below `m` form a set of measure `m`. The ratio of the measures of two closed balls is
controlled by the ratio of their radii raised to the dimension, also for the restriction of the
measure to a set of positive density in the balls, the shell between concentric balls
has measure the difference of the powers of the radii, and the part of a ball outside a translate of
itself is controlled by the distance between the centres. The measure of an affine image
`y + r • S` relative to a ball of radius `r` is that of `S` relative to the unit ball, and a
homothety of ratio `r ≠ 0` pushes the measure forward to its multiple by `|r|⁻ⁿ`, and an
invertible affine map `x ↦ c + A x` pushes it to its multiple by `|det A|⁻¹`. Comparing the
measure of the image of the closed unit ball under a linear endomorphism `f` with that of the
closed ball of radius `‖f‖` bounds `|det f|` by `‖f‖` raised to the dimension; restricting scalars
to `ℝ` gives the same bound for `‖det f‖` over `ℂ`, or any `RCLike` field.

## Main results

* `MeasureTheory.Measure.addHaar_real_ball_of_pos`: the real measure of a positive-radius ball.
* `MeasureTheory.Measure.finrank_div_mul_addHaar_real_ball`:
  `(n / r) μ (ball x r) = n rⁿ⁻¹ μ (ball 0 1)` in dimension `n`.
* `MeasureTheory.Measure.hasDerivAt_measureReal_ball`: `ρ ↦ μ (ball x ρ)` has derivative
  `n rⁿ⁻¹ μ (ball 0 1)` at every `r > 0`.
* `MeasureTheory.Measure.addHaar_real_ball_mul_diam_ball_pow_div_le`:
  `μ (ball 0 1) (diam (ball x r))ⁿ⁺¹ / μ (ball x r) ≤ 2ⁿ⁺¹ r` in dimension `n`.
* `MeasureTheory.Measure.addHaar_real_ball_rpow_mul_diam_ball_pow_div_le`:
  `μ (ball 0 1) ^ (1 - 1/n) (diam (ball x r))ⁿ / μ (ball x r) ≤ 2ⁿ μ (ball 0 1) ^ (-1/n)` in
  dimension `n`.
* `MeasureTheory.Measure.addHaar_closedBall_ae_eq_ball`: closed and open balls agree up to a null
  set in a nontrivial space.
* `MeasureTheory.Measure.addHaar_closedBall_ae_eq_ball_of_ne_zero`: the same agreement at nonzero
  radius, including trivial spaces.
* `MeasureTheory.Measure.ae_eq_closedBall_of_subset_of_measure_eq`: a set inside a closed ball,
  with the measure of a closed ball of the same radius, agrees with it up to a null set.
* `MeasureTheory.Measure.addHaar_ball_lt_addHaar_ball_iff`: concentric balls are ordered by
  measure as by radius.
* `MeasureTheory.Measure.exists_nonneg_addHaar_ball_eq`: every finite nonnegative value is the
  measure of a centered ball in a nontrivial space.
* `MeasureTheory.Measure.setOf_addHaar_ball_norm_lt_addHaar_ball`: the points whose centered
  norm-radius ball has measure below that of the radius-`r` ball form exactly the radius-`r` ball.
* `MeasureTheory.Measure.setOf_measure_ball_norm_lt_top`: every centered norm-radius ball has
  finite measure for a measure finite on compact sets in a proper space.
* `MeasureTheory.Measure.addHaar_setOf_addHaar_ball_norm_lt`: in a nontrivial space, the set where
  the centered ball has measure below `m` has measure `m`.
* `MeasureTheory.Measure.addHaar_real_closedBall_div_le`: a closed ball of radius `R ≤ c r` has
  at most `cⁿ` times the measure of a closed ball of radius `r`.
* `MeasureTheory.Measure.addHaar_real_restrict_closedBall_div_le`,
  `MeasureTheory.Measure.ofReal_mul_rpow_mul_le_addHaar_restrict_closedBall`: for the restriction
  of the measure to a set `s` with density at least `c > 0` in a closed ball, the ratio of the
  measures of nearby balls is at most `2ⁿ / c`, and the measure of a ball of radius `r` is at
  least `c rⁿ` times that of the unit ball.
* `MeasureTheory.Measure.addHaar_real_closedBall_mul_eq_pow_mul_addHaar_real_ball`: the closed ball
  of radius `c r` has `cⁿ` times the measure of the open ball of radius `r`.
* `MeasureTheory.Measure.addHaar_real_closedBall_sdiff_ball`: the shell between the open ball of
  radius `r > 0` and the concentric closed ball of radius `s ≥ r` has measure `(sⁿ - rⁿ)` times
  that of the unit ball.
* `MeasureTheory.Measure.addHaar_real_ball_sdiff_ball_le`: the part of a ball outside a ball of the
  same radius `s` whose centre is at distance `d` is no larger than a spherical shell of radii `s`
  and `s + d`.
* `MeasureTheory.Measure.addHaar_image_add_smul_div_addHaar_closedBall`: the measure of
  `y + r • S` relative to a closed ball of radius `r > 0` is the measure of `S` relative to the
  unit ball.
* `MeasureTheory.Measure.map_addHaar_homothety`: a homothety of nonzero ratio `r` pushes an
  additive Haar measure to its multiple by `|r ^ n|⁻¹`.
* `MeasureTheory.Measure.map_affine_addHaar_eq_smul`: an invertible affine map `x ↦ c + A x` pushes
  an additive Haar measure to its multiple by `|det A|⁻¹`.
* `MeasureTheory.Measure.eLpNorm_ball_le_mul_rpow`: Hölder's inequality on a ball, with the volume
  of a ball of radius `R > 0` written through that of the unit ball (for `R ≤ 0` the ball is
  empty).
* `ContinuousLinearMap.abs_det_le_opNorm_pow`: `|det f| ≤ ‖f‖ ^ n` in dimension `n`.
* `ContinuousLinearMap.norm_det_le_opNorm_pow`: `‖det f‖ ≤ ‖f‖ ^ n` in dimension `n` over an
  `RCLike` field.
-/

public section

open MeasureTheory MeasureTheory.Measure Metric Module

namespace TauCeti

/-- The real measure of a ball of positive radius is the corresponding power of the radius times
the real measure of the unit ball. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_ball_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    mu.real (ball x r) = r ^ finrank ℝ E * mu.real (ball 0 1) := by
  rw [measureReal_def, mu.addHaar_ball_of_pos x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

/-- Hölder's inequality on a ball: for `p₀ ≤ p`, the `L^{p₀}` norm on `B(x₀, R)` is at most the
`L^p` norm times `(Rⁿ |B(0, 1)|)^{1/p₀ - 1/p}`, where `n` is the dimension. For `R > 0` this
factor is `|B(x₀, R)|^{1/p₀ - 1/p}`; for `R ≤ 0` the ball is empty, so the inequality holds
trivially and the factor need not be the volume. -/
theorem _root_.MeasureTheory.Measure.eLpNorm_ball_le_mul_rpow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] {f : E → F} {p₀ p R : ℝ} {x₀ : E}
    (hp₀0 : 0 < p₀) (hp₀p : p₀ ≤ p) (hf : AEStronglyMeasurable f (mu.restrict (ball x₀ R))) :
    eLpNorm f (ENNReal.ofReal p₀) (mu.restrict (ball x₀ R)) ≤
      eLpNorm f (ENNReal.ofReal p) (mu.restrict (ball x₀ R)) *
        ENNReal.ofReal ((R ^ finrank ℝ E * mu.real (ball (0 : E) 1)) ^ (1 / p₀ - 1 / p)) := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 hR]
  have he : 0 ≤ 1 / p₀ - 1 / p := sub_nonneg.2 (one_div_le_one_div_of_le hp₀0 hp₀p)
  have hV : mu (ball (0 : E) 1) = ENNReal.ofReal (mu.real (ball (0 : E) 1)) :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hvol : mu.restrict (ball x₀ R) Set.univ =
      ENNReal.ofReal (R ^ finrank ℝ E * mu.real (ball (0 : E) 1)) := by
    rw [Measure.restrict_apply_univ, Measure.addHaar_ball_of_pos mu x₀ hR, hV,
      ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_natCast]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.ofReal_le_ofReal hp₀p) hf
  rwa [hvol, ENNReal.toReal_ofReal hp₀0.le, ENNReal.toReal_ofReal (hp₀0.le.trans hp₀p),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) he] at h

/-- For a ball of radius `r > 0` in dimension `n`, `n / r` times its real measure is
`n rⁿ⁻¹` times the real measure of the unit ball, the derivative in `r` of its measure. -/
theorem _root_.MeasureTheory.Measure.finrank_div_mul_addHaar_real_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    finrank ℝ E / r * mu.real (ball x r) =
      finrank ℝ E * r ^ (finrank ℝ E - 1) * mu.real (ball 0 1) := by
  rcases (finrank ℝ E).eq_zero_or_pos with h0 | hpos
  · simp [h0]
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos hpos
  rw [mu.addHaar_real_ball_of_pos x hr]
  cases hn : finrank ℝ E with
  | zero => simp
  | succ k =>
    simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    field_simp
    ring

/-- The real measure of the ball of radius `ρ` about `x`, as a function of `ρ`, has derivative
`n rⁿ⁻¹` times the real measure of the unit ball at every `r > 0`, where `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.hasDerivAt_measureReal_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun ρ => mu.real (ball x ρ))
      (finrank ℝ E * r ^ (finrank ℝ E - 1) * mu.real (ball 0 1)) r := by
  refine ((hasDerivAt_pow (finrank ℝ E) r).mul_const (mu.real (ball 0 1))).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hr] with ρ hρ
  exact mu.addHaar_real_ball_of_pos x hρ

/-- For a ball of radius `r > 0` in dimension `n`, the ratio
`μ (ball 0 1) * (diam (ball x r)) ^ (n + 1) / μ (ball x r)` of real measures is at most
`2 ^ (n + 1) * r`. This is the constant of the Poincaré–Wirtinger inequality on a convex domain,
evaluated on a ball. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_ball_mul_diam_ball_pow_div_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    mu.real (ball 0 1) * diam (ball x r) ^ (finrank ℝ E + 1) / mu.real (ball x r) ≤
      2 ^ (finrank ℝ E + 1) * r := by
  have homega : 0 < mu.real (ball (0 : E) 1) :=
    Metric.measureReal_ball_pos mu 0 one_pos
  rw [mu.addHaar_real_ball_of_pos x hr, div_le_iff₀ (by positivity)]
  calc mu.real (ball (0 : E) 1) * diam (ball x r) ^ (finrank ℝ E + 1)
      ≤ mu.real (ball (0 : E) 1) * (2 * r) ^ (finrank ℝ E + 1) := by
        gcongr
        exact diam_ball hr.le
    _ = 2 ^ (finrank ℝ E + 1) * r * (r ^ finrank ℝ E * mu.real (ball (0 : E) 1)) := by ring

/-- For a ball of radius `r > 0` in dimension `n`, the ratio
`μ (ball 0 1) ^ (1 - 1/n) * (diam (ball x r)) ^ n / μ (ball x r)` of real measures is at most
`2 ^ n / μ (ball 0 1) ^ (1/n)`, whatever the radius. This is the constant of the localized
Poincaré–Wirtinger inequality on a convex domain, evaluated on a ball. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_ball_rpow_mul_diam_ball_pow_div_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    mu.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) * diam (ball x r) ^ finrank ℝ E /
        mu.real (ball x r) ≤
      2 ^ finrank ℝ E / mu.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹ := by
  set n := finrank ℝ E
  set ω := mu.real (ball (0 : E) 1)
  have homega : 0 < ω :=
    Metric.measureReal_ball_pos mu 0 one_pos
  rw [mu.addHaar_real_ball_of_pos x hr]
  calc ω ^ (1 - (n : ℝ)⁻¹) * diam (ball x r) ^ n / (r ^ n * ω)
      ≤ ω ^ (1 - (n : ℝ)⁻¹) * (2 * r) ^ n / (r ^ n * ω) := by
        gcongr
        exact diam_ball hr.le
    _ = 2 ^ n / ω ^ (n : ℝ)⁻¹ := by
        rw [Real.rpow_sub homega, Real.rpow_one]
        field_simp
        ring

/-- Closed and open balls agree up to a null set in a nontrivial finite-dimensional space. -/
theorem _root_.MeasureTheory.Measure.addHaar_closedBall_ae_eq_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [mu.IsAddHaarMeasure] (x : E) (r : ℝ) :
    closedBall x r =ᵐ[mu] ball x r :=
  (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
    (mu.addHaar_closedBall_eq_addHaar_ball x r).le
    measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm

/-- At nonzero radius, closed and open balls agree up to a null set even in a trivial space. -/
theorem _root_.MeasureTheory.Measure.addHaar_closedBall_ae_eq_ball_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [mu.IsAddHaarMeasure] (x : E) (r : ℝ) (hr : r ≠ 0) :
    closedBall x r =ᵐ[mu] ball x r := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · apply Filter.EventuallyEq.of_eq
    ext y
    simp [mem_closedBall, mem_ball, Subsingleton.elim y x, le_iff_lt_or_eq, Ne.symm hr]
  · exact mu.addHaar_closedBall_ae_eq_ball x r

/-- A null-measurable set inside a closed ball of radius `r`, with the measure of some closed ball
of radius `r`, agrees up to a null set with the ball containing it. -/
theorem _root_.MeasureTheory.Measure.ae_eq_closedBall_of_subset_of_measure_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure] {s : Set E}
    (hsm : NullMeasurableSet s mu) {c x : E} {r : ℝ} (hc : s ⊆ closedBall c r)
    (h : mu s = mu (closedBall x r)) :
    s =ᵐ[mu] closedBall c r :=
  ae_eq_of_subset_of_measure_ge hc
    (by rw [mu.addHaar_closedBall_center c, ← mu.addHaar_closedBall_center x, h]) hsm
    measure_closedBall_lt_top.ne

/-- In a nontrivial finite-dimensional space, comparing the measures of two concentric balls is
comparing their radii, as long as the first radius is nonnegative. -/
theorem _root_.MeasureTheory.Measure.addHaar_ball_lt_addHaar_ball_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {a b : ℝ} (ha : 0 ≤ a) :
    mu (ball x a) < mu (ball x b) ↔ a < b := by
  refine ⟨fun h ↦ lt_of_not_ge fun hba ↦ h.not_ge (measure_mono (ball_subset_ball hba)),
    fun hab ↦ ?_⟩
  rw [mu.addHaar_ball x ha, mu.addHaar_ball x (ha.trans hab.le)]
  exact ENNReal.mul_lt_mul_left (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2
      (pow_lt_pow_left₀ hab ha finrank_pos.ne'))

/-- Every finite nonnegative value is the measure of a centered ball in a nontrivial
finite-dimensional real normed space. -/
theorem _root_.MeasureTheory.Measure.exists_nonneg_addHaar_ball_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    {m : ENNReal} (hm : m ≠ ⊤) : ∃ r : ℝ, 0 ≤ r ∧ mu (ball (0 : E) r) = m := by
  have hω0 : mu (ball (0 : E) 1) ≠ 0 := (measure_ball_pos mu 0 one_pos).ne'
  refine ⟨(m / mu (ball (0 : E) 1)).toReal ^ (finrank ℝ E : ℝ)⁻¹, by positivity, ?_⟩
  rw [mu.addHaar_ball 0 (by positivity),
    Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg finrank_pos.ne',
    ENNReal.ofReal_toReal (ENNReal.div_ne_top hm hω0),
    ENNReal.div_mul_cancel hω0 measure_ball_lt_top.ne]

/-- In a finite-dimensional real normed space, the points whose centered norm-radius
ball has measure strictly below that of the centered radius-`r` ball form exactly that ball.
No sign condition on `r` is needed. -/
theorem _root_.MeasureTheory.Measure.setOf_addHaar_ball_norm_lt_addHaar_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (r : ℝ) :
    {x : E | mu (ball (0 : E) ‖x‖) < mu (ball 0 r)} = ball 0 r := by
  ext x
  rcases subsingleton_or_nontrivial E with hE | hE
  · obtain rfl : x = 0 := Subsingleton.elim _ _
    rcases le_or_gt r 0 with hr | hr
    · simp [Metric.ball_eq_empty.2 hr]
    · simp [measure_ball_pos mu 0 hr, hr]
  rw [Set.mem_ofPred_eq, mu.addHaar_ball_lt_addHaar_ball_iff 0 (norm_nonneg x),
    mem_ball_zero_iff]

/-- Every centered norm-radius ball has finite measure when the space is proper and the measure
is finite on compact sets; no Haar or vector-space hypothesis is needed. -/
theorem _root_.MeasureTheory.Measure.setOf_measure_ball_norm_lt_top
    {E : Type*} [SeminormedAddCommGroup E] [ProperSpace E] [MeasurableSpace E]
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] :
    {x : E | mu (ball (0 : E) ‖x‖) < ⊤} = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ measure_ball_lt_top

/-- In a nontrivial finite-dimensional space, `{x | μ (ball 0 ‖x‖) < m}` is the centered open ball
of `μ`-measure `m` when `m` is finite, and the whole space when `m = ∞`; in both cases its
measure is `m`. -/
theorem _root_.MeasureTheory.Measure.addHaar_setOf_addHaar_ball_norm_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (m : ENNReal) :
    mu {x | mu (ball (0 : E) ‖x‖) < m} = m := by
  rcases eq_or_ne m ⊤ with rfl | hm
  · rw [mu.setOf_measure_ball_norm_lt_top, measure_univ_of_isAddLeftInvariant]
  -- For finite `m`, pick the radius `r` of the centered ball of measure `m`.
  obtain ⟨r, _, hr⟩ := mu.exists_nonneg_addHaar_ball_eq hm
  rw [← hr, mu.setOf_addHaar_ball_norm_lt_addHaar_ball]

/-- A closed ball of radius `R ≤ c r` has at most `cⁿ` times the real measure of a closed ball of
radius `r > 0`, whatever their centres, where `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_closedBall_div_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x y : E) {c r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hRr : R ≤ c * r) :
    mu.real (closedBall x R) / mu.real (closedBall y r) ≤ c ^ finrank ℝ E := by
  have hball : 0 < mu.real (ball (0 : E) 1) :=
    Metric.measureReal_ball_pos mu 0 one_pos
  rw [mu.addHaar_real_closedBall x hR, mu.addHaar_real_closedBall y hr.le,
    mul_div_mul_right _ _ hball.ne', div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ hR hRr _

/-- If a set `s` has density at least `c > 0` in `closedBall y ε`, in the sense that
`c μ(closedBall y ε) ≤ μ(closedBall y ε ∩ s)`, then for `0 ≤ r ≤ 2 ε` a closed ball of radius `r`
has at most `2ⁿ / c` times the `μ.restrict s`-measure of `closedBall y ε`, whatever its centre,
where `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_restrict_closedBall_div_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x y : E) {s : Set E} {c : NNReal} {ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 0 ≤ r)
    (hrε : r ≤ 2 * ε) (hd : (c : ENNReal) * mu (closedBall y ε) ≤ mu (closedBall y ε ∩ s)) :
    (mu.restrict s).real (closedBall x r) / (mu.restrict s).real (closedBall y ε) ≤
      2 ^ finrank ℝ E / c := by
  have hy : 0 < mu.real (closedBall y ε) :=
    ENNReal.toReal_pos (measure_closedBall_pos mu y hε).ne' measure_closedBall_lt_top.ne
  have hden : c * mu.real (closedBall y ε) ≤ (mu.restrict s).real (closedBall y ε) := by
    rw [measureReal_restrict_apply measurableSet_closedBall, measureReal_def, measureReal_def,
      ← ENNReal.coe_toReal, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono
      ((measure_mono Set.inter_subset_left).trans_lt measure_closedBall_lt_top).ne hd
  have hnum : (mu.restrict s).real (closedBall x r) ≤ mu.real (closedBall x r) :=
    ENNReal.toReal_mono measure_closedBall_lt_top.ne (Measure.restrict_apply_le _ _)
  calc (mu.restrict s).real (closedBall x r) / (mu.restrict s).real (closedBall y ε)
      ≤ mu.real (closedBall x r) / (c * mu.real (closedBall y ε)) :=
        div_le_div₀ measureReal_nonneg hnum (mul_pos (NNReal.coe_pos.2 hc) hy) hden
    _ = mu.real (closedBall x r) / mu.real (closedBall y ε) / c := by rw [mul_comm, div_div]
    _ ≤ 2 ^ finrank ℝ E / c := by
        gcongr
        exact mu.addHaar_real_closedBall_div_le x y hε hr hrε

/-- If a set `s` has density at least `c` in `closedBall x r`, `r > 0`, in the sense that
`c μ(closedBall x r) ≤ μ(closedBall x r ∩ s)`, then the `μ.restrict s`-measure of the ball is at
least `c rⁿ μ(closedBall 0 1)`, where `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.ofReal_mul_rpow_mul_le_addHaar_restrict_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {s : Set E} {c : NNReal} {r : ℝ} (hr : 0 < r)
    (hd : (c : ENNReal) * mu (closedBall x r) ≤ mu (closedBall x r ∩ s)) :
    ENNReal.ofReal (c * r ^ (finrank ℝ E : ℝ) * mu.real (closedBall 0 1)) ≤
      mu.restrict s (closedBall x r) := by
  rw [Measure.restrict_apply measurableSet_closedBall]
  refine le_trans (le_of_eq ?_) hd
  rw [mu.addHaar_closedBall' x hr.le, ← Real.rpow_natCast, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, mul_assoc, measureReal_def,
    ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]

/-- The closed ball of radius `c r`, for `c ≥ 0` and `r > 0`, has `cⁿ` times the real measure of
the open ball of radius `r` with the same centre, where `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_closedBall_mul_eq_pow_mul_addHaar_real_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {c r : ℝ} (hc : 0 ≤ c) (hr : 0 < r) :
    mu.real (closedBall x (c * r)) = c ^ finrank ℝ E * mu.real (ball x r) := by
  rw [mu.addHaar_real_closedBall x (by positivity), mu.addHaar_real_ball_of_pos x hr, mul_pow]
  ring

/-- The shell between the open ball of radius `r > 0` and the concentric closed ball of radius
`s ≥ r` has real measure `(sⁿ - rⁿ)` times the real measure of the unit ball, where `n` is the
dimension. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_closedBall_sdiff_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    mu.real (closedBall x s \ ball x r) =
      (s ^ finrank ℝ E - r ^ finrank ℝ E) * mu.real (ball 0 1) := by
  rw [measureReal_sdiff (ball_subset_closedBall.trans (closedBall_subset_closedBall hrs))
    measurableSet_ball measure_closedBall_lt_top.ne, mu.addHaar_real_closedBall x (hr.le.trans hrs),
    mu.addHaar_real_ball_of_pos x hr, sub_mul]

/-- The part of the ball `ball y s` outside the ball `ball z s` of the same radius `s > 0` has
measure at most `((s + dist y z)ⁿ - sⁿ)` times the measure of the unit ball, the measure of the
shell between the spheres of radii `s` and `s + dist y z` about `z`. Here `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_ball_sdiff_ball_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (y z : E) {s : ℝ} (hs : 0 < s) :
    mu.real (ball y s \ ball z s) ≤
      ((s + dist y z) ^ finrank ℝ E - s ^ finrank ℝ E) * mu.real (ball 0 1) := by
  have hsub : ball y s \ ball z s ⊆ ball z (s + dist y z) \ ball z s := by
    refine Set.sdiff_subset_sdiff_left fun x hx ↦ ?_
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle x y z]
  have hss : ball z s ⊆ ball z (s + dist y z) :=
    ball_subset_ball (by linarith [dist_nonneg (x := y) (y := z)])
  calc mu.real (ball y s \ ball z s) ≤ mu.real (ball z (s + dist y z) \ ball z s) :=
        measureReal_mono hsub (measure_ne_top_of_subset Set.sdiff_subset measure_ball_lt_top.ne)
    _ = _ := by
        rw [measureReal_sdiff hss measurableSet_ball measure_ball_lt_top.ne,
          mu.addHaar_real_ball_of_pos z (by positivity), mu.addHaar_real_ball_of_pos z hs]
        ring

open scoped Pointwise in
/-- The measure of `y + r • S`, relative to that of a closed ball of radius `r > 0`, is the measure
of `S` relative to that of the closed unit ball. -/
theorem _root_.MeasureTheory.Measure.addHaar_image_add_smul_div_addHaar_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x y : E) {r : ℝ} (hr : 0 < r) (S : Set E) :
    mu ((fun w => y + r • w) '' S) / mu (closedBall x r) = mu S / mu (closedBall 0 1) := by
  have himage : (fun w => y + r • w) '' S = y +ᵥ r • S := by
    rw [← Set.image_smul, ← Set.image_vadd, Set.image_image]
    rfl
  rw [himage, measure_vadd, addHaar_smul, addHaar_closedBall' mu x hr.le,
    abs_of_pos (pow_pos hr _)]
  exact ENNReal.mul_div_mul_left _ _ (by simpa using pow_pos hr _) ENNReal.ofReal_ne_top

/-- A homothety of nonzero ratio `r` pushes an additive Haar measure to its multiple by
`|r ^ n|⁻¹`, where `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.map_addHaar_homothety
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : r ≠ 0) :
    mu.map (AffineMap.homothety x r) = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| • mu := by
  have hfun : ⇑(AffineMap.homothety x r) = (x - r • x + ·) ∘ (r • ·) := by
    ext y
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, Function.comp_apply, smul_sub]
    abel
  rw [hfun, ← Measure.map_map (measurable_const_add _) (measurable_const_smul _),
    map_addHaar_smul mu hr, Measure.map_smul _ (measurable_const_add _).aemeasurable,
    map_add_left_eq_self]

/-- **Image of an additive Haar measure under an invertible affine map.** The image of `μ` under
`x ↦ c + A x` is `μ` scaled by the reciprocal absolute determinant `|det A|⁻¹`. -/
theorem _root_.MeasureTheory.Measure.map_affine_addHaar_eq_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E ≃L[ℝ] E) (c : E) :
    μ.map (fun x => c + A x) =
      ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| • μ := by
  have hdet : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := ((A : E ≃ₗ[ℝ] E).isUnit_det').ne_zero
  have hmapA : μ.map A = ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  calc
    μ.map (fun x ↦ c + A x) = (μ.map A).map (fun y : E ↦ c + y) :=
      (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = (ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| • μ).map (fun y : E ↦ c + y) := by
      rw [hmapA]
    _ = ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| • μ := by
      rw [Measure.map_smul _ ((by fun_prop : Measurable fun y : E ↦ c + y).aemeasurable),
        map_add_left_eq_self]

/-- **The determinant is bounded by the operator norm**: `|det f| ≤ ‖f‖ ^ n` for a linear
endomorphism `f` of a real normed space of finite dimension `n`. The image of the closed unit ball
under `f` lies in the closed ball of radius `‖f‖`, and its measure is `|det f|` times that of the
closed unit ball. -/
theorem _root_.ContinuousLinearMap.abs_det_le_opNorm_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →L[ℝ] E) : |f.det| ≤ ‖f‖ ^ finrank ℝ E := by
  borelize E
  set mu : Measure E := addHaar
  have hsub : (f : E →ₗ[ℝ] E) '' closedBall 0 1 ⊆ closedBall 0 ‖f‖ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ ‖f‖ * 1 := by gcongr
      _ = ‖f‖ := mul_one _
  have h := measure_mono (μ := mu) hsub
  rw [mu.addHaar_image_linearMap, mu.addHaar_closedBall 0 (norm_nonneg f),
    mu.addHaar_closedBall 0 zero_le_one, one_pow, ENNReal.ofReal_one, one_mul] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 <|
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne).1 h

/-- **The determinant is bounded by the operator norm** over an `RCLike` field: `‖det f‖ ≤ ‖f‖ ^ n`
for a linear endomorphism `f` of a normed space of finite dimension `n`. -/
theorem _root_.ContinuousLinearMap.norm_det_le_opNorm_pow {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (f : E →L[𝕜] E) :
    ‖f.det‖ ≤ ‖f‖ ^ finrank 𝕜 E := by
  -- Restricting scalars to `ℝ` turns the determinant into its field norm, whose absolute value is
  -- `‖det f‖ ^ finrank ℝ 𝕜` and is bounded by `abs_det_le_opNorm_pow`.
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := ⟨fun r c x ↦ by simp [Algebra.smul_def, mul_smul]⟩
  have : FiniteDimensional ℝ E := Module.Finite.trans 𝕜 E
  have h := (f.restrictScalars ℝ).abs_det_le_opNorm_pow
  have hdet : (f.restrictScalars ℝ).det = Algebra.norm ℝ f.det := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
      LinearMap.det_restrictScalars]
  rw [hdet, RCLike.abs_algebraNorm_eq_norm_pow, ContinuousLinearMap.norm_restrictScalars,
    ← finrank_mul_finrank ℝ 𝕜 E, pow_mul'] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) finrank_pos.ne').1 h

end TauCeti

end
