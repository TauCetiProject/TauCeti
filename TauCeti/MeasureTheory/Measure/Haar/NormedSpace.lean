/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real

/-!
# Additive Haar measures on real normed spaces

In a finite-dimensional real normed space, the real measure of a positive-radius ball is its radius
raised to the dimension times the real measure of the unit ball, independently of its centre;
equivalently, `n / r` times the measure of the ball of radius `r` is `n rⁿ⁻¹` times the measure of
the unit ball, where `n` is the dimension. It agrees with the measure of the closed ball, which
therefore differs from the open ball by a null set. A set inside a closed ball with the measure of a
ball of the same radius likewise agrees with it up to a null set. In a nontrivial space, concentric
balls are ordered by measure as by radius, so the points `x` whose centered ball of radius `‖x‖` has
measure below `m` form a set of measure `m`. The ratio of the measures of two closed balls is
controlled by the ratio of their radii raised to the dimension, the shell between concentric balls
has measure the difference of the powers of the radii, and the part of a ball outside a translate of
itself is controlled by the distance between the centres. The measure of an affine image
`y + r • S` relative to a ball of radius `r` is that of `S` relative to the unit ball, and a
homothety of ratio `r ≠ 0` pushes the measure forward to its multiple by `|r|⁻ⁿ`. Comparing the
measure of the image of the closed unit ball under a linear endomorphism `f` with that of the
closed ball of radius `‖f‖` bounds `|det f|` by `‖f‖` raised to the dimension.

## Main results

* `MeasureTheory.Measure.addHaar_real_ball_of_pos`: the real measure of a positive-radius ball.
* `MeasureTheory.Measure.finrank_div_mul_addHaar_real_ball`:
  `(n / r) μ (ball x r) = n rⁿ⁻¹ μ (ball 0 1)` in dimension `n`.
* `MeasureTheory.Measure.addHaar_real_ball_mul_diam_ball_pow_div_le`:
  `μ (ball 0 1) (diam (ball x r))ⁿ⁺¹ / μ (ball x r) ≤ 2ⁿ⁺¹ r` in dimension `n`.
* `MeasureTheory.Measure.addHaar_closedBall_ae_eq_ball`: closed and open balls agree up to a null
  set in a nontrivial space.
* `MeasureTheory.Measure.addHaar_closedBall_ae_eq_ball_of_ne_zero`: the same agreement at nonzero
  radius, including trivial spaces.
* `MeasureTheory.Measure.ae_eq_closedBall_of_subset_of_measure_eq`: a set inside a closed ball,
  with the measure of a closed ball of the same radius, agrees with it up to a null set.
* `MeasureTheory.Measure.addHaar_ball_lt_addHaar_ball_iff`: concentric balls are ordered by
  measure as by radius.
* `MeasureTheory.Measure.addHaar_setOf_addHaar_ball_norm_lt`: in a nontrivial space, the set where
  the centered ball has measure below `m` has measure `m`.
* `MeasureTheory.Measure.addHaar_real_closedBall_div_le`: a closed ball of radius `R ≤ c r` has
  at most `cⁿ` times the measure of a closed ball of radius `r`.
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
* `ContinuousLinearMap.abs_det_le_opNorm_pow`: `|det f| ≤ ‖f‖ ^ n` in dimension `n`.
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

/-- For a ball of radius `r > 0` in dimension `n`, `n / r` times its real measure is
`n rⁿ⁻¹` times the real measure of the unit ball, the derivative in `r` of its measure. -/
theorem _root_.MeasureTheory.Measure.finrank_div_mul_addHaar_real_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    finrank ℝ E / r * mu.real (ball x r) =
      finrank ℝ E * r ^ (finrank ℝ E - 1) * mu.real (ball 0 1) := by
  rw [mu.addHaar_real_ball_of_pos x hr]
  cases finrank ℝ E with
  | zero => simp
  | succ k =>
    simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    field_simp
    ring

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
    ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
  rw [mu.addHaar_real_ball_of_pos x hr, div_le_iff₀ (by positivity)]
  calc mu.real (ball (0 : E) 1) * diam (ball x r) ^ (finrank ℝ E + 1)
      ≤ mu.real (ball (0 : E) 1) * (2 * r) ^ (finrank ℝ E + 1) := by
        gcongr
        exact diam_ball hr.le
    _ = 2 ^ (finrank ℝ E + 1) * r * (r ^ finrank ℝ E * mu.real (ball (0 : E) 1)) := by ring

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

/-- In a nontrivial finite-dimensional space, `{x | μ (ball 0 ‖x‖) < m}` is the centered open ball
of `μ`-measure `m` when `m` is finite, and the whole space when `m = ∞`; in both cases its
measure is `m`. -/
theorem _root_.MeasureTheory.Measure.addHaar_setOf_addHaar_ball_norm_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (m : ENNReal) :
    mu {x | mu (ball (0 : E) ‖x‖) < m} = m := by
  rcases eq_or_ne m ⊤ with rfl | hm
  · have huniv : {x : E | mu (ball (0 : E) ‖x‖) < ⊤} = Set.univ :=
      Set.eq_univ_of_forall fun _ ↦ measure_ball_lt_top
    rw [huniv, measure_univ_of_isAddLeftInvariant]
  -- For finite `m`, pick the radius `r` of the centered ball of measure `m`.
  have hω0 : mu (ball (0 : E) 1) ≠ 0 := (measure_ball_pos mu 0 one_pos).ne'
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ mu (ball (0 : E) r) = m := by
    refine ⟨(m / mu (ball (0 : E) 1)).toReal ^ (finrank ℝ E : ℝ)⁻¹, by positivity, ?_⟩
    rw [mu.addHaar_ball 0 (by positivity),
      Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg finrank_pos.ne',
      ENNReal.ofReal_toReal (ENNReal.div_ne_top hm hω0),
      ENNReal.div_mul_cancel hω0 measure_ball_lt_top.ne]
  have hset : {x : E | mu (ball (0 : E) ‖x‖) < m} = ball 0 r := by
    ext x
    rw [← hr, Set.mem_ofPred_eq, mu.addHaar_ball_lt_addHaar_ball_iff 0 (norm_nonneg x),
      mem_ball_zero_iff]
  rw [hset, hr]

/-- A closed ball of radius `R ≤ c r` has at most `cⁿ` times the real measure of a closed ball of
radius `r > 0`, whatever their centres, where `n` is the dimension. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_closedBall_div_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x y : E) {c r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hRr : R ≤ c * r) :
    mu.real (closedBall x R) / mu.real (closedBall y r) ≤ c ^ finrank ℝ E := by
  have hball : 0 < mu.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
  rw [mu.addHaar_real_closedBall x hR, mu.addHaar_real_closedBall y hr.le,
    mul_div_mul_right _ _ hball.ne', div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ hR hRr _

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

end TauCeti

end
