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

In a finite-dimensional real normed space, the real measure of a positive-radius ball is its
radius raised to the dimension times the real measure of the unit ball, independently of its
centre. It agrees with the measure of the closed ball, which therefore differs from the open ball
by a null set. Consequently the ratio of the measures of two closed balls is controlled by the
ratio of their radii raised to the dimension, and the part of a ball outside a translate of
itself is controlled by the distance between the centres. The measure of an affine image
`y + r • S` relative to a ball of radius `r` is that of `S` relative to the unit ball.

## Main results

* `MeasureTheory.Measure.addHaar_real_ball_of_pos`: the real measure of a positive-radius ball.
* `MeasureTheory.Measure.addHaar_closedBall_ae_eq_ball`: closed and open balls agree up to a null
  set in a nontrivial space.
* `MeasureTheory.Measure.addHaar_closedBall_ae_eq_ball_of_ne_zero`: the same agreement at nonzero
  radius, including trivial spaces.
* `MeasureTheory.Measure.addHaar_real_closedBall_div_le`: a closed ball of radius `R ≤ c r` has
  at most `cⁿ` times the measure of a closed ball of radius `r`.
* `MeasureTheory.Measure.addHaar_real_ball_sdiff_ball_le`: the part of a ball outside a ball of the
  same radius `s` whose centre is at distance `d` is no larger than a spherical shell of radii `s`
  and `s + d`.
* `MeasureTheory.Measure.addHaar_image_add_smul_div_addHaar_closedBall`: the measure of
  `y + r • S` relative to a closed ball of radius `r > 0` is the measure of `S` relative to the
  unit ball.
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

end TauCeti

end
