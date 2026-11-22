/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import TauCeti.MeasureTheory.Measure.Comap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Integrals against normalized bumps

Let `f` be a smooth bump centred at `c` in a finite-dimensional real normed space. Its normalized
form `f.normed μ` is continuous with compact support, so it makes every continuous function
integrable. Since it vanishes off the closed ball of radius `f.rOut` around `c`, an integral against
it may be taken over that compact ball, with the pullback of `μ`, which is a finite measure. There
`f.normed μ` still has integral one and averages constants to themselves.

## Main declarations

* `ContDiffBump.integrable_normed_smul`: bump-weighted continuous functions are integrable.
* `ContDiffBump.integral_closedBall_normed_smul`: bump-weighted integrals over the closed ball of
  radius `f.rOut` are integrals over the whole space.
* `ContDiffBump.integral_closedBall_normed_smul_const`: over that closed ball, the normalized bump
  averages a constant to itself.
* `ContDiffBump.normed_le_div_measureReal_ball`: pointwise upper bound on a normalized bump in
  terms of the open-ball measure.
-/

public section

open MeasureTheory Metric

namespace ContDiffBump

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {c : E} (f : ContDiffBump c) (μ : Measure E) [IsLocallyFiniteMeasure μ]
  [μ.IsOpenPosMeasure]

/-- Bump-weighted continuous functions are integrable. -/
theorem integrable_normed_smul {g : E → G} (hg : Continuous g) :
    Integrable (fun x ↦ f.normed μ x • g x) μ :=
  (f.continuous_normed.smul hg).integrable_of_hasCompactSupport
    f.hasCompactSupport_normed.smul_right

/-- An integral against a normalized bump over the closed ball of radius `f.rOut`, with the
pullback of `μ`, is the integral over the whole space. -/
theorem integral_closedBall_normed_smul (g : E → G) :
    ∫ x : closedBall c f.rOut, f.normed μ x • g x ∂(μ.comap (↑)) =
      ∫ x, f.normed μ x • g x ∂μ := by
  rw [integral_subtype_comap measurableSet_closedBall (fun x ↦ f.normed μ x • g x)]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport (f := f.normed μ) (by rwa [f.tsupport_normed_eq]),
      zero_smul]

/-- A normalized bump has integral one over the closed ball of radius `f.rOut`. -/
theorem integral_closedBall_normed :
    ∫ x : closedBall c f.rOut, f.normed μ x ∂(μ.comap (↑)) = 1 := by
  have h := f.integral_closedBall_normed_smul μ (fun _ ↦ (1 : ℝ))
  simp only [smul_eq_mul, mul_one] at h
  rw [h, f.integral_normed]

omit [μ.IsOpenPosMeasure] in
/-- Bump-weighted constants are integrable over the closed ball of radius `f.rOut`. -/
theorem integrable_closedBall_normed_smul_const (z : G) :
    Integrable (fun x : closedBall c f.rOut ↦ f.normed μ x • z) (μ.comap (↑)) :=
  ((f.continuous_normed.comp continuous_subtypeVal).smul continuous_const)
    |>.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- Over the closed ball of radius `f.rOut`, a normalized bump averages a constant to itself. -/
theorem integral_closedBall_normed_smul_const [CompleteSpace G] (z : G) :
    ∫ x : closedBall c f.rOut, f.normed μ x • z ∂(μ.comap (↑)) = z := by
  rw [integral_smul_const, f.integral_closedBall_normed, one_smul]

section AddHaar

omit [HasContDiffBump E] [NormedAddCommGroup G] [NormedSpace ℝ G] [IsLocallyFiniteMeasure μ]
  [μ.IsOpenPosMeasure]

/-- Pointwise upper bound on a normalized bump in terms of the open-ball measure. -/
theorem normed_le_div_measureReal_ball [HasContDiffBump E] [μ.IsAddHaarMeasure]
    (K : ℝ) (h : f.rOut ≤ K * f.rIn) (x : E) :
    f.normed μ x ≤ K ^ Module.finrank ℝ E / μ.real (ball c f.rOut) := by
  rw [← measureReal_congr (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero c _ f.rOut_pos.ne')]
  exact f.normed_le_div_measure_closedBall_rOut μ K h x

end AddHaar

end ContDiffBump
