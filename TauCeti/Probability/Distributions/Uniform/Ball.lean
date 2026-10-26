/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Uniform
public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.Uniform.Sphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Integral.OddSymmetric
import TauCeti.Probability.ConditionalProbability
import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Probability.Moments.Covariance

/-!
# The uniform law on a ball

On a finite-dimensional real inner product space `E` of dimension `d`, the uniform law
`uniformBallMeasure c r` on the open ball of center `c` and radius `r > 0` is Lebesgue measure
conditioned on the ball, `ProbabilityTheory.cond volume (ball c r)`. This is the same `cond` that
defines Mathlib's `MeasureTheory.pdf.IsUniform`, so a random vector with this law is uniform on
the ball in Mathlib's sense and Mathlib's `MeasureTheory.pdf.uniformPDF` is its density. In
positive dimension the volume of the ball is `r ^ d * √π ^ d / Γ (d / 2 + 1)`, which is Mathlib's
`InnerProductSpace.volume_ball`. Radius zero gives the point mass at `c`, and a negative radius
gives the zero measure.

The law is carried to a uniform law on a ball by translations, nonzero dilations and linear
isometries. For `r ≥ 0` its mean is the center. For `r > 0` and `d ≥ 1` the normalized radius
`‖X - c‖ / r` has the beta law with parameters `d` and `1`, whose cumulative distribution function
is `t ^ d` on `[0, 1]` (`TauCeti.Probability.cdf_betaMeasure_one_right`) and whose quantile is
`u ^ d⁻¹` (`TauCeti.Probability.quantile_betaMeasure_one_right`); under the same hypotheses the
direction `(X - c) / ‖X - c‖` is uniform on the unit sphere and independent of the radius. For
`r ≥ 0`, combining invariance under isometries with the second moment
`E ‖X - c‖ ^ 2 = d r ^ 2 / (d + 2)` of the radius shows that the covariance is `r ^ 2 / (d + 2)`
times the inner product.

## Main definitions

* `TauCeti.Probability.uniformBallMeasure`: the uniform law on a ball.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_uniformBallMeasure_iff`: it is a probability
  measure exactly for nonnegative radius.
* `TauCeti.Probability.uniformBallMeasure_eq_withDensity`,
  `TauCeti.Probability.rnDeriv_uniformBallMeasure`: for nonzero radius, its density against
  Lebesgue measure.
* `TauCeti.Probability.map_const_add_uniformBallMeasure`,
  `TauCeti.Probability.map_const_smul_uniformBallMeasure`,
  `LinearIsometryEquiv.map_uniformBallMeasure`: transport by translations, dilations and
  isometries.
* `TauCeti.Probability.integral_id_uniformBallMeasure`: for `r ≥ 0` the mean is the center.
* `TauCeti.Probability.map_norm_sub_div_uniformBallMeasure`: for `r > 0` and `d ≥ 1` the
  normalized radius has the beta law with parameters `d` and `1`.
* `TauCeti.Probability.map_sphereDirection_prod_uniformBallMeasure`: for `r > 0` and `d ≥ 1`
  direction and normalized radius are independent, uniform on the sphere and beta distributed.
* `TauCeti.Probability.covarianceBilin_uniformBallMeasure`: for `r ≥ 0` the covariance is
  `r ^ 2 / (d + 2)` times the inner product.

## References

* K.-T. Fang, S. Kotz, K. W. Ng, *Symmetric Multivariate and Related Distributions*, Chapman and
  Hall, 1990, chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Module
open scoped ENNReal

namespace TauCeti.Probability

section Definition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {c : E} {r : ℝ}

/-- The uniform law on the open ball of center `c` and radius `r`: Lebesgue measure conditioned
on the ball. Radius zero gives the point mass at `c`, and a negative radius gives the zero
measure. -/
def uniformBallMeasure (c : E) (r : ℝ) : Measure E :=
  if r = 0 then Measure.dirac c else volume[|ball c r]

/-- The uniform law on a ball, by cases on whether the radius vanishes. -/
theorem uniformBallMeasure_def (c : E) (r : ℝ) :
    uniformBallMeasure c r = if r = 0 then Measure.dirac c else volume[|ball c r] := by
  rw [uniformBallMeasure]

/-- For nonzero radius the uniform law on a ball is Lebesgue measure conditioned on the ball. -/
theorem uniformBallMeasure_of_ne_zero (hr : r ≠ 0) :
    uniformBallMeasure c r = volume[|ball c r] := by
  simp [uniformBallMeasure, hr]

/-- The uniform law on a ball of radius zero is the point mass at the center. -/
@[simp]
theorem uniformBallMeasure_zero_right (c : E) : uniformBallMeasure c 0 = Measure.dirac c := by
  simp [uniformBallMeasure]

/-- The uniform law on a ball of negative radius is the zero measure. -/
theorem uniformBallMeasure_of_neg (hr : r < 0) : uniformBallMeasure c r = 0 := by
  rw [uniformBallMeasure_of_ne_zero hr.ne, ball_eq_empty.2 hr.le, cond_empty]

/-- For nonzero radius the uniform law on a ball gives a set the proportion of the volume of the
ball that it occupies. -/
theorem uniformBallMeasure_apply (hr : r ≠ 0) (s : Set E) :
    uniformBallMeasure c r s = volume (ball c r ∩ s) / volume (ball c r) := by
  rw [uniformBallMeasure_of_ne_zero hr, cond_apply measurableSet_ball, ENNReal.div_eq_inv_mul]

instance isFiniteMeasure_uniformBallMeasure : IsFiniteMeasure (uniformBallMeasure c r) := by
  unfold uniformBallMeasure
  split_ifs <;> infer_instance

/-- For nonnegative radius the uniform law on a ball is a probability measure. -/
theorem isProbabilityMeasure_uniformBallMeasure (hr : 0 ≤ r) :
    IsProbabilityMeasure (uniformBallMeasure c r) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [uniformBallMeasure_zero_right]
    infer_instance
  · rw [uniformBallMeasure_of_ne_zero hr.ne']
    exact cond_isProbabilityMeasure_of_finite (measure_ball_pos volume c hr).ne'
      measure_ball_lt_top.ne

/-- The uniform law on a ball is a probability measure exactly when the radius is
nonnegative. -/
@[simp]
theorem isProbabilityMeasure_uniformBallMeasure_iff :
    IsProbabilityMeasure (uniformBallMeasure c r) ↔ 0 ≤ r := by
  refine ⟨fun h ↦ not_lt.1 fun hr ↦ ?_, isProbabilityMeasure_uniformBallMeasure⟩
  rw [uniformBallMeasure_of_neg hr] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure E) rfl

/-- For positive radius a point drawn from the uniform law on a ball lies in the open ball almost
surely. -/
theorem ae_mem_ball_uniformBallMeasure (hr : 0 < r) :
    ∀ᵐ x ∂uniformBallMeasure c r, x ∈ ball c r := by
  rw [uniformBallMeasure_of_ne_zero hr.ne']
  exact ae_cond_mem measurableSet_ball

/-- A point drawn from the uniform law on a ball lies in the closed ball almost surely, for every
radius. -/
theorem ae_mem_closedBall_uniformBallMeasure (c : E) (r : ℝ) :
    ∀ᵐ x ∂uniformBallMeasure c r, x ∈ closedBall c r := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · simp [uniformBallMeasure_of_neg hr]
  · simp
  · exact (ae_mem_ball_uniformBallMeasure hr).mono fun x hx ↦ ball_subset_closedBall hx

/-- The uniform law on a ball has finite moments of every order. -/
theorem memLp_id_uniformBallMeasure (c : E) (r : ℝ) (p : ℝ≥0∞) :
    MemLp id p (uniformBallMeasure c r) :=
  .of_bound aestronglyMeasurable_id (‖c‖ + r)
    ((ae_mem_closedBall_uniformBallMeasure c r).mono fun _ hx ↦ norm_le_of_mem_closedBall hx)

end Definition

section Density

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {c : E} {r : ℝ}

/-- For nonzero radius the uniform law on a ball is Lebesgue measure weighted by Mathlib's uniform
density on the ball. -/
theorem uniformBallMeasure_eq_withDensity (hr : r ≠ 0) :
    uniformBallMeasure c r = volume.withDensity fun x ↦ pdf.uniformPDF (ball c r) x volume := by
  unfold pdf.uniformPDF
  rw [withDensity_indicator measurableSet_ball]
  simp only [Pi.smul_def, smul_eq_mul, Pi.one_apply, mul_one]
  rw [withDensity_const, uniformBallMeasure_of_ne_zero hr, ProbabilityTheory.cond]

/-- For nonzero radius the Radon–Nikodym derivative of the uniform law on a ball against Lebesgue
measure is Mathlib's uniform density on the ball. -/
theorem rnDeriv_uniformBallMeasure (hr : r ≠ 0) :
    (uniformBallMeasure c r).rnDeriv volume
      =ᵐ[volume] fun x ↦ pdf.uniformPDF (ball c r) x volume := by
  rw [uniformBallMeasure_eq_withDensity hr]
  exact Measure.rnDeriv_withDensity volume (measurable_uniformPDF measurableSet_ball volume)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → E}

/-- For nonzero radius a random vector with the uniform law on a ball is uniform on the ball in
the sense of Mathlib's `MeasureTheory.pdf.IsUniform`. -/
theorem isUniform_of_hasLaw_uniformBallMeasure (hr : r ≠ 0)
    (hX : HasLaw X (uniformBallMeasure c r) P) : pdf.IsUniform X (ball c r) P volume := by
  rwa [uniformBallMeasure_of_ne_zero hr] at hX

/-- For nonzero radius a random vector with the uniform law on a ball has a density. -/
theorem hasPDF_of_hasLaw_uniformBallMeasure (hr : r ≠ 0)
    (hX : HasLaw X (uniformBallMeasure c r) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_uniformPDF measurableSet_ball volume).aemeasurable
    (by rwa [uniformBallMeasure_eq_withDensity hr] at hX)

end Density

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Translating the uniform law on a ball translates the center. -/
theorem map_const_add_uniformBallMeasure (a c : E) (r : ℝ) :
    (uniformBallMeasure c r).map (a + ·) = uniformBallMeasure (a + c) r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [Measure.map_dirac' (measurable_const_add a)]
  have hpre : (a + ·) ⁻¹' ball (a + c) r = ball c r := by
    ext x
    simp [dist_eq_norm]
  rw [uniformBallMeasure_of_ne_zero hr, uniformBallMeasure_of_ne_zero hr, ← hpre]
  exact map_cond_preimage (measurable_const_add a) one_ne_zero ENNReal.one_ne_top
    (fun A _ ↦ by rw [one_mul, measure_preimage_add]) measurableSet_ball

/-- The uniform law on a ball is the translate by the center of the uniform law on the ball of
the same radius centered at the origin. -/
theorem uniformBallMeasure_eq_map_const_add (c : E) (r : ℝ) :
    uniformBallMeasure c r = (uniformBallMeasure (0 : E) r).map (c + ·) := by
  simpa using (map_const_add_uniformBallMeasure c 0 r).symm

/-- A nonzero dilation carries the uniform law on a ball to the uniform law on the dilated
ball. -/
theorem map_const_smul_uniformBallMeasure {s : ℝ} (hs : s ≠ 0) (c : E) (r : ℝ) :
    (uniformBallMeasure c r).map (s • ·) = uniformBallMeasure (s • c) (|s| * r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [Measure.map_dirac' (measurable_const_smul s)]
  have hpre : (s • ·) ⁻¹' ball (s • c) (|s| * r) = ball c r := by
    ext x
    simp [dist_eq_norm, ← smul_sub, norm_smul, abs_pos.2 hs]
  rw [uniformBallMeasure_of_ne_zero hr,
    uniformBallMeasure_of_ne_zero (mul_ne_zero (abs_ne_zero.2 hs) hr), ← hpre]
  refine map_cond_preimage (measurable_const_smul s) ?_ ENNReal.ofReal_ne_top
    (fun A _ ↦ Measure.addHaar_preimage_smul volume hs A) measurableSet_ball
  exact (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (pow_ne_zero _ hs)))).ne'

end Transport

end TauCeti.Probability

namespace LinearIsometryEquiv

open TauCeti.Probability

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Isometry invariance of the uniform ball law.** A linear isometric equivalence carries the
uniform law on a ball to the uniform law on the image ball. -/
theorem map_uniformBallMeasure (f : E ≃ₗᵢ[ℝ] F) (c : E) (r : ℝ) :
    (uniformBallMeasure c r).map f = uniformBallMeasure (f c) r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [Measure.map_dirac' f.continuous.measurable]
  have hpre : f ⁻¹' ball (f c) r = ball c r := by
    rw [f.preimage_ball, f.symm_apply_apply]
  rw [uniformBallMeasure_of_ne_zero hr, uniformBallMeasure_of_ne_zero hr, ← hpre]
  exact map_cond_preimage f.continuous.measurable one_ne_zero ENNReal.one_ne_top
    (fun A hA ↦ by rw [one_mul, f.measurePreserving.measure_preimage hA.nullMeasurableSet])
    measurableSet_ball

end LinearIsometryEquiv

namespace TauCeti.Probability

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {r : ℝ}

/-- The uniform law on a ball centered at the origin is invariant under negation. -/
instance isNegInvariant_uniformBallMeasure (r : ℝ) :
    (uniformBallMeasure (0 : E) r).IsNegInvariant :=
  ⟨by simpa [Measure.neg_def] using (LinearIsometryEquiv.neg ℝ (E := E)).map_uniformBallMeasure 0 r⟩

/-- **The mean of the uniform ball law is the center.** -/
theorem integral_id_uniformBallMeasure (c : E) (hr : 0 ≤ r) :
    ∫ x, x ∂uniformBallMeasure c r = c := by
  have := isProbabilityMeasure_uniformBallMeasure (c := (0 : E)) hr
  rw [uniformBallMeasure_eq_map_const_add c, integral_map (by fun_prop) (by fun_prop),
    integral_add (g := fun x ↦ x) (integrable_const c)
      ((memLp_id_uniformBallMeasure 0 r 1).integrable le_rfl),
    integral_eq_zero_of_odd (g := fun x : E ↦ x) fun _ ↦ rfl, integral_const, probReal_univ,
    one_smul, add_zero]

end Moments

section Radius

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {r : ℝ}

/-- **The normalized radius of a uniform point of a ball is beta distributed.** For a point `X`
drawn uniformly from a ball of center `c` and radius `r > 0` in positive dimension `d`, the
normalized radius `‖X - c‖ / r` has the beta law with parameters `d` and `1`: its cumulative
distribution function is `t ^ d` on `[0, 1]`, the proportion of the volume of the ball filled by
the concentric ball of radius `t r`. -/
theorem map_norm_sub_div_uniformBallMeasure [Nontrivial E] (c : E) (hr : 0 < r) :
    (uniformBallMeasure c r).map (fun x ↦ ‖x - c‖ / r) = betaMeasure (finrank ℝ E) 1 := by
  set d := finrank ℝ E
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 finrank_pos
  have := isProbabilityMeasure_uniformBallMeasure (c := c) hr.le
  have := isProbabilityMeasureBeta hd one_pos
  refine Measure.ext_of_Iic _ _ fun t ↦ ?_
  have hpre : (fun x : E ↦ ‖x - c‖ / r) ⁻¹' Iic t = closedBall c (t * r) := by
    ext x
    simp [dist_eq_norm, div_le_iff₀ hr]
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic, hpre, uniformBallMeasure_apply hr.ne',
    ← ofReal_cdf]
  have hV₀ : volume (ball c r) ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hV : volume (ball c r) ≠ ∞ := measure_ball_lt_top.ne
  rcases lt_or_ge t 0 with ht | ht
  · rw [closedBall_eq_empty.2 (mul_neg_of_neg_of_pos ht hr), inter_empty, measure_empty,
      ENNReal.zero_div, cdf_betaMeasure_eq hd one_pos,
      regularizedIncompleteBeta_eq_zero_of_nonpos hd.ne' 1 ht.le, ENNReal.ofReal_zero]
  rcases lt_or_ge t 1 with ht₁ | ht₁
  · -- The concentric closed ball of radius `t r` fills the proportion `t ^ d` of the ball.
    rw [inter_eq_right.2 (closedBall_subset_ball (mul_lt_of_lt_one_left hr ht₁)),
      Measure.addHaar_closedBall_mul volume c ht hr.le, cdf_betaMeasure_one_right hd ⟨ht, ht₁.le⟩,
      Real.rpow_natCast, Measure.addHaar_closedBall_eq_addHaar_ball,
      ← Measure.addHaar_ball_center volume c, ENNReal.mul_div_cancel_right hV₀ hV]
  · rw [inter_eq_left.2 (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (le_mul_of_one_le_left hr.le ht₁))),
      ENNReal.div_self hV₀ hV, cdf_betaMeasure_eq hd one_pos,
      regularizedIncompleteBeta_eq_one_of_one_le hd.le one_pos ht₁, ENNReal.ofReal_one]

/-- **Direction and radius of a uniform point of a ball.** For a point `X` drawn uniformly from a
ball of center `c` and radius `r > 0`, the direction `(X - c) / ‖X - c‖` and the normalized radius
`‖X - c‖ / r` are independent; the direction is uniform on the unit sphere and the normalized
radius has the beta law with parameters `d` and `1`. The center itself is a null set, so the
direction `e` assigned to it is irrelevant. -/
theorem map_sphereDirection_prod_uniformBallMeasure (e : sphere (0 : E) 1) (c : E)
    (hr : 0 < r) :
    (uniformBallMeasure c r).map (fun x ↦ (sphereDirection e (x - c), ‖x - c‖ / r)) =
      (uniformSphereMeasure E).prod (betaMeasure (finrank ℝ E) 1) := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  have hdir : Measurable (sphereDirection e) := measurable_sphereDirection e
  rw [uniformBallMeasure_eq_map_const_add c, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, add_sub_cancel_left]
  -- The centered uniform law has a radial density.
  set φ : ℝ → ℝ≥0∞ := (Iio r).indicator fun _ ↦ (volume (ball (0 : E) r))⁻¹
  have hφ : Measurable φ := measurable_const.indicator measurableSet_Iio
  have h₀ : uniformBallMeasure (0 : E) r = volume.withDensity fun x ↦ φ ‖x‖ := by
    rw [uniformBallMeasure_eq_withDensity hr.ne']
    congr 1
    funext x
    by_cases hx : ‖x‖ < r <;> simp [pdf.uniformPDF, φ, indicator, hx]
  have : IsFiniteMeasure ((volume : Measure E).withDensity fun x ↦ φ ‖x‖) := h₀ ▸ inferInstance
  have hjoint := map_sphereDirection_prod_norm_withDensity e hφ
  rw [← h₀] at hjoint
  have hrad := map_norm_sub_div_uniformBallMeasure (0 : E) hr
  simp only [sub_zero] at hrad
  have hcomp : (fun x : E ↦ (sphereDirection e x, ‖x‖ / r)) =
      Prod.map id (· / r) ∘ fun x ↦ (sphereDirection e x, ‖x‖) := by
    funext x
    simp
  have hdiv : Measurable fun t : ℝ ↦ t / r := by fun_prop
  rw [hcomp, ← Measure.map_map (measurable_id.prodMap hdiv) (hdir.prodMk measurable_norm), hjoint,
    ← Measure.map_prod_map _ _ measurable_id hdiv, Measure.map_id,
    Measure.map_map hdiv measurable_norm]
  exact congrArg _ hrad

/-- The direction `(X - c) / ‖X - c‖` of a point drawn uniformly from a ball of positive radius is
uniform on the unit sphere. -/
theorem map_sphereDirection_uniformBallMeasure (e : sphere (0 : E) 1) (c : E) (hr : 0 < r) :
    (uniformBallMeasure c r).map (fun x ↦ sphereDirection e (x - c)) = uniformSphereMeasure E := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  have := isProbabilityMeasureBeta (Nat.cast_pos.2 (finrank_pos (R := ℝ) (M := E))) one_pos
  have h := congrArg (Measure.map Prod.fst) (map_sphereDirection_prod_uniformBallMeasure e c hr)
  rwa [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod, measure_univ,
    one_smul] at h

/-- The mean squared distance of a uniform point of a ball of radius `r` from its center is
`d r ^ 2 / (d + 2)`. -/
theorem integral_norm_sub_sq_uniformBallMeasure (c : E) (hr : 0 ≤ r) :
    ∫ x, ‖x - c‖ ^ 2 ∂uniformBallMeasure c r = finrank ℝ E * r ^ 2 / (finrank ℝ E + 2) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim _ c, finrank_zero_of_subsingleton]
  set d := finrank ℝ E
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 finrank_pos
  have hG₂ : Real.Gamma (d + 2) = (d + 1) * d * Real.Gamma d := by
    rw [show (d : ℝ) + 2 = d + 1 + 1 by ring, Real.Gamma_add_one (by positivity),
      Real.Gamma_add_one hd.ne']
    ring
  have hG₃ : Real.Gamma (d + 1 + 2) = (d + 2) * (d + 1) * Real.Gamma (d + 1) := by
    rw [show (d : ℝ) + 1 + 2 = d + 1 + 1 + 1 by ring, Real.Gamma_add_one (by positivity),
      Real.Gamma_add_one (by positivity)]
    ring
  -- Write the squared distance through the normalized radius, which is beta distributed.
  calc ∫ x, ‖x - c‖ ^ 2 ∂uniformBallMeasure c r
      = ∫ t, r ^ 2 * t ^ 2 ∂(uniformBallMeasure c r).map (fun x ↦ ‖x - c‖ / r) := by
        rw [integral_map (by fun_prop) (by fun_prop)]
        congr 1
        funext x
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hr.ne')]
    _ = d * r ^ 2 / (d + 2) := by
      rw [map_norm_sub_div_uniformBallMeasure c hr, integral_const_mul,
        integral_pow_betaMeasure hd one_pos]
      push_cast
      rw [hG₂, hG₃]
      have := Real.Gamma_pos_of_pos hd
      have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < d + 1)
      field_simp

/-- **Covariance of the uniform ball law.** The uniform law on a ball of radius `r ≥ 0` in
dimension `d` has covariance `r ^ 2 / (d + 2)` times the inner product. -/
theorem covarianceBilin_uniformBallMeasure (c : E) (hr : 0 ≤ r) :
    covarianceBilin (uniformBallMeasure c r) = (r ^ 2 / (finrank ℝ E + 2)) • innerSL ℝ := by
  have := isProbabilityMeasure_uniformBallMeasure (c := (0 : E)) hr
  rw [uniformBallMeasure_eq_map_const_add c, covarianceBilin_map_const_add,
    covarianceBilin_eq_smul_innerSL fun f ↦ by simpa using f.map_uniformBallMeasure 0 r]
  rcases subsingleton_or_nontrivial E with hE | hE
  · ext x y
    simp [Subsingleton.elim x 0]
  have hd : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have h := integral_norm_sub_sq_uniformBallMeasure (0 : E) hr
  simp only [sub_zero] at h
  rw [h]
  congr 1
  field_simp

end Radius

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti TauCeti.Probability Metric Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → E}
  {c : E} {r : ℝ}

/-- The normalized radius `‖X - c‖ / r` of a random vector uniform on a ball of center `c` and
radius `r > 0`, in positive dimension `d`, has the beta law with parameters `d` and `1`. -/
theorem HasLaw.norm_sub_div_uniformBallMeasure [Nontrivial E]
    (hX : HasLaw X (uniformBallMeasure c r) P) (hr : 0 < r) :
    HasLaw (fun ω ↦ ‖X ω - c‖ / r) (betaMeasure (finrank ℝ E) 1) P :=
  HasLaw.comp ⟨(by fun_prop), map_norm_sub_div_uniformBallMeasure c hr⟩ hX

/-- The direction `(X - c) / ‖X - c‖` of a random vector uniform on a ball of center `c` and
radius `r > 0` is uniform on the unit sphere. -/
theorem HasLaw.sphereDirection_uniformBallMeasure (hX : HasLaw X (uniformBallMeasure c r) P)
    (hr : 0 < r) (e : sphere (0 : E) 1) :
    HasLaw (fun ω ↦ sphereDirection e (X ω - c)) (uniformSphereMeasure E) P :=
  HasLaw.comp (Y := fun x ↦ sphereDirection e (x - c))
    ⟨((measurable_sphereDirection e).comp (measurable_sub_const c)).aemeasurable,
      map_sphereDirection_uniformBallMeasure e c hr⟩ hX

/-- The direction of a random vector uniform on a ball about its center is independent of its
normalized distance from the center. -/
theorem HasLaw.indepFun_sphereDirection_norm_uniformBallMeasure
    (hX : HasLaw X (uniformBallMeasure c r) P) (hr : 0 < r) (e : sphere (0 : E) 1) :
    IndepFun (fun ω ↦ sphereDirection e (X ω - c)) (fun ω ↦ ‖X ω - c‖ / r) P := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  have := isProbabilityMeasure_uniformBallMeasure (c := c) hr.le
  have := hX.isProbabilityMeasure
  have hdir : Measurable (sphereDirection e) := measurable_sphereDirection e
  refine (indepFun_iff_hasLaw_prodMk_prod (hX.sphereDirection_uniformBallMeasure hr e)
    (hX.norm_sub_div_uniformBallMeasure hr)).2 ?_
  exact HasLaw.comp ⟨(by fun_prop), map_sphereDirection_prod_uniformBallMeasure e c hr⟩ hX

end ProbabilityTheory
