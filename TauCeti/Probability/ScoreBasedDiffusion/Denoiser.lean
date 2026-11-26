/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Probability.DenoisingDiffusion.SmoothedDensity

import TauCeti.Analysis.InnerProductSpace.Positive.Integral

/-!
# The denoiser and the pointwise Tweedie formulas

Let `X` have law `μ₀` on `EuclideanSpace ℝ ι`, let `Z` be an independent standard Gaussian vector
and observe `Y = c • X + s • Z` with `s ≠ 0`. Given the observation `y`, the posterior law of `X`
is the probability measure with density `x ↦ φ_{s²}(y - c • x) / p(y)` with respect to `μ₀`, where
`φ_{s²}` is the density of `N(0, s² • 1)` and `p = smoothedDensity μ₀ c s` is the density of `Y`.
This file defines the mean and the covariance of that posterior law,

* the *denoiser* `m(y) = p(y)⁻¹ ∫ φ_{s²}(y - c • x) x dμ₀(x)`, and
* the *posterior covariance* `Σ(y) = p(y)⁻¹ ∫ φ_{s²}(y - c • x) (x - m(y)) ⊗ (x - m(y)) dμ₀(x)`,

with `u ⊗ u` the rank-one operator `w ↦ ⟪u, w⟫ • u`, and expresses the score `∇ log p` and its
derivative through them:

* (first order, Tweedie's formula) `∇ log p(y) = (c m(y) - y) / s²`;
* (second order) the derivative of `∇ log p` at `y` is `((c² / s²) Σ(y) - 1) / s²`.

Both formulas hold at every point, for every finite nonzero data law `μ₀` and every signal level
`c`, with no moment assumption: the integrals defining `m` and `Σ` converge absolutely when `c ≠ 0`
because `‖z‖² φ_{s²}(z)` is bounded, and for `c = 0` they enter the formulas multiplied by `c`.
Since `Σ(y)` is a positive operator, the derivative of the score is bounded below by `-1 / s²` as
a quadratic form, which is the second-order condition for `y ↦ log p(y) + ‖y‖² / (2 s²)` to be
convex.

## Main definitions

* `TauCeti.Probability.denoiser μ₀ c s y`: the posterior mean `m(y)`.
* `TauCeti.Probability.posteriorCov μ₀ c s y`: the posterior covariance `Σ(y)`.

## Main results

* `TauCeti.Probability.noisyScore_eq_denoiser`: Tweedie's formula `∇ log p = (c m - y) / s²`.
* `TauCeti.Probability.isPositive_posteriorCov`: the posterior covariance is a positive operator.
* `TauCeti.Probability.hasFDerivAt_noisyScore`: the second-order Tweedie formula.
* `TauCeti.Probability.le_inner_fderiv_noisyScore`: the derivative of the score is at least
  `-1 / s²` as a quadratic form.

## References

* B. Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. **106** (2011),
  1602–1614, equation (1.3), for the first-order formula; the same paper expresses the posterior
  variance through the second derivative of `log p` in dimension one.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory InnerProductSpace ContinuousLinearMap
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **denoiser** `p(y)⁻¹ ∫ φ_{s²}(y - c • x) x dμ₀(x)`. For a finite nonzero `μ₀` and
`s ≠ 0` it is the mean of the posterior law of `X` given the observation `c • X + s • Z = y`, for
`X` with law `μ₀` and an independent standard Gaussian vector `Z`, whenever `c ≠ 0` or `μ₀` has a
first moment. Otherwise (`c = 0` and no first moment) the integral diverges and the denoiser is
`0`, Bochner's value for a non-integrable integrand. -/
def denoiser (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  (smoothedDensity μ₀ c s y)⁻¹ •
    ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • x ∂μ₀

/-- The **posterior covariance** `p(y)⁻¹ ∫ φ_{s²}(y - c • x) (x - m) ⊗ (x - m) dμ₀(x)`, where
`m = denoiser μ₀ c s y` and `u ⊗ u = rankOne ℝ u u` is the operator `w ↦ ⟪u, w⟫ • u`. For a finite
nonzero `μ₀` and `s ≠ 0` it is the covariance operator of the posterior law of `X` given the
observation `c • X + s • Z = y` whenever `c ≠ 0` or `μ₀` has a second moment. Otherwise (`c = 0`
and no second moment) the integral diverges and the value is `0`, Bochner's value for a
non-integrable integrand. -/
def posteriorCov (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (smoothedDensity μ₀ c s y)⁻¹ •
    ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
      rankOne ℝ (x - denoiser μ₀ c s y) (x - denoiser μ₀ c s y) ∂μ₀

variable {μ₀ : Measure (EuclideanSpace ℝ ι)} {c s : ℝ}

/-- The defining formula of the denoiser. -/
theorem denoiser_def (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    denoiser μ₀ c s y = (smoothedDensity μ₀ c s y)⁻¹ •
      ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • x ∂μ₀ :=
  (rfl)

/-- The defining formula of the posterior covariance. -/
theorem posteriorCov_def (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    posteriorCov μ₀ c s y = (smoothedDensity μ₀ c s y)⁻¹ •
      ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
        rankOne ℝ (x - denoiser μ₀ c s y) (x - denoiser μ₀ c s y) ∂μ₀ :=
  (rfl)

/-! ### Moments of the noise -/

section Moments

/-- The unnormalized first moment `∫ φ_{s²}(y - c • x) (y - c • x) dμ₀(x)` of the noise
`y - c • x`; it is `-s² ∇p(y)`. -/
private def noiseFirstMoment (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ)
    (y : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀

/-- The unnormalized second moment `∫ φ_{s²}(y - c • x) (y - c • x) ⊗ (y - c • x) dμ₀(x)` of the
noise `y - c • x`. -/
private def noiseSecondMoment (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ)
    (y : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • rankOne ℝ (y - c • x) (y - c • x) ∂μ₀

private theorem noiseFirstMoment_def (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ)
    (y : EuclideanSpace ℝ ι) : noiseFirstMoment μ₀ c s y =
      ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀ :=
  (rfl)

private theorem noiseSecondMoment_def (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ)
    (y : EuclideanSpace ℝ ι) : noiseSecondMoment μ₀ c s y =
      ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
        rankOne ℝ (y - c • x) (y - c • x) ∂μ₀ :=
  (rfl)

/-- Against a finite measure, `x ↦ φ_{s²}(y - c • x) (y - c • x)` is integrable. -/
private theorem integrable_pdf_sub_smul_sub [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x))
      μ₀ :=
  integrable_multivariateGaussianPDFReal_sub_smul_smul hs continuous_id (K := 1) 2
    (fun z ↦ by simp only [id]; nlinarith [norm_nonneg z]) y

/-- Against a finite measure, `x ↦ φ_{s²}(y - c • x) (y - c • x) ⊗ (y - c • x)` is
integrable. -/
private theorem integrable_pdf_sub_smul_rankOne [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
      rankOne ℝ (y - c • x) (y - c • x)) μ₀ :=
  integrable_multivariateGaussianPDFReal_sub_smul_smul hs (g := fun z ↦ rankOne ℝ z z)
    (by simp only [rankOne_def]; fun_prop) (K := 1) 2 (fun z ↦ by
      rw [norm_rankOne, one_mul]
      nlinarith [norm_nonneg z]) y

end Moments

/-! ### Tweedie's formula -/

/-- The first moment of the unnormalized posterior, multiplied by the signal level:
`c ∫ φ_{s²}(y - c • x) x dμ₀(x) = p(y) y - ∫ φ_{s²}(y - c • x) (y - c • x) dμ₀(x)`. The right side
converges for every finite `μ₀`, also when the left integral does not. -/
private theorem smul_integral_pdf_smul [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    c • ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • x ∂μ₀ =
      smoothedDensity μ₀ c s y • y - noiseFirstMoment μ₀ c s y := by
  rw [← integral_smul, smoothedDensity_apply, ← integral_smul_const, noiseFirstMoment_def,
    ← integral_sub ((integrable_multivariateGaussianPDFReal_sub_smul hs y).smul_const y)
      (integrable_pdf_sub_smul_sub hs y)]
  congr 1
  funext x
  rw [← smul_sub, sub_sub_cancel, smul_comm]

/-- The signal level times the denoiser is the observation minus the normalized first moment of
the noise. -/
private theorem smul_denoiser [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    c • denoiser μ₀ c s y = y - (smoothedDensity μ₀ c s y)⁻¹ • noiseFirstMoment μ₀ c s y := by
  rw [denoiser_def, smul_comm, smul_integral_pdf_smul hs, smul_sub, smul_smul,
    inv_mul_cancel₀ (smoothedDensity_pos hs y).ne', one_smul]

/-- **Tweedie's formula, at every point.** For a finite nonzero data law `μ₀`, every signal level
`c` and every noise level `s ≠ 0`, the score of the law of `c • X + s • Z` is
`∇ log p(y) = (c m(y) - y) / s²`, with `m` the denoiser. No moment of `μ₀` is assumed; for `c = 0`
this reads `∇ log p(y) = -y / s²`. -/
theorem noisyScore_eq_denoiser [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    noisyScore μ₀ c s y = (s ^ 2)⁻¹ • (c • denoiser μ₀ c s y - y) := by
  rw [noisyScore_eq_integral hs, ← noiseFirstMoment_def, smul_denoiser hs, sub_sub_cancel_left,
    smul_neg, neg_smul]

/-! ### The posterior covariance as a second moment -/

section Covariance

/-- The second moment of the noise `z = y - c • x` about a point `a` under the unnormalized
posterior: `∫ φ_{s²}(z) (z - a) ⊗ (z - a) = H - a ⊗ G - G ⊗ a + p(y) a ⊗ a`, where `G` and `H` are
the first and second moments of the noise. -/
private theorem integral_pdf_smul_rankOne_sub [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (a y : EuclideanSpace ℝ ι) :
    ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
        rankOne ℝ (y - c • x - a) (y - c • x - a) ∂μ₀ =
      noiseSecondMoment μ₀ c s y - rankOne ℝ a (noiseFirstMoment μ₀ c s y) -
        rankOne ℝ (noiseFirstMoment μ₀ c s y) a + smoothedDensity μ₀ c s y • rankOne ℝ a a := by
  have hz := integrable_pdf_sub_smul_sub (μ₀ := μ₀) (c := c) hs y
  have hH := integrable_pdf_sub_smul_rankOne (μ₀ := μ₀) (c := c) hs y
  have hp := (integrable_multivariateGaussianPDFReal_sub_smul (μ₀ := μ₀) (c := c) hs y).smul_const
    (rankOne ℝ a a)
  -- `R` is the continuous linear map `u ↦ u ⊗ a`; it and `u ↦ a ⊗ u` commute with `∫`.
  set R := (rankOne ℝ (E := EuclideanSpace ℝ ι)).flip a
  have hR (u : EuclideanSpace ℝ ι) : R u = rankOne ℝ u a := ContinuousLinearMap.flip_apply _ _ _
  have hL := (rankOne ℝ a).integrable_comp hz
  set φ := multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1)
  -- Expand `(z - a) ⊗ (z - a)` by bilinearity of `rankOne`.
  have e (x : EuclideanSpace ℝ ι) : φ (y - c • x) • rankOne ℝ (y - c • x - a) (y - c • x - a) =
      φ (y - c • x) • rankOne ℝ (y - c • x) (y - c • x) -
        rankOne ℝ a (φ (y - c • x) • (y - c • x)) - R (φ (y - c • x) • (y - c • x)) +
        φ (y - c • x) • rankOne ℝ a a := by
    simp only [hR, map_sub, map_smul, sub_apply, smul_apply, smul_sub]
    abel
  rw [integral_congr_ae (ae_of_all _ e), integral_add ((hH.sub' hL).sub' (R.integrable_comp hz)) hp,
    integral_sub (hH.sub' hL) (R.integrable_comp hz), integral_sub hH hL,
    (rankOne ℝ a).integral_comp_commSL (by simp) hz, R.integral_comp_comm hz, integral_smul_const,
    ← smoothedDensity_apply, hR, noiseFirstMoment_def, noiseSecondMoment_def]

/-- The signal level squared times the rank-one operator `(x - m) ⊗ (x - m)`, for `m` the
denoiser at `y`, is `(z - a) ⊗ (z - a)` with `z = y - c • x` and `a = p(y)⁻¹ G` the normalized
first moment of the noise. -/
private theorem sq_smul_rankOne_sub_denoiser [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (x y : EuclideanSpace ℝ ι) :
    c ^ 2 • rankOne ℝ (x - denoiser μ₀ c s y) (x - denoiser μ₀ c s y) =
      rankOne ℝ (y - c • x - (smoothedDensity μ₀ c s y)⁻¹ • noiseFirstMoment μ₀ c s y)
        (y - c • x - (smoothedDensity μ₀ c s y)⁻¹ • noiseFirstMoment μ₀ c s y) := by
  have hcx : c • (x - denoiser μ₀ c s y) =
      -(y - c • x - (smoothedDensity μ₀ c s y)⁻¹ • noiseFirstMoment μ₀ c s y) := by
    rw [smul_sub, smul_denoiser hs]
    abel
  rw [← neg_neg (y - c • x - _), ← hcx]
  ext1 w
  simp only [smul_apply, rankOne_apply, inner_neg_left, real_inner_smul_left, smul_neg, smul_smul]
  module

/-- The signal level squared times the posterior covariance is the normalized second moment of
the noise minus the square of its normalized first moment. -/
private theorem sq_smul_posteriorCov [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    c ^ 2 • posteriorCov μ₀ c s y =
      (smoothedDensity μ₀ c s y)⁻¹ • noiseSecondMoment μ₀ c s y -
        (smoothedDensity μ₀ c s y)⁻¹ ^ 2 •
          rankOne ℝ (noiseFirstMoment μ₀ c s y) (noiseFirstMoment μ₀ c s y) := by
  rw [posteriorCov_def, smul_comm, ← integral_smul]
  simp_rw [smul_comm (c ^ 2), sq_smul_rankOne_sub_denoiser hs _ y]
  rw [integral_pdf_smul_rankOne_sub hs]
  have hp : smoothedDensity μ₀ c s y ≠ 0 := (smoothedDensity_pos hs y).ne'
  set p := smoothedDensity μ₀ c s y
  set g := noiseFirstMoment μ₀ c s y
  ext1 w
  simp only [smul_apply, add_apply, sub_apply, rankOne_apply, real_inner_smul_left, smul_smul]
  rw [show p * (p⁻¹ * ⟪g, w⟫ * p⁻¹) = p⁻¹ * ⟪g, w⟫ by field_simp]
  module

end Covariance

/-! ### The derivative of the score -/

section Derivative

/-- Differentiation under the integral sign of the first moment of the noise, the integral giving
`-s² ∇p(y)`. -/
private theorem hasFDerivAt_noiseFirstMoment [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    HasFDerivAt (noiseFirstMoment μ₀ c s)
      (smoothedDensity μ₀ c s y • ContinuousLinearMap.id ℝ _ -
        (s ^ 2)⁻¹ • noiseSecondMoment μ₀ c s y) y := by
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_multivariateGaussianPDFReal_smul_one_le
    (ι := ι) (by positivity : 0 < s ^ 2) 2
  have hid : Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) μ₀ :=
    (integrable_multivariateGaussianPDFReal_sub_smul hs y).smul_const _
  have hrk : Integrable (fun x ↦ ((s ^ 2)⁻¹ *
      multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x)) •
        rankOne ℝ (y - c • x) (y - c • x)) μ₀ := by
    simpa only [Pi.smul_def, mul_smul] using
      (integrable_pdf_sub_smul_rankOne (μ₀ := μ₀) (c := c) hs y).smul (s ^ 2)⁻¹
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ₀) (x₀ := y)
    (F := fun y x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x))
    (F' := fun y x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
        ContinuousLinearMap.id ℝ _ - ((s ^ 2)⁻¹ *
          multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x)) •
        rankOne ℝ (y - c • x) (y - c • x))
    (bound := fun _ ↦ (1 + (s ^ 2)⁻¹) * C) Filter.univ_mem
    (.of_forall fun y' ↦ (integrable_pdf_sub_smul_sub hs y').aestronglyMeasurable)
    (integrable_pdf_sub_smul_sub hs y) (hid.sub hrk).aestronglyMeasurable
    (.of_forall fun x y' _ ↦ by
      rw [← (hasFDerivAt_multivariateGaussianPDFReal_smul_one_smul_self
        (by positivity : 0 < s ^ 2) (y' - c • x)).fderiv]
      exact (norm_fderiv_multivariateGaussianPDFReal_smul_one_smul_self_le
        (by positivity) _).trans (mul_le_mul_of_nonneg_left (hC _) (by positivity)))
    (integrable_const _)
    (.of_forall fun x y' _ ↦ by
      have h := (hasFDerivAt_multivariateGaussianPDFReal_smul_one_smul_self
        (by positivity : 0 < s ^ 2) (y' - c • x)).comp y' ((hasFDerivAt_id y').sub_const (c • x))
      rwa [comp_id] at h)
  rw [funext (noiseFirstMoment_def μ₀ c s)]
  refine key.congr_fderiv ?_
  rw [integral_sub hid hrk, integral_smul_const, ← smoothedDensity_apply, noiseSecondMoment_def]
  simp only [mul_smul, integral_smul]

/-- **The posterior covariance is a positive operator**, for every data law, every level and
every observation. -/
theorem isPositive_posteriorCov (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ)
    (y : EuclideanSpace ℝ ι) : (posteriorCov μ₀ c s y).IsPositive := by
  rw [posteriorCov_def]
  refine (isPositive_integral fun x ↦ ?_).smul_of_nonneg
    (inv_nonneg.2 (smoothedDensity_nonneg μ₀ c s y))
  exact (isPositive_rankOne_self _).smul_of_nonneg (multivariateGaussianPDFReal_nonneg _ _ _)

/-- **The second-order Tweedie formula, at every point.** For a finite nonzero data law `μ₀`,
every signal level `c` and every noise level `s ≠ 0`, the score of the law of `c • X + s • Z` has
at every `y` the derivative `((c² / s²) Σ(y) - 1) / s²`, with `Σ` the posterior covariance. No
moment of `μ₀` is assumed; for `c = 0` the derivative is `-1 / s²`. -/
theorem hasFDerivAt_noisyScore [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    HasFDerivAt (noisyScore μ₀ c s)
      ((s ^ 2)⁻¹ • ((c ^ 2 / s ^ 2) • posteriorCov μ₀ c s y - ContinuousLinearMap.id ℝ _)) y := by
  have hp0 : smoothedDensity μ₀ c s y ≠ 0 := (smoothedDensity_pos hs y).ne'
  have hp := hasGradientAt_iff_hasFDerivAt.1
    (hasGradientAt_smoothedDensity (μ₀ := μ₀) (c := c) hs y)
  rw [← noiseFirstMoment_def] at hp
  have h := (((hasDerivAt_inv hp0).comp_hasFDerivAt y hp).smul
    (hasFDerivAt_noiseFirstMoment (μ₀ := μ₀) (c := c) hs y)).const_smul (-(s ^ 2)⁻¹)
  rw [funext (noisyScore_eq_integral (μ₀ := μ₀) (c := c) hs)]
  simp only [← noiseFirstMoment_def]
  refine h.congr_fderiv ?_
  rw [div_eq_inv_mul, mul_smul, sq_smul_posteriorCov hs]
  ext1 w
  simp only [Function.comp_apply, smul_apply, sub_apply, add_apply, smulRight_apply,
    ContinuousLinearMap.id_apply, rankOne_apply, toDual_apply_apply, real_inner_smul_left]
  rw [smul_add, smul_sub, inv_smul_smul₀ hp0, ← inv_pow]
  module

/-- **The derivative of the score is bounded below.** For a finite data law, the derivative of the
score is at least `-1 / s²` as a quadratic form: `⟪D(∇ log p)(y) w, w⟫ ≥ -‖w‖² / s²`. This is the
second-order condition for `y ↦ log p(y) + ‖y‖² / (2 s²)` to be convex, that is, for `log p` to be
semiconvex. -/
theorem le_inner_fderiv_noisyScore [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y w : EuclideanSpace ℝ ι) :
    -(‖w‖ ^ 2 / s ^ 2) ≤ ⟪fderiv ℝ (noisyScore μ₀ c s) y w, w⟫ := by
  rcases eq_zero_or_neZero μ₀ with rfl | _
  · -- For the zero measure the score vanishes identically.
    simp only [noisyScore_zero, fderiv_zero, Pi.zero_apply, zero_apply, inner_zero_left]
    exact neg_nonpos.2 (by positivity)
  rw [(hasFDerivAt_noisyScore hs y).fderiv]
  simp only [smul_apply, sub_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
    inner_sub_left, real_inner_self_eq_norm_sq]
  have hcov := (isPositive_posteriorCov μ₀ c s y).inner_nonneg_left w
  have : 0 ≤ (s ^ 2)⁻¹ * (c ^ 2 / s ^ 2 * ⟪posteriorCov μ₀ c s y w, w⟫) := by positivity
  rw [mul_sub, div_eq_inv_mul (‖w‖ ^ 2)]
  linarith

end Derivative

/-! ### Point masses -/

/-- For a point mass `δ_{x₀}` the posterior law is `δ_{x₀}` and the denoiser is `x₀`. -/
@[simp]
theorem denoiser_dirac (x₀ : EuclideanSpace ℝ ι) (hs : s ≠ 0) (y : EuclideanSpace ℝ ι) :
    denoiser (Measure.dirac x₀) c s y = x₀ := by
  rw [denoiser_def, integral_dirac, smoothedDensity_dirac, smul_smul,
    inv_mul_cancel₀ (multivariateGaussianPDFReal_pos
      (Matrix.PosDef.one.smul (by positivity : 0 < s ^ 2)).det_pos _ _).ne', one_smul]

/-- For a point mass the posterior covariance vanishes. -/
@[simp]
theorem posteriorCov_dirac (x₀ : EuclideanSpace ℝ ι) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    posteriorCov (Measure.dirac x₀) c s y = 0 := by
  rw [posteriorCov_def, integral_dirac, denoiser_def, integral_dirac, smoothedDensity_dirac]
  rcases eq_or_ne (multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x₀)) 0 with hq | hq
  · simp [hq]
  · simp [inv_smul_smul₀ hq]

end TauCeti.Probability
