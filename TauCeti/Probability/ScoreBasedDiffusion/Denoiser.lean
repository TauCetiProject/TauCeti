/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Probability.DenoisingDiffusion.SmoothedDensity

import TauCeti.Analysis.InnerProductSpace.Positive.Integral
import TauCeti.Analysis.PDE.HeatKernel.Bounds

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

/-- The **denoiser**: the mean `p(y)⁻¹ ∫ φ_{s²}(y - c • x) x dμ₀(x)` of the posterior law of `X`
given the observation `c • X + s • Z = y`, for `X` with law `μ₀` and an independent standard
Gaussian vector `Z`. -/
def denoiser (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  (smoothedDensity μ₀ c s y)⁻¹ •
    ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • x ∂μ₀

/-- The **posterior covariance**: the covariance operator
`p(y)⁻¹ ∫ φ_{s²}(y - c • x) (x - m) ⊗ (x - m) dμ₀(x)` of the posterior law of `X` given the
observation `c • X + s • Z = y`, where `m = denoiser μ₀ c s y` and `u ⊗ u = rankOne ℝ u u` is the
operator `w ↦ ⟪u, w⟫ • u`. -/
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

/-! ### Integrability of Gaussian moments -/

section Integrability

/-- The Gaussian density `φ_{s²}` decays fast enough to absorb a quadratic weight. -/
private theorem exists_one_add_norm_sq_mul_pdf_le (hs : s ≠ 0) :
    ∃ C, ∀ z : EuclideanSpace ℝ ι,
      (1 + ‖z‖) ^ 2 * multivariateGaussianPDFReal 0 (s ^ 2 • 1) z ≤ C := by
  have hv : 0 < s ^ 2 / 2 := by positivity
  obtain ⟨C, hC0, hC⟩ :=
    exists_one_add_norm_pow_mul_heatKernel_le (E := EuclideanSpace ℝ ι) hv 2
  refine ⟨C * (4 * Real.pi * (2 * (s ^ 2 / 2))) ^
    (-(Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / 2), fun z ↦ ?_⟩
  rw [multivariateGaussianPDFReal_zero_smul_one (by positivity)]
  exact (hC z).trans (mul_le_mul_of_nonneg_left (heatKernel_le (by positivity) z) hC0.le)

/-- Against a finite measure, `x ↦ φ_{s²}(y - c • x) • g(y - c • x)` is integrable for every
continuous `g` of at most quadratic growth. -/
private theorem integrable_pdf_sub_smul_smul [IsFiniteMeasure μ₀] (hs : s ≠ 0) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : EuclideanSpace ℝ ι → F} (hg : Continuous g)
    {K : ℝ} (hgK : ∀ z, ‖g z‖ ≤ K * (1 + ‖z‖) ^ 2) (y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
      g (y - c • x)) μ₀ := by
  obtain ⟨C, hC⟩ := exists_one_add_norm_sq_mul_pdf_le (ι := ι) hs
  have hφ : Continuous (multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1)) :=
    (contDiff_multivariateGaussianPDFReal_smul_one (n := 0) (by positivity) 0).continuous
  refine Integrable.of_bound (C := K * C)
    ((hφ.smul hg).comp (by fun_prop : Continuous fun x : EuclideanSpace ℝ ι ↦ y - c • x)
      |>.aestronglyMeasurable) (.of_forall fun x ↦ ?_)
  set z := y - c • x
  have hφz := multivariateGaussianPDFReal_nonneg (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1) z
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hgK 0)
  rw [norm_smul, Real.norm_of_nonneg hφz]
  calc multivariateGaussianPDFReal 0 (s ^ 2 • 1) z * ‖g z‖
      ≤ multivariateGaussianPDFReal 0 (s ^ 2 • 1) z * (K * (1 + ‖z‖) ^ 2) :=
        mul_le_mul_of_nonneg_left (hgK z) hφz
    _ = K * ((1 + ‖z‖) ^ 2 * multivariateGaussianPDFReal 0 (s ^ 2 • 1) z) := by ring
    _ ≤ K * C := mul_le_mul_of_nonneg_left (hC z) hK

/-- Against a finite measure, `x ↦ φ_{s²}(y - c • x) (y - c • x)` is integrable. -/
private theorem integrable_pdf_sub_smul_sub [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x))
      μ₀ :=
  integrable_pdf_sub_smul_smul hs continuous_id (K := 1)
    (fun z ↦ by simp only [id]; nlinarith [norm_nonneg z]) y

/-- Against a finite measure, `x ↦ φ_{s²}(y - c • x) (y - c • x - a) ⊗ (y - c • x - a)` is
integrable. -/
private theorem integrable_pdf_sub_smul_rankOne [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (a y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
      rankOne ℝ (y - c • x - a) (y - c • x - a)) μ₀ :=
  integrable_pdf_sub_smul_smul hs (g := fun z ↦ rankOne ℝ (z - a) (z - a))
    (by simp only [rankOne_def]; fun_prop) (K := (1 + ‖a‖) ^ 2) (fun z ↦ by
      rw [norm_rankOne, ← sq, ← mul_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      nlinarith [norm_nonneg z, norm_nonneg a]) y

/-- The case `a = 0` of `integrable_pdf_sub_smul_rankOne`. -/
private theorem integrable_pdf_sub_smul_rankOne_self [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
      rankOne ℝ (y - c • x) (y - c • x)) μ₀ := by
  simpa only [sub_zero] using integrable_pdf_sub_smul_rankOne (μ₀ := μ₀) (c := c) hs 0 y

end Integrability

/-! ### Tweedie's formula -/

/-- The first moment of the unnormalized posterior, multiplied by the signal level:
`c ∫ φ_{s²}(y - c • x) x dμ₀(x) = p(y) y - ∫ φ_{s²}(y - c • x) (y - c • x) dμ₀(x)`. The right side
converges for every finite `μ₀`, also when the left integral does not. -/
private theorem smul_integral_pdf_smul [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    c • ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • x ∂μ₀ =
      smoothedDensity μ₀ c s y • y -
        ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀ := by
  rw [← integral_smul, smoothedDensity_apply, ← integral_smul_const,
    ← integral_sub ((integrable_pdf_sub_smul hs y).smul_const y) (integrable_pdf_sub_smul_sub hs y)]
  congr 1
  funext x
  rw [← smul_sub, sub_sub_cancel, smul_comm]

/-- The signal level times the denoiser is the observation minus the normalized integral of
`φ_{s²}(y - c • x) (y - c • x)`. -/
private theorem smul_denoiser [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    c • denoiser μ₀ c s y = y - (smoothedDensity μ₀ c s y)⁻¹ •
      ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀ := by
  rw [denoiser_def, smul_comm, smul_integral_pdf_smul hs, smul_sub, smul_smul,
    inv_mul_cancel₀ (smoothedDensity_pos hs y).ne', one_smul]

/-- **Tweedie's formula, at every point.** For a finite nonzero data law `μ₀`, every signal level
`c` and every noise level `s ≠ 0`, the score of the law of `c • X + s • Z` is
`∇ log p(y) = (c m(y) - y) / s²`, with `m` the denoiser. No moment of `μ₀` is assumed; for `c = 0`
this reads `∇ log p(y) = -y / s²`. -/
theorem noisyScore_eq_denoiser [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    noisyScore μ₀ c s y = (s ^ 2)⁻¹ • (c • denoiser μ₀ c s y - y) := by
  rw [noisyScore_eq_integral hs, smul_denoiser hs, sub_sub_cancel_left, smul_neg, neg_smul]

/-! ### The posterior covariance as a second moment -/

section Covariance

/-- The second moment of `z = y - c • x` about a point `a` under the unnormalized posterior:
`∫ φ_{s²}(z) (z - a) ⊗ (z - a) = ∫ φ_{s²}(z) z ⊗ z - a ⊗ G - G ⊗ a + p(y) a ⊗ a`, where
`G = ∫ φ_{s²}(z) z`. -/
private theorem integral_pdf_smul_rankOne_sub [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (a y : EuclideanSpace ℝ ι) :
    ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
        rankOne ℝ (y - c • x - a) (y - c • x - a) ∂μ₀ =
      (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
          rankOne ℝ (y - c • x) (y - c • x) ∂μ₀) -
        rankOne ℝ a (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀) -
        rankOne ℝ (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀) a +
        smoothedDensity μ₀ c s y • rankOne ℝ a a := by
  set φ := multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1)
  have hz := integrable_pdf_sub_smul_sub (μ₀ := μ₀) (c := c) hs y
  ext1 w
  have I0 : Integrable (fun x ↦ φ (y - c • x) • ⟪y - c • x, w⟫ • (y - c • x)) μ₀ := by
    simpa only [smul_apply, rankOne_apply] using
      (integrable_pdf_sub_smul_rankOne_self (μ₀ := μ₀) (c := c) hs y).apply_continuousLinearMap w
  have I1 : Integrable (fun x ↦ ⟪φ (y - c • x) • (y - c • x), w⟫ • a) μ₀ :=
    (hz.inner_const w).smul_const a
  have I2 : Integrable (fun x ↦ ⟪a, w⟫ • (φ (y - c • x) • (y - c • x))) μ₀ := hz.smul ⟪a, w⟫
  have I3 : Integrable (fun x ↦ (⟪a, w⟫ * φ (y - c • x)) • a) μ₀ :=
    ((integrable_pdf_sub_smul hs y).const_mul ⟪a, w⟫).smul_const a
  have I01 : Integrable (fun x ↦ φ (y - c • x) • ⟪y - c • x, w⟫ • (y - c • x) -
      ⟪φ (y - c • x) • (y - c • x), w⟫ • a) μ₀ := I0.sub I1
  have I012 : Integrable (fun x ↦ φ (y - c • x) • ⟪y - c • x, w⟫ • (y - c • x) -
      ⟪φ (y - c • x) • (y - c • x), w⟫ • a - ⟪a, w⟫ • (φ (y - c • x) • (y - c • x))) μ₀ :=
    I01.sub I2
  have e (x : EuclideanSpace ℝ ι) :
      φ (y - c • x) • ⟪y - c • x - a, w⟫ • (y - c • x - a) =
        φ (y - c • x) • ⟪y - c • x, w⟫ • (y - c • x) - ⟪φ (y - c • x) • (y - c • x), w⟫ • a -
          ⟪a, w⟫ • (φ (y - c • x) • (y - c • x)) + (⟪a, w⟫ * φ (y - c • x)) • a := by
    simp only [inner_sub_left, real_inner_smul_left]
    module
  rw [integral_apply (integrable_pdf_sub_smul_rankOne hs a y) w, add_apply, sub_apply, sub_apply,
    integral_apply (integrable_pdf_sub_smul_rankOne_self hs y) w]
  simp only [smul_apply, rankOne_apply]
  rw [integral_congr_ae (ae_of_all _ e), integral_add I012 I3, integral_sub I01 I2,
    integral_sub I0 I1, integral_smul_const, integral_smul, integral_smul_const,
    integral_const_mul, ← smoothedDensity_apply]
  simp only [real_inner_comm w]
  rw [integral_inner hz w]
  module

/-- The signal level squared times the rank-one operator `(x - m) ⊗ (x - m)`, for `m` the
denoiser at `y`, is `(z - a) ⊗ (z - a)` with `z = y - c • x` and `a = p(y)⁻¹ ∫ φ_{s²}(z) z`. -/
private theorem sq_smul_rankOne_sub_denoiser [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (x y : EuclideanSpace ℝ ι) :
    c ^ 2 • rankOne ℝ (x - denoiser μ₀ c s y) (x - denoiser μ₀ c s y) =
      rankOne ℝ (y - c • x - (smoothedDensity μ₀ c s y)⁻¹ •
          ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀)
        (y - c • x - (smoothedDensity μ₀ c s y)⁻¹ •
          ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀) := by
  have hcx : c • (x - denoiser μ₀ c s y) = -(y - c • x - (smoothedDensity μ₀ c s y)⁻¹ •
      ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀) := by
    rw [smul_sub, smul_denoiser hs]
    abel
  rw [← neg_neg (y - c • x - _), ← hcx]
  ext1 w
  simp only [smul_apply, rankOne_apply, inner_neg_left, real_inner_smul_left, smul_neg, smul_smul]
  module

/-- The signal level squared times the posterior covariance is the normalized second moment of
`y - c • x` minus the square of its normalized first moment. -/
private theorem sq_smul_posteriorCov [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    c ^ 2 • posteriorCov μ₀ c s y =
      (smoothedDensity μ₀ c s y)⁻¹ • ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
        rankOne ℝ (y - c • x) (y - c • x) ∂μ₀ -
      (smoothedDensity μ₀ c s y)⁻¹ ^ 2 • rankOne ℝ
        (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀)
        (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀) := by
  have hp : smoothedDensity μ₀ c s y ≠ 0 := (smoothedDensity_pos hs y).ne'
  rw [posteriorCov_def, smul_comm, ← integral_smul]
  simp_rw [smul_comm (c ^ 2), sq_smul_rankOne_sub_denoiser hs _ y]
  rw [integral_pdf_smul_rankOne_sub hs]
  generalize (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
    rankOne ℝ (y - c • x) (y - c • x) ∂μ₀) = H
  generalize (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀) = g
  generalize smoothedDensity μ₀ c s y = p at hp ⊢
  ext1 w
  simp only [smul_apply, add_apply, sub_apply, rankOne_apply, real_inner_smul_left, smul_smul]
  rw [show p * (p⁻¹ * ⟪g, w⟫ * p⁻¹) = p⁻¹ * ⟪g, w⟫ by field_simp]
  module

end Covariance

/-! ### The derivative of the score -/

section Derivative

/-- The derivative of `z ↦ φ_{s²}(z) z` is `φ_{s²}(z) (1 - z ⊗ z / s²)`. -/
private theorem hasFDerivAt_pdf_smul_self (hs : s ≠ 0) (z : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun z ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) z • z)
      (multivariateGaussianPDFReal 0 (s ^ 2 • 1) z • ContinuousLinearMap.id ℝ _ -
        ((s ^ 2)⁻¹ * multivariateGaussianPDFReal 0 (s ^ 2 • 1) z) • rankOne ℝ z z) z := by
  have h := (hasGradientAt_multivariateGaussianPDFReal_smul_one
    (by positivity : 0 < s ^ 2) 0 z).hasFDerivAt
  refine (h.fun_smul (hasFDerivAt_id z)).congr_fderiv ?_
  ext1 w
  simp only [sub_zero, add_apply, smul_apply, ContinuousLinearMap.id_apply, smulRight_apply,
    toDual_apply_apply, sub_apply, rankOne_apply, real_inner_smul_left, mul_smul, id_eq]
  module

/-- The norm of the derivative of `z ↦ φ_{s²}(z) z` is controlled by a quadratic weight. -/
private theorem norm_pdf_smul_id_sub_le (z : EuclideanSpace ℝ ι) :
    ‖multivariateGaussianPDFReal 0 (s ^ 2 • 1) z • ContinuousLinearMap.id ℝ _ -
        ((s ^ 2)⁻¹ * multivariateGaussianPDFReal 0 (s ^ 2 • 1) z) • rankOne ℝ z z‖ ≤
      (1 + (s ^ 2)⁻¹) * ((1 + ‖z‖) ^ 2 * multivariateGaussianPDFReal 0 (s ^ 2 • 1) z) := by
  have hφ := multivariateGaussianPDFReal_nonneg (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1) z
  have hid : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)‖ ≤ 1 := norm_id_le
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_rankOne, Real.norm_of_nonneg hφ,
    Real.norm_of_nonneg (by positivity)]
  have h1 : 1 ≤ (1 + ‖z‖) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg z))
  have h2 : ‖z‖ * ‖z‖ ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  calc multivariateGaussianPDFReal 0 (s ^ 2 • 1) z * ‖ContinuousLinearMap.id ℝ _‖ +
        (s ^ 2)⁻¹ * multivariateGaussianPDFReal 0 (s ^ 2 • 1) z * (‖z‖ * ‖z‖)
      ≤ multivariateGaussianPDFReal 0 (s ^ 2 • 1) z * (1 + ‖z‖) ^ 2 +
        (s ^ 2)⁻¹ * multivariateGaussianPDFReal 0 (s ^ 2 • 1) z * (1 + ‖z‖) ^ 2 := by
        gcongr
        exact hid.trans h1
    _ = _ := by ring

/-- Differentiation under the integral sign of `y ↦ ∫ φ_{s²}(y - c • x) (y - c • x) dμ₀(x)`, the
integral giving `-s² ∇p(y)`. -/
private theorem hasFDerivAt_integral_pdf_smul_sub [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y ↦ ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
        (y - c • x) ∂μ₀)
      (smoothedDensity μ₀ c s y • ContinuousLinearMap.id ℝ _ - (s ^ 2)⁻¹ •
        ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
          rankOne ℝ (y - c • x) (y - c • x) ∂μ₀) y := by
  obtain ⟨C, hC⟩ := exists_one_add_norm_sq_mul_pdf_le (ι := ι) hs
  have hid : Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) μ₀ :=
    (integrable_pdf_sub_smul hs y).smul_const _
  have hrk : Integrable (fun x ↦ ((s ^ 2)⁻¹ *
      multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x)) •
        rankOne ℝ (y - c • x) (y - c • x)) μ₀ := by
    simpa only [Pi.smul_def, mul_smul] using
      (integrable_pdf_sub_smul_rankOne_self (μ₀ := μ₀) (c := c) hs y).smul (s ^ 2)⁻¹
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ₀) (x₀ := y)
    (F := fun y x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x))
    (F' := fun y x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
        ContinuousLinearMap.id ℝ _ - ((s ^ 2)⁻¹ *
          multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x)) •
        rankOne ℝ (y - c • x) (y - c • x))
    (bound := fun _ ↦ (1 + (s ^ 2)⁻¹) * C) Filter.univ_mem
    (.of_forall fun y' ↦ (integrable_pdf_sub_smul_sub hs y').aestronglyMeasurable)
    (integrable_pdf_sub_smul_sub hs y) (hid.sub hrk).aestronglyMeasurable
    (.of_forall fun x y' _ ↦ (norm_pdf_smul_id_sub_le _).trans
      (mul_le_mul_of_nonneg_left (hC _) (by positivity)))
    (integrable_const _)
    (.of_forall fun x y' _ ↦ by
      have h := (hasFDerivAt_pdf_smul_self hs (y' - c • x)).comp y'
        ((hasFDerivAt_id y').sub_const (c • x))
      rwa [comp_id] at h)
  convert key using 1
  rw [integral_sub hid hrk, integral_smul_const, ← smoothedDensity_apply]
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
  set G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun y ↦
    ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀
  have hp0 : smoothedDensity μ₀ c s y ≠ 0 := (smoothedDensity_pos hs y).ne'
  have hp : HasFDerivAt (smoothedDensity μ₀ c s) (toDual ℝ _ (-(s ^ 2)⁻¹ • G y)) y :=
    hasGradientAt_iff_hasFDerivAt.1 (hasGradientAt_smoothedDensity (μ₀ := μ₀) (c := c) hs y)
  have h := (((hasDerivAt_inv hp0).comp_hasFDerivAt y hp).smul
    (hasFDerivAt_integral_pdf_smul_sub (μ₀ := μ₀) (c := c) hs y)).const_smul (-(s ^ 2)⁻¹)
  rw [funext (noisyScore_eq_integral (μ₀ := μ₀) (c := c) hs)]
  refine h.congr_fderiv ?_
  rw [div_eq_inv_mul, mul_smul, sq_smul_posteriorCov hs]
  simp only [G, Function.comp_apply]
  generalize (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
    rankOne ℝ (y - c • x) (y - c • x) ∂μ₀) = H
  generalize (∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀) = g
  generalize smoothedDensity μ₀ c s y = p at hp0 ⊢
  ext1 w
  simp only [smul_apply, sub_apply, add_apply, smulRight_apply, ContinuousLinearMap.id_apply,
    rankOne_apply, toDual_apply_apply, real_inner_smul_left]
  rw [smul_add, smul_sub, inv_smul_smul₀ hp0, ← inv_pow]
  module

/-- **The score is semiconvex.** For a finite data law, the derivative of the score is at least
`-1 / s²` as a quadratic form: `⟪D(∇ log p)(y) w, w⟫ ≥ -‖w‖² / s²`. This is the second-order
condition for `y ↦ log p(y) + ‖y‖² / (2 s²)` to be convex. -/
theorem le_inner_fderiv_noisyScore [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y w : EuclideanSpace ℝ ι) :
    -(‖w‖ ^ 2 / s ^ 2) ≤ ⟪fderiv ℝ (noisyScore μ₀ c s) y w, w⟫ := by
  rcases eq_zero_or_neZero μ₀ with rfl | _
  · -- For the zero measure the density, hence the score, vanishes identically.
    have h0 : noisyScore (0 : Measure (EuclideanSpace ℝ ι)) c s = 0 := by
      funext z
      simp [noisyScore_apply, smoothedDensity_apply]
    rw [h0]
    simp only [fderiv_zero, Pi.zero_apply, zero_apply, inner_zero_left]
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
