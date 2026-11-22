/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Probability.Distributions.Gaussian.HeatKernel

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.PDE.HeatKernel.Bounds
import TauCeti.MeasureTheory.Group.Convolution.Translation
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.MeasureTheory.Measure.Mixture.Basic
import TauCeti.Probability.Distributions.Gaussian.Isotropic

/-!
# The density and score of a law observed through Gaussian noise

Let `X` have an arbitrary law `μ₀` on `EuclideanSpace ℝ ι`, let `Z` be a standard Gaussian vector
independent of `X`, and observe `Y = c • X + s • Z` with `c` real and `s ≠ 0`. Then `Y` has the
density

`p(y) = ∫ φ_{s²}(y - c • x) dμ₀(x)`,

where `φ_{s²}` is the density of the isotropic Gaussian law `N(0, s² • 1)`. No moment assumption
on `μ₀` is needed: since `φ_{s²}` is the heat kernel at time `s² / 2`, all of its derivatives are
bounded, so `p` is positive and smooth and every derivative of `p` is the integral of the
corresponding derivative of `φ_{s²}`. In particular

`∇p(y) = -(1/s²) ∫ φ_{s²}(y - c • x) (y - c • x) dμ₀(x)`.

The score of the law of `Y` is `∇ log p = ∇p / p`. It is the object of Tweedie's formula and of
denoising score matching, which express it as a conditional expectation of the noise given `Y`.

## Main definitions

* `TauCeti.Probability.smoothedDensity μ₀ c s`: the density `p` above.
* `TauCeti.Probability.noisyScore μ₀ c s`: its score `∇ log p`.

## Main results

* `TauCeti.Probability.bind_multivariateGaussian_eq_withDensity_smoothedDensity`: mixing the
  Gaussian laws `N(c • x, s² • 1)` over `x ∼ μ₀` gives Lebesgue measure weighted by `p`.
* `TauCeti.Probability.hasLaw_smoothedDensity`: `Y = c • X + s • Z` has density `p`.
* `TauCeti.Probability.smoothedDensity_pos` and `TauCeti.Probability.contDiff_smoothedDensity`:
  `p` is positive and `C^∞`.
* `TauCeti.Probability.iteratedFDeriv_smoothedDensity`: every derivative of `p` is taken under
  the integral sign.
* `TauCeti.Probability.hasGradientAt_smoothedDensity`: the gradient formula for `p`.
* `TauCeti.Probability.noisyScore_eq_inv_smul_gradient` and
  `TauCeti.Probability.noisyScore_eq_integral`: the score is `∇p / p`, explicitly
  `-(1/s²) p(y)⁻¹ ∫ φ_{s²}(y - c • x) (y - c • x) dμ₀(x)`.
* `TauCeti.Probability.smoothedDensity_dirac` and `TauCeti.Probability.noisyScore_dirac`: for a
  point mass `μ₀ = δ_{x₀}`, `p = φ_{s²}(· - c • x₀)` and the score is `-(y - c • x₀) / s²`.

## References

* B. Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. **106** (2011),
  1602–1614, equation (1.3).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The density of `c • X + s • Z`, for `X` with law `μ₀` and an independent standard Gaussian
vector `Z`: the convolution `y ↦ ∫ φ_{s²}(y - c • x) dμ₀(x)` of the image of `μ₀` under `c • ·`
with the density `φ_{s²}` of `N(0, s² • 1)`. It is a density of the law of `c • X + s • Z` when
`μ₀` is a finite measure and `s ≠ 0` (`TauCeti.Probability.hasLaw_smoothedDensity`). -/
def smoothedDensity (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ) (y : EuclideanSpace ℝ ι) : ℝ :=
  ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) ∂μ₀

/-- The score `∇ log p` of the smoothed density `p = smoothedDensity μ₀ c s`, that is, of the law
of `c • X + s • Z`. -/
def noisyScore (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  gradient (fun y ↦ Real.log (smoothedDensity μ₀ c s y)) y

variable {μ₀ : Measure (EuclideanSpace ℝ ι)} {c s : ℝ}

/-- The defining formula of the smoothed density. -/
theorem smoothedDensity_apply (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ)
    (y : EuclideanSpace ℝ ι) :
    smoothedDensity μ₀ c s y = ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) ∂μ₀ :=
  (rfl)

/-- The defining formula of the score. -/
theorem noisyScore_apply (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    noisyScore μ₀ c s y = gradient (fun y ↦ Real.log (smoothedDensity μ₀ c s y)) y :=
  (rfl)

/-! ### The Gaussian kernel -/

section Kernel

open scoped ContDiff

/-- For `s ≠ 0` the density of `N(0, s² • 1)` is the heat kernel at time `s² / 2`. -/
private theorem pdf_eq_heatKernel (hs : s ≠ 0) :
    multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1) = heatKernel (s ^ 2 / 2) := by
  funext z
  rw [multivariateGaussianPDFReal_smul_one (by positivity), sub_zero]

private theorem pdf_pos (hs : s ≠ 0) (z : EuclideanSpace ℝ ι) :
    0 < multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1) z := by
  rw [pdf_eq_heatKernel hs]
  exact heatKernel_pos (by positivity) z

private theorem contDiff_pdf (hs : s ≠ 0) :
    ContDiff ℝ ∞ (multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1)) := by
  rw [pdf_eq_heatKernel hs]
  exact contDiff_heatKernel _

/-- Every derivative of the Gaussian density is bounded. -/
private theorem exists_norm_iteratedFDeriv_pdf_le (hs : s ≠ 0) (k : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ k
      (multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1)) z‖ ≤ C := by
  have ht : 0 < s ^ 2 / 2 := by positivity
  obtain ⟨C, hC₀, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le
    (E := EuclideanSpace ℝ ι) ht k
  refine ⟨C * (4 * π * (2 * (s ^ 2 / 2))) ^ (-(Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / 2),
    fun z ↦ ?_⟩
  rw [pdf_eq_heatKernel hs]
  exact (hC z).trans (mul_le_mul_of_nonneg_left (heatKernel_le (by positivity) z) hC₀.le)

private theorem measurable_pdf_sub_smul (y : EuclideanSpace ℝ ι) :
    Measurable fun x : EuclideanSpace ℝ ι ↦
      multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1) (y - c • x) :=
  (measurable_multivariateGaussianPDFReal _ _).comp (by fun_prop)

/-- Against a finite measure the integrand of the smoothed density is integrable. -/
private theorem integrable_pdf_sub_smul [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x)) μ₀ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_pdf_le (ι := ι) hs 0
  refine Integrable.of_bound (C := C) (measurable_pdf_sub_smul y).aestronglyMeasurable
    (.of_forall fun x ↦ ?_)
  simpa using hC (y - c • x)

end Kernel

/-! ### The density of the noisy observation -/

/-- For `s ≠ 0`, the smoothed density is the integral of the heat kernel at time `s² / 2`. -/
theorem smoothedDensity_eq_integral_heatKernel (hs : s ≠ 0) (y : EuclideanSpace ℝ ι) :
    smoothedDensity μ₀ c s y = ∫ x, heatKernel (s ^ 2 / 2) (y - c • x) ∂μ₀ := by
  rw [smoothedDensity_apply, pdf_eq_heatKernel hs]

/-- The smoothed density is nonnegative. -/
theorem smoothedDensity_nonneg (μ₀ : Measure (EuclideanSpace ℝ ι)) (c s : ℝ)
    (y : EuclideanSpace ℝ ι) : 0 ≤ smoothedDensity μ₀ c s y :=
  integral_nonneg fun _ ↦ multivariateGaussianPDFReal_nonneg _ _ _

/-- The smoothed density of a nonzero finite measure is positive. -/
theorem smoothedDensity_pos [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) : 0 < smoothedDensity μ₀ c s y := by
  rw [smoothedDensity_apply, integral_pos_iff_support_of_nonneg
    (fun _ ↦ multivariateGaussianPDFReal_nonneg _ _ _) (integrable_pdf_sub_smul hs y),
    Function.support_eq_univ fun _ ↦ (pdf_pos hs _).ne']
  exact Measure.measure_univ_pos.2 (NeZero.ne μ₀)

/-- **Gaussian smoothing of a finite measure has a density.** Mixing the isotropic Gaussian laws
`N(c • x, s² • 1)` over `x ∼ μ₀` gives Lebesgue measure weighted by the smoothed density. -/
theorem bind_multivariateGaussian_eq_withDensity_smoothedDensity [IsFiniteMeasure μ₀]
    (hs : s ≠ 0) :
    μ₀.bind (fun x ↦ multivariateGaussian (c • x) (s ^ 2 • 1)) =
      volume.withDensity fun y ↦ ENNReal.ofReal (smoothedDensity μ₀ c s y) := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hdens (x : EuclideanSpace ℝ ι) : multivariateGaussian (c • x) (s ^ 2 • 1) =
      volume.withDensity fun y ↦
        ENNReal.ofReal (multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x)) := by
    rw [multivariateGaussian_smul_one_eq_withDensity_heatKernel hs2, pdf_eq_heatKernel hs]
  simp_rw [hdens]
  rw [Measure.bind_withDensity μ₀ volume
    ((measurable_multivariateGaussianPDFReal _ _).comp (by fun_prop)).ennreal_ofReal.aemeasurable]
  congr 1
  funext y
  rw [smoothedDensity_apply, ofReal_integral_eq_lintegral_ofReal (integrable_pdf_sub_smul hs y)
    (.of_forall fun x ↦ multivariateGaussianPDFReal_nonneg _ _ _)]

/-- **The density of a Gaussian observation.** If `X` has a finite law `μ₀` and `Z` is a standard
Gaussian vector independent of `X`, then for `s ≠ 0` the observation `c • X + s • Z` has the
density `smoothedDensity μ₀ c s`. No moment assumption on `μ₀` is needed. -/
theorem hasLaw_smoothedDensity [IsFiniteMeasure μ₀] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Z : Ω → EuclideanSpace ℝ ι} (hX : HasLaw X μ₀ P)
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ ι)) P) (hXZ : X ⟂ᵢ[P] Z) (hs : s ≠ 0) :
    HasLaw (fun ω ↦ c • X ω + s • Z ω)
      (volume.withDensity fun y ↦ ENNReal.ofReal (smoothedDensity μ₀ c s y)) P := by
  have hcX : HasLaw (fun ω ↦ c • X ω) (μ₀.map (c • ·)) P :=
    (hasLaw_map (by fun_prop)).comp hX
  have hsZ : HasLaw (fun ω ↦ s • Z ω) (multivariateGaussian 0 (s ^ 2 • 1)) P := by
    have h :=
      EuclideanSpace.multivariateGaussian_sq_smul_one_eq_map_stdGaussian (0 : EuclideanSpace ℝ ι) s
    simp only [zero_add] at h
    rw [h]
    exact (hasLaw_map (by fun_prop)).comp hZ
  have hind : (fun ω ↦ c • X ω) ⟂ᵢ[P] (fun ω ↦ s • Z ω) :=
    hXZ.comp (measurable_const_smul c) (measurable_const_smul s)
  have htrans (x : EuclideanSpace ℝ ι) :
      (multivariateGaussian 0 (s ^ 2 • 1)).map (c • x + ·) =
        multivariateGaussian (c • x) (s ^ 2 • 1) := by
    simpa using map_add_smul_multivariateGaussian 0 (Matrix.PosSemidef.one.smul (sq_nonneg s))
      (c • x) 1
  have hlaw := hind.hasLaw_fun_add hcX hsZ
  rwa [← Measure.bind_map_add_eq_conv _ _ (measurable_const_smul c), funext htrans,
    bind_multivariateGaussian_eq_withDensity_smoothedDensity hs] at hlaw

/-! ### Smoothness and the gradient -/

section Smoothness

open scoped ContDiff

/-- The smoothed density has a Taylor series of every order whose terms are the integrals of the
derivatives of the Gaussian kernel. -/
private theorem exists_hasFTaylorSeriesUpTo_smoothedDensity [IsFiniteMeasure μ₀] (hs : s ≠ 0) :
    ∃ p, HasFTaylorSeriesUpTo ∞ (smoothedDensity μ₀ c s) p ∧ ∀ y (k : ℕ), p y k =
      ∫ x, iteratedFDeriv ℝ k (multivariateGaussianPDFReal 0 (s ^ 2 • 1)) (y - c • x) ∂μ₀ := by
  have hφ := contDiff_pdf (ι := ι) hs
  have hshift (x : EuclideanSpace ℝ ι) :
      ContDiff ℝ ∞ fun y ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) :=
    hφ.comp (contDiff_id.sub contDiff_const)
  choose C hC using exists_norm_iteratedFDeriv_pdf_le (ι := ι) hs
  have h := hasFTaylorSeriesUpToOn_integral_of_le_bound (μ := μ₀) (n := ∞)
    (F := fun y x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x))
    (p := fun y x ↦ ftaylorSeries ℝ
      (fun z ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (z - c • x)) y)
    (bound := fun k _ ↦ C k) isOpen_univ (fun y _ k _ ↦ ?_) (.of_forall fun x y _ k _ ↦ ?_)
    (fun k _ ↦ integrable_const _)
    (.of_forall fun x ↦ hasFTaylorSeriesUpToOn_univ_iff.2 (hshift x).ftaylorSeries)
  · refine ⟨_, hasFTaylorSeriesUpToOn_univ_iff.1 h, fun y k ↦ ?_⟩
    simp only [ftaylorSeries, iteratedFDeriv_comp_sub]
  · simp only [ftaylorSeries, iteratedFDeriv_comp_sub]
    exact ((hφ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (by fun_prop)).aestronglyMeasurable
  · simp only [ftaylorSeries, iteratedFDeriv_comp_sub]
    exact hC k _

/-- **The smoothed density is smooth.** -/
theorem contDiff_smoothedDensity [IsFiniteMeasure μ₀] (hs : s ≠ 0) :
    ContDiff ℝ ∞ (smoothedDensity μ₀ c s) :=
  (exists_hasFTaylorSeriesUpTo_smoothedDensity hs).choose_spec.1.contDiff

/-- **Every derivative of the smoothed density is taken under the integral sign:**
`D^k p(y) = ∫ D^k φ_{s²}(y - c • x) dμ₀(x)`. -/
theorem iteratedFDeriv_smoothedDensity [IsFiniteMeasure μ₀] (hs : s ≠ 0) (k : ℕ)
    (y : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ k (smoothedDensity μ₀ c s) y =
      ∫ x, iteratedFDeriv ℝ k (multivariateGaussianPDFReal 0 (s ^ 2 • 1)) (y - c • x) ∂μ₀ := by
  obtain ⟨p, hp, hpk⟩ := exists_hasFTaylorSeriesUpTo_smoothedDensity (μ₀ := μ₀) (c := c) hs
  rw [← hp.eq_iteratedFDeriv (by exact_mod_cast le_top) y, hpk]

/-- **The gradient of the smoothed density:**
`∇p(y) = -(1/s²) ∫ φ_{s²}(y - c • x) (y - c • x) dμ₀(x)`. -/
theorem hasGradientAt_smoothedDensity [IsFiniteMeasure μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    HasGradientAt (smoothedDensity μ₀ c s)
      (-(s ^ 2)⁻¹ • ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀)
      y := by
  have hs2 : 0 < s ^ 2 := by positivity
  set φ := multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1)
  -- The gradient of `φ` at `z` is `g z = -(1/s²) φ(z) z`.
  set g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun z ↦ -(s ^ 2)⁻¹ • φ z • z
  have hg (z : EuclideanSpace ℝ ι) : HasGradientAt φ (g z) z := by
    simpa [g] using hasGradientAt_multivariateGaussianPDFReal_smul_one hs2 0 z
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_pdf_le (ι := ι) hs 1
  have hgC (z : EuclideanSpace ℝ ι) : ‖toDual ℝ _ (g z)‖ ≤ C := by
    rw [← (hg z).hasFDerivAt.fderiv, ← norm_iteratedFDeriv_one]
    exact hC z
  have hgcont : Continuous g := by
    have : Continuous φ := (contDiff_pdf (ι := ι) hs).continuous
    fun_prop
  have hderiv : HasFDerivAt (smoothedDensity μ₀ c s)
      (∫ x, toDual ℝ _ (g (y - c • x)) ∂μ₀) y := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ C)
      (F' := fun y x ↦ toDual ℝ _ (g (y - c • x))) Filter.univ_mem
      (.of_forall fun y ↦ (measurable_pdf_sub_smul y).aestronglyMeasurable)
      (integrable_pdf_sub_smul hs y) ?_ (.of_forall fun x y _ ↦ hgC _) (integrable_const C)
      (.of_forall fun x y _ ↦ ?_)
    · exact ((toDual ℝ _).continuous.comp (hgcont.comp (by fun_prop))).aestronglyMeasurable
    · exact (hg (y - c • x)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const (c • x))
        |>.congr_fderiv (by ext; simp)
  have hcomm : ∫ x, toDual ℝ _ (g (y - c • x)) ∂μ₀ = toDual ℝ _ (∫ x, g (y - c • x) ∂μ₀) :=
    (toDual ℝ (EuclideanSpace ℝ ι)).toContinuousLinearEquiv.integral_comp_comm _
  rw [hcomm] at hderiv
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hderiv using 2
  simp only [g]
  rw [integral_smul]

/-- The gradient of the smoothed density, as a value. -/
theorem gradient_smoothedDensity [IsFiniteMeasure μ₀] (hs : s ≠ 0) (y : EuclideanSpace ℝ ι) :
    gradient (smoothedDensity μ₀ c s) y =
      -(s ^ 2)⁻¹ • ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀ :=
  (hasGradientAt_smoothedDensity hs y).gradient

end Smoothness

/-! ### The score -/

/-- For a nonzero finite measure, `log p` has gradient `∇p / p` at every point. -/
theorem hasGradientAt_log_smoothedDensity [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    HasGradientAt (fun y ↦ Real.log (smoothedDensity μ₀ c s y))
      ((smoothedDensity μ₀ c s y)⁻¹ • gradient (smoothedDensity μ₀ c s) y) y := by
  have h := ((hasGradientAt_smoothedDensity (μ₀ := μ₀) (c := c) hs y).hasFDerivAt.log
    (smoothedDensity_pos hs y).ne')
  rw [hasGradientAt_iff_hasFDerivAt, map_smul, (hasGradientAt_smoothedDensity hs y).gradient]
  exact h

/-- **The score is `∇p / p`.** -/
theorem noisyScore_eq_inv_smul_gradient [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    noisyScore μ₀ c s y = (smoothedDensity μ₀ c s y)⁻¹ • gradient (smoothedDensity μ₀ c s) y :=
  (hasGradientAt_log_smoothedDensity hs y).gradient

/-- **The score, explicitly:**
`∇ log p(y) = -(1/s²) p(y)⁻¹ ∫ φ_{s²}(y - c • x) (y - c • x) dμ₀(x)`. -/
theorem noisyScore_eq_integral [IsFiniteMeasure μ₀] [NeZero μ₀] (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    noisyScore μ₀ c s y = -(s ^ 2)⁻¹ • (smoothedDensity μ₀ c s y)⁻¹ •
      ∫ x, multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) • (y - c • x) ∂μ₀ := by
  rw [noisyScore_eq_inv_smul_gradient hs, gradient_smoothedDensity hs, smul_comm]

/-! ### A point mass -/

/-- For a point mass the smoothed density is the translated Gaussian density. -/
@[simp]
theorem smoothedDensity_dirac (x₀ : EuclideanSpace ℝ ι) (c s : ℝ) (y : EuclideanSpace ℝ ι) :
    smoothedDensity (Measure.dirac x₀) c s y =
      multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x₀) := by
  rw [smoothedDensity_apply, integral_dirac]

/-- For a point mass `δ_{x₀}` the score is that of `N(c • x₀, s² • 1)`: `-(y - c • x₀) / s²`. -/
theorem noisyScore_dirac (x₀ : EuclideanSpace ℝ ι) (hs : s ≠ 0) (y : EuclideanSpace ℝ ι) :
    noisyScore (Measure.dirac x₀) c s y = -(s ^ 2)⁻¹ • (y - c • x₀) := by
  rw [noisyScore_eq_integral hs, integral_dirac, smoothedDensity_dirac, smul_smul (_ : ℝ)⁻¹,
    inv_mul_cancel₀ (pdf_pos hs _).ne', one_smul]

end TauCeti.Probability
