/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Probability.Distributions.Categorical
public import TauCeti.Probability.Density
import TauCeti.Algebra.BigOperators.Finset.WeightedVariance
import TauCeti.Probability.Distributions.Mixture
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# Finite mixtures of real Gaussian laws

A scalar Gaussian mixture with simplex weights `p`, means `m` and variances `v` is the finite
weighted sum `∑ i, pᵢ • N(mᵢ, vᵢ)`. Every parameter value gives a probability measure; a
component of variance zero is the Dirac mass at its mean.

This file provides the construction and its categorical-mixture presentation, the decomposition
into the atoms of the zero-variance components and the weighted Gaussian density of the others,
the density and Radon--Nikodym interfaces, parameter measurability, finite-mixture integration,
the transforms, and the mean and variance. The exponential-integrability domain is all of `ℝ`,
the mgf is `∑ i, pᵢ * exp (mᵢ t + vᵢ t² / 2)`, and the variance is the law of total variance
`∑ i, pᵢ * (vᵢ + (mᵢ - mMean)²)` with `mMean = ∑ i, pᵢ * mᵢ`.

## References

* G. McLachlan and D. Peel, *Finite Mixture Models*, Wiley (2000), Chapter 1.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]
variable {p : StdSimplex ℝ≥0 ι} {m : ι → ℝ} {v : ι → ℝ≥0}

/-- The finite mixture of the real Gaussian laws `N(m i, v i)` with weights `p`. -/
def gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) : Measure ℝ :=
  ∑ i, (p.weights i : ℝ≥0∞) • gaussianReal (m i) (v i)

/-- The Gaussian mixture as its defining weighted sum of Gaussian laws. -/
theorem gaussianMixtureMeasure_def (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) :
    gaussianMixtureMeasure p m v = ∑ i, (p.weights i : ℝ≥0∞) • gaussianReal (m i) (v i) :=
  (rfl)

/-- Every Gaussian mixture is a probability measure, including zero-variance components. -/
instance isProbabilityMeasure_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ)
    (v : ι → ℝ≥0) : IsProbabilityMeasure (gaussianMixtureMeasure p m v) := by
  constructor
  simp only [gaussianMixtureMeasure_def, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact_mod_cast p.total_of_fintype

/-- The Gaussian mixture is the categorical mixture of its Gaussian components. -/
theorem gaussianMixtureMeasure_eq_bind [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) :
    gaussianMixtureMeasure p m v =
      (categoricalMeasure p).bind fun i ↦ gaussianReal (m i) (v i) := by
  ext s hs
  rw [gaussianMixtureMeasure_def, Measure.finsetSum_apply,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_fintype]
  simp only [categoricalMeasure_singleton, Measure.smul_apply, smul_eq_mul, mul_comm]

/-- A mixture of identical Gaussian components is that Gaussian law. -/
@[simp]
theorem gaussianMixtureMeasure_const (p : StdSimplex ℝ≥0 ι) (μ : ℝ) (σ2 : ℝ≥0) :
    gaussianMixtureMeasure p (fun _ ↦ μ) (fun _ ↦ σ2) = gaussianReal μ σ2 := by
  rw [gaussianMixtureMeasure_def, ← Finset.sum_smul]
  have hw : ∑ i, (p.weights i : ℝ≥0∞) = 1 := by exact_mod_cast p.total_of_fintype
  rw [hw, one_smul]

/-- Changing the parameters of zero-weight components leaves the mixture unchanged. -/
theorem gaussianMixtureMeasure_congr {m' : ι → ℝ} {v' : ι → ℝ≥0}
    (h : ∀ i, 0 < p.weights i → m i = m' i ∧ v i = v' i) :
    gaussianMixtureMeasure p m v = gaussianMixtureMeasure p m' v' := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : p.weights i = 0
  · simp [hi]
  · obtain ⟨hm, hv⟩ := h i (pos_iff_ne_zero.mpr hi)
    rw [hm, hv]

/-- Gaussian mixtures are measurable in their weights, means, and variances. -/
@[fun_prop]
theorem measurable_gaussianMixtureMeasure :
    Measurable fun z : StdSimplex ℝ≥0 ι × (ι → ℝ) × (ι → ℝ≥0) ↦
      gaussianMixtureMeasure z.1 z.2.1 z.2.2 := by
  have hw (i : ι) : Measurable fun p : StdSimplex ℝ≥0 ι ↦ p.weights i :=
    (measurable_pi_apply i).comp StdSimplex.measurable_toFun_comp_weights
  simp only [gaussianMixtureMeasure_def]
  refine Finset.measurable_sum _ fun i _ ↦ Measure.measurable_measure.mpr fun s hs ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  have hg : Measurable fun z : StdSimplex ℝ≥0 ι × (ι → ℝ) × (ι → ℝ≥0) ↦
      gaussianReal (z.2.1 i) (z.2.2 i) :=
    measurable_gaussianReal.comp
      (f := fun z : StdSimplex ℝ≥0 ι × (ι → ℝ) × (ι → ℝ≥0) ↦ (z.2.1 i, z.2.2 i)) (by fun_prop)
  exact (measurable_coe_nnreal_ennreal.comp ((hw i).comp measurable_fst)).mul
    ((Measure.measurable_coe hs).comp hg)

/-! ### Densities -/

/-- The real density of the continuous part of a Gaussian mixture: the weighted sum of the
Gaussian densities. Zero-variance components contribute nothing, since `gaussianPDFReal m 0`
vanishes. -/
def gaussianMixturePDFReal (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) (x : ℝ) : ℝ :=
  ∑ i, (p.weights i : ℝ) * gaussianPDFReal (m i) (v i) x

/-- The extended nonnegative density of the continuous part of a Gaussian mixture. -/
def gaussianMixturePDF (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianMixturePDFReal p m v x)

/-- The real mixture density as its defining weighted sum. -/
theorem gaussianMixturePDFReal_def (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) (x : ℝ) :
    gaussianMixturePDFReal p m v x = ∑ i, (p.weights i : ℝ) * gaussianPDFReal (m i) (v i) x :=
  (rfl)

/-- The extended density is the nonnegative coercion of the real density. -/
theorem gaussianMixturePDF_eq_ofReal (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0)
    (x : ℝ) : gaussianMixturePDF p m v x = ENNReal.ofReal (gaussianMixturePDFReal p m v x) :=
  (rfl)

/-- The real mixture density is nonnegative. -/
theorem gaussianMixturePDFReal_nonneg (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0)
    (x : ℝ) : 0 ≤ gaussianMixturePDFReal p m v x :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (NNReal.coe_nonneg _) (gaussianPDFReal_nonneg _ _ _)

/-- Coercing the extended density back to the reals recovers the real density. -/
@[simp]
theorem toReal_gaussianMixturePDF (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) (x : ℝ) :
    (gaussianMixturePDF p m v x).toReal = gaussianMixturePDFReal p m v x :=
  ENNReal.toReal_ofReal (gaussianMixturePDFReal_nonneg p m v x)

/-- The extended mixture density is the weighted sum of the extended Gaussian densities. -/
theorem gaussianMixturePDF_eq_sum (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) (x : ℝ) :
    gaussianMixturePDF p m v x = ∑ i, (p.weights i : ℝ≥0∞) * gaussianPDF (m i) (v i) x := by
  rw [gaussianMixturePDF_eq_ofReal, gaussianMixturePDFReal_def,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦
      mul_nonneg (NNReal.coe_nonneg _) (gaussianPDFReal_nonneg _ _ _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, gaussianPDF]

/-- The mixture density is positive everywhere as soon as one positive-weight component has
nonzero variance. -/
theorem gaussianMixturePDFReal_pos (h : ∃ i, 0 < p.weights i ∧ v i ≠ 0) (x : ℝ) :
    0 < gaussianMixturePDFReal p m v x := by
  obtain ⟨i, hi, hvi⟩ := h
  exact Finset.sum_pos'
    (fun j _ ↦ mul_nonneg (NNReal.coe_nonneg _) (gaussianPDFReal_nonneg _ _ _))
    ⟨i, Finset.mem_univ i, mul_pos (NNReal.coe_pos.mpr hi) (gaussianPDFReal_pos _ _ _ hvi)⟩

/-- The real mixture density is measurable. -/
@[fun_prop]
theorem measurable_gaussianMixturePDFReal (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) :
    Measurable (gaussianMixturePDFReal p m v) := by
  rw [funext (gaussianMixturePDFReal_def p m v)]
  exact Finset.measurable_sum _ fun i _ ↦ (measurable_gaussianPDFReal _ _).const_mul _

/-- The extended mixture density is measurable. -/
@[fun_prop]
theorem measurable_gaussianMixturePDF (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) :
    Measurable (gaussianMixturePDF p m v) :=
  (measurable_gaussianMixturePDFReal p m v).ennreal_ofReal

/-- **Atomic and continuous decomposition.** A Gaussian mixture is the sum of the weighted
Dirac masses of its zero-variance components and of Lebesgue measure weighted by the mixture
density. -/
theorem gaussianMixtureMeasure_eq_sum_dirac_add_withDensity [DecidablePred fun i : ι ↦ v i = 0]
    (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) :
    gaussianMixtureMeasure p m v =
      (∑ i with v i = 0, (p.weights i : ℝ≥0∞) • Measure.dirac (m i)) +
        volume.withDensity (gaussianMixturePDF p m v) := by
  have hcomponent (i : ι) : gaussianReal (m i) (v i) =
      (if v i = 0 then Measure.dirac (m i) else 0) +
        volume.withDensity (gaussianPDF (m i) (v i)) := by
    by_cases hvi : v i = 0
    · simp [hvi, gaussianReal_zero_var, gaussianPDF_zero_var]
    · simp [hvi, gaussianReal_of_var_ne_zero _ hvi]
  have hdensity : volume.withDensity (gaussianMixturePDF p m v) =
      ∑ i, (p.weights i : ℝ≥0∞) • volume.withDensity (gaussianPDF (m i) (v i)) := by
    have hsum := withDensity_tsum (μ := (volume : Measure ℝ))
      (f := fun i x ↦ (p.weights i : ℝ≥0∞) * gaussianPDF (m i) (v i) x)
      (fun i ↦ measurable_const.mul (measurable_gaussianPDF _ _))
    simp only [tsum_fintype, Measure.sum_fintype] at hsum
    rw [funext (gaussianMixturePDF_eq_sum p m v), ← Finset.sum_fn, hsum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simpa only [Pi.smul_def, smul_eq_mul] using
      (withDensity_smul' (μ := (volume : Measure ℝ)) (p.weights i : ℝ≥0∞)
        (gaussianPDF (m i) (v i)) ENNReal.coe_ne_top)
  rw [hdensity, Finset.sum_filter, gaussianMixtureMeasure_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hcomponent i, smul_add]
  split_ifs <;> simp

/-- If every positive-weight component has nonzero variance, the mixture is Lebesgue measure
weighted by the mixture density. -/
theorem gaussianMixtureMeasure_eq_withDensity (hv : ∀ i, 0 < p.weights i → v i ≠ 0) :
    gaussianMixtureMeasure p m v = volume.withDensity (gaussianMixturePDF p m v) := by
  classical
  have hatoms : ∑ i with v i = 0, (p.weights i : ℝ≥0∞) • Measure.dirac (m i) = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    by_cases hwi : p.weights i = 0
    · simp [hwi]
    · exact absurd (Finset.mem_filter.mp hi).2 (hv i (pos_iff_ne_zero.mpr hwi))
  rw [gaussianMixtureMeasure_eq_sum_dirac_add_withDensity p m, hatoms, zero_add]

/-- The Radon--Nikodym derivative of a Gaussian mixture with respect to Lebesgue measure is the
mixture density, also when some components are Dirac masses. -/
theorem rnDeriv_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) :
    (gaussianMixtureMeasure p m v).rnDeriv volume =ᵐ[volume] gaussianMixturePDF p m v := by
  classical
  have (i : ι) : IsFiniteMeasure ((p.weights i : ℝ≥0∞) • Measure.dirac (m i)) :=
    ⟨by simp [ENNReal.coe_lt_top]⟩
  have hsingular : (∑ i with v i = 0, (p.weights i : ℝ≥0∞) • Measure.dirac (m i)) ⟂ₘ
      (volume : Measure ℝ) :=
    Finset.sum_induction _ (· ⟂ₘ (volume : Measure ℝ))
      (fun _ _ ↦ Measure.MutuallySingular.add_left) Measure.MutuallySingular.zero_left
      fun _ _ ↦ (mutuallySingular_dirac _ _).smul _
  have : SigmaFinite (volume.withDensity (gaussianMixturePDF p m v)) :=
    SigmaFinite.withDensity_of_ne_top' fun _ ↦ ENNReal.ofReal_ne_top
  rw [gaussianMixtureMeasure_eq_sum_dirac_add_withDensity p m, add_comm]
  filter_upwards [Measure.rnDeriv_add_of_mutuallySingular
      (volume.withDensity (gaussianMixturePDF p m v)) _ volume hsingular,
    Measure.rnDeriv_withDensity volume (measurable_gaussianMixturePDF p m v)] with x hx hx'
  rw [hx, hx']

/-- If every positive-weight component has nonzero variance, the mixture has no atoms. -/
theorem nullSingletonClass_gaussianMixtureMeasure (hv : ∀ i, 0 < p.weights i → v i ≠ 0) :
    NullSingletonClass (gaussianMixtureMeasure p m v) := by
  rw [gaussianMixtureMeasure_eq_withDensity hv]
  infer_instance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable whose law is a Gaussian mixture with nondegenerate positive-weight components has
a Lebesgue density. -/
theorem hasPDF_of_hasLaw_gaussianMixtureMeasure (hv : ∀ i, 0 < p.weights i → v i ≠ 0)
    (hX : HasLaw X (gaussianMixtureMeasure p m v) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_gaussianMixturePDF p m v).aemeasurable
    (by rwa [gaussianMixtureMeasure_eq_withDensity hv] at hX)

/-- The canonical pdf of such a variable agrees almost everywhere with the mixture density. -/
theorem pdf_eq_gaussianMixturePDF_of_hasLaw_gaussianMixtureMeasure
    (hv : ∀ i, 0 < p.weights i → v i ≠ 0) (hX : HasLaw X (gaussianMixtureMeasure p m v) P) :
    pdf X P volume =ᵐ[volume] gaussianMixturePDF p m v :=
  pdf_eq_of_hasLaw_withDensity (measurable_gaussianMixturePDF p m v).aemeasurable
    (by rwa [gaussianMixtureMeasure_eq_withDensity hv] at hX)

/-! ### Integration, transforms, and moments -/

section Integration

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}

/-- Integrability under a Gaussian mixture is integrability under every positive-weight
component. -/
theorem integrable_gaussianMixtureMeasure_iff :
    Integrable f (gaussianMixtureMeasure p m v) ↔
      ∀ i, 0 < p.weights i → Integrable f (gaussianReal (m i) (v i)) := by
  rw [gaussianMixtureMeasure_def, integrable_finsetSum_measure]
  simp only [Finset.mem_univ, forall_const]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : p.weights i = 0
  · simp [hi]
  · rw [integrable_smul_measure (by simpa using hi) ENNReal.coe_ne_top]
    exact ⟨fun h _ ↦ h, fun h ↦ h (pos_iff_ne_zero.mpr hi)⟩

variable [NormedSpace ℝ E]

/-- The expectation of an integrable observable is the weighted sum of its component
expectations. -/
theorem integral_gaussianMixtureMeasure (hf : Integrable f (gaussianMixtureMeasure p m v)) :
    ∫ x, f x ∂gaussianMixtureMeasure p m v =
      ∑ i, (p.weights i : ℝ) • ∫ x, f x ∂gaussianReal (m i) (v i) := by
  rw [gaussianMixtureMeasure_def] at hf ⊢
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hf)]
  simp only [integral_smul_measure, ENNReal.coe_toReal]

end Integration

/-- Every exponential moment of a Gaussian mixture is finite. -/
@[simp]
theorem integrableExpSet_id_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ)
    (v : ι → ℝ≥0) : integrableExpSet id (gaussianMixtureMeasure p m v) = univ := by
  ext t
  simp only [mem_univ, iff_true]
  exact integrable_gaussianMixtureMeasure_iff.mpr fun i _ ↦ integrable_exp_mul_gaussianReal t

/-- The mgf of a Gaussian mixture is the weighted sum of the Gaussian mgfs. -/
@[simp]
theorem mgf_id_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0)
    (t : ℝ) : mgf id (gaussianMixtureMeasure p m v) t =
      ∑ i, (p.weights i : ℝ) * exp (m i * t + v i * t ^ 2 / 2) := by
  have hf : Integrable (fun x ↦ exp (t * x)) (gaussianMixtureMeasure p m v) :=
    integrable_gaussianMixtureMeasure_iff.mpr fun i _ ↦ integrable_exp_mul_gaussianReal t
  rw [mgf, integral_gaussianMixtureMeasure (by simpa using hf)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_eq_mul, ← mgf, mgf_id_gaussianReal]

/-- The cgf of a Gaussian mixture is the logarithm of the weighted sum of the Gaussian mgfs. -/
@[simp]
theorem cgf_id_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0)
    (t : ℝ) : cgf id (gaussianMixtureMeasure p m v) t =
      log (∑ i, (p.weights i : ℝ) * exp (m i * t + v i * t ^ 2 / 2)) := by
  rw [cgf, mgf_id_gaussianMixtureMeasure]

/-- The characteristic function of a Gaussian mixture is the weighted sum of the Gaussian
characteristic functions. -/
@[simp]
theorem charFun_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0)
    (t : ℝ) : charFun (gaussianMixtureMeasure p m v) t =
      ∑ i, (p.weights i : ℂ) * Complex.exp (t * m i * Complex.I - v i * t ^ 2 / 2) := by
  let _ : MeasurableSpace ι := ⊤
  let _ : IsProbabilityMeasure
      ((categoricalMeasure p).bind fun i ↦ gaussianReal (m i) (v i)) := by
    rw [← gaussianMixtureMeasure_eq_bind]
    infer_instance
  rw [gaussianMixtureMeasure_eq_bind, Measure.charFun_bind _
    Measurable.of_discrete.aemeasurable, integral_categoricalMeasure]
  simp [charFun_gaussianReal, Complex.real_smul]

/-- Every natural power is integrable under a Gaussian mixture. -/
@[simp]
theorem integrable_pow_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0)
    (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n) (gaussianMixtureMeasure p m v) :=
  integrable_gaussianMixtureMeasure_iff.mpr fun _ _ ↦ TauCeti.integrable_pow_gaussianReal _ _ n

/-- The mean of a Gaussian mixture is the weighted mean of the component means. -/
@[simp]
theorem integral_id_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) :
    ∫ x, x ∂gaussianMixtureMeasure p m v = ∑ i, (p.weights i : ℝ) * m i := by
  rw [integral_gaussianMixtureMeasure
    (by simpa using integrable_pow_gaussianMixtureMeasure p m v 1)]
  simp [integral_id_gaussianReal]

/-- The second moment of a Gaussian mixture is the weighted sum of the component second
moments. -/
theorem integral_sq_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) :
    ∫ x, x ^ 2 ∂gaussianMixtureMeasure p m v = ∑ i, (p.weights i : ℝ) * (v i + m i ^ 2) := by
  rw [integral_gaussianMixtureMeasure (integrable_pow_gaussianMixtureMeasure p m v 2)]
  simp [integral_sq_gaussianReal]

/-- **Law of total variance** for a Gaussian mixture: the weighted component variance plus the
weighted spread of the component means about the overall mean. -/
theorem variance_id_gaussianMixtureMeasure (p : StdSimplex ℝ≥0 ι) (m : ι → ℝ) (v : ι → ℝ≥0) :
    Var[id; gaussianMixtureMeasure p m v] =
      ∑ i, (p.weights i : ℝ) * (v i + (m i - ∑ j, (p.weights j : ℝ) * m j) ^ 2) := by
  have hmem : MemLp id 2 (gaussianMixtureMeasure p m v) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr
      (integrable_pow_gaussianMixtureMeasure p m v 2)
  have hw : ∑ i, (p.weights i : ℝ) = 1 := by exact_mod_cast p.total_of_fintype
  rw [variance_eq_sub hmem]
  simp only [id_eq, Pi.pow_apply, integral_sq_gaussianMixtureMeasure,
    integral_id_gaussianMixtureMeasure]
  have h := Finset.sum_mul_sub_sq_eq Finset.univ hw 0 m
  simp only [zero_sub, neg_sq] at h
  simp only [mul_add, Finset.sum_add_distrib, h, sub_sq_comm (m _)]
  ring

/-- The mean of a random variable whose law is a Gaussian mixture. -/
theorem integral_of_hasLaw_gaussianMixtureMeasure
    (hX : HasLaw X (gaussianMixtureMeasure p m v) P) :
    ∫ ω, X ω ∂P = ∑ i, (p.weights i : ℝ) * m i := by
  rw [hX.integral_eq, integral_id_gaussianMixtureMeasure]

/-- The variance of a random variable whose law is a Gaussian mixture. -/
theorem variance_of_hasLaw_gaussianMixtureMeasure
    (hX : HasLaw X (gaussianMixtureMeasure p m v) P) :
    Var[X; P] = ∑ i, (p.weights i : ℝ) * (v i + (m i - ∑ j, (p.weights j : ℝ) * m j) ^ 2) := by
  rw [hX.variance_eq, variance_id_gaussianMixtureMeasure]

end TauCeti.Probability
