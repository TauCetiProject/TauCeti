/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Categorical
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Moments.Covariance
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Probability.Distributions.Gaussian.Transforms
import TauCeti.Probability.Distributions.Mixture

/-!
# Finite mixtures of multivariate Gaussian laws

A multivariate Gaussian mixture with simplex weights `p`, means `m` and covariance parameters `S`
is the finite weighted sum `∑ k, pₖ • N(mₖ, Sₖ)` on `EuclideanSpace ℝ ι`. Every parameter value
gives a probability measure.

The components with positive-definite covariance have Lebesgue densities, while every other
component is singular with respect to Lebesgue measure. The mixture density
`multivariateGaussianMixturePDFReal` is therefore the weighted sum of the densities of the
positive-definite components only. It is the Radon–Nikodym derivative of the mixture at every
parameter value, and when every positive-weight component is positive definite it is the
weighted sum of all component densities and the mixture is absolutely continuous.

The remaining results are the categorical-mixture presentation, parameter measurability,
finite-mixture integration, the moment-generating function of every linear observable (with
domain all of `ℝ`), the characteristic function, the mean `∑ k, pₖ • mₖ`, and the law of total
covariance `∑ k, pₖ • (Sₖ + (mₖ - m̄)(mₖ - m̄)ᵀ)` with `m̄` the mean.

## References

* G. McLachlan and D. Peel, *Finite Mixture Models*, Wiley (2000), Chapter 3.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix NNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
variable {p : StdSimplex ℝ≥0 κ} {m : κ → EuclideanSpace ℝ ι} {S : κ → Matrix ι ι ℝ}

/-- The finite mixture of the multivariate Gaussian laws `N(m k, S k)` with weights `p`. -/
def multivariateGaussianMixtureMeasure (p : StdSimplex ℝ≥0 κ) (m : κ → EuclideanSpace ℝ ι)
    (S : κ → Matrix ι ι ℝ) : Measure (EuclideanSpace ℝ ι) :=
  ∑ k, (p.weights k : ℝ≥0∞) • multivariateGaussian (m k) (S k)

/-- The multivariate Gaussian mixture as its defining weighted sum of Gaussian laws. -/
theorem multivariateGaussianMixtureMeasure_def (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    multivariateGaussianMixtureMeasure p m S =
      ∑ k, (p.weights k : ℝ≥0∞) • multivariateGaussian (m k) (S k) :=
  (rfl)

/-- Every multivariate Gaussian mixture is a probability measure. -/
instance isProbabilityMeasure_multivariateGaussianMixtureMeasure (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    IsProbabilityMeasure (multivariateGaussianMixtureMeasure p m S) := by
  constructor
  simp only [multivariateGaussianMixtureMeasure_def, Measure.finsetSum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact_mod_cast p.total_of_fintype

/-- The multivariate Gaussian mixture is the categorical mixture of its Gaussian components. -/
theorem multivariateGaussianMixtureMeasure_eq_bind [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (p : StdSimplex ℝ≥0 κ) (m : κ → EuclideanSpace ℝ ι)
    (S : κ → Matrix ι ι ℝ) :
    multivariateGaussianMixtureMeasure p m S =
      (categoricalMeasure p).bind fun k ↦ multivariateGaussian (m k) (S k) := by
  ext s hs
  rw [multivariateGaussianMixtureMeasure_def, Measure.finsetSum_apply,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_fintype]
  simp only [categoricalMeasure_singleton, Measure.smul_apply, smul_eq_mul, mul_comm]

/-- A mixture of identical multivariate Gaussian components is that Gaussian law. -/
@[simp]
theorem multivariateGaussianMixtureMeasure_const (p : StdSimplex ℝ≥0 κ)
    (μ : EuclideanSpace ℝ ι) (C : Matrix ι ι ℝ) :
    multivariateGaussianMixtureMeasure p (fun _ ↦ μ) (fun _ ↦ C) = multivariateGaussian μ C := by
  rw [multivariateGaussianMixtureMeasure_def, ← Finset.sum_smul]
  have hw : ∑ k, (p.weights k : ℝ≥0∞) = 1 := by exact_mod_cast p.total_of_fintype
  rw [hw, one_smul]

/-- Changing the parameters of zero-weight components leaves the mixture unchanged. -/
theorem multivariateGaussianMixtureMeasure_congr {m' : κ → EuclideanSpace ℝ ι}
    {S' : κ → Matrix ι ι ℝ} (h : ∀ k, 0 < p.weights k → m k = m' k ∧ S k = S' k) :
    multivariateGaussianMixtureMeasure p m S = multivariateGaussianMixtureMeasure p m' S' := by
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : p.weights k = 0
  · simp [hk]
  · obtain ⟨hm, hS⟩ := h k (pos_iff_ne_zero.mpr hk)
    rw [hm, hS]

/-- Multivariate Gaussian mixtures are measurable in their weights, means, and covariance
parameters. -/
@[fun_prop]
theorem measurable_multivariateGaussianMixtureMeasure :
    Measurable fun z : StdSimplex ℝ≥0 κ × (κ → EuclideanSpace ℝ ι) × (κ → Matrix ι ι ℝ) ↦
      multivariateGaussianMixtureMeasure z.1 z.2.1 z.2.2 := by
  have hw (k : κ) : Measurable fun p : StdSimplex ℝ≥0 κ ↦ p.weights k :=
    (measurable_pi_apply k).comp StdSimplex.measurable_toFun_comp_weights
  simp only [multivariateGaussianMixtureMeasure_def]
  refine Finset.measurable_sum _ fun k _ ↦ Measure.measurable_measure.mpr fun s hs ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  have hg : Measurable fun z : StdSimplex ℝ≥0 κ × (κ → EuclideanSpace ℝ ι) ×
      (κ → Matrix ι ι ℝ) ↦ multivariateGaussian (z.2.1 k) (z.2.2 k) :=
    measurable_multivariateGaussian.comp
      (f := fun z : StdSimplex ℝ≥0 κ × (κ → EuclideanSpace ℝ ι) × (κ → Matrix ι ι ℝ) ↦
        (z.2.1 k, z.2.2 k)) (by fun_prop)
  exact (measurable_coe_nnreal_ennreal.comp ((hw k).comp measurable_fst)).mul
    ((Measure.measurable_coe hs).comp hg)

/-! ### Densities -/

open Classical in
/-- The real density of the absolutely continuous part of a multivariate Gaussian mixture: the
weighted sum of the Gaussian densities of the components with positive-definite covariance. The
other components are singular with respect to Lebesgue measure and contribute nothing. -/
def multivariateGaussianMixturePDFReal (p : StdSimplex ℝ≥0 κ) (m : κ → EuclideanSpace ℝ ι)
    (S : κ → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ k with (S k).PosDef, (p.weights k : ℝ) * multivariateGaussianPDFReal (m k) (S k) x

open Classical in
/-- The mixture density as its defining weighted sum over the positive-definite components. -/
theorem multivariateGaussianMixturePDFReal_def (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    multivariateGaussianMixturePDFReal p m S x =
      ∑ k with (S k).PosDef, (p.weights k : ℝ) * multivariateGaussianPDFReal (m k) (S k) x :=
  (rfl)

/-- The extended nonnegative density of the absolutely continuous part of a multivariate
Gaussian mixture. -/
def multivariateGaussianMixturePDF (p : StdSimplex ℝ≥0 κ) (m : κ → EuclideanSpace ℝ ι)
    (S : κ → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal (multivariateGaussianMixturePDFReal p m S x)

/-- The `ℝ≥0∞`-valued mixture density is the `ENNReal.ofReal` lift of the real-valued one. -/
theorem multivariateGaussianMixturePDF_eq_ofReal (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    multivariateGaussianMixturePDF p m S x =
      ENNReal.ofReal (multivariateGaussianMixturePDFReal p m S x) :=
  (rfl)

/-- If every positive-weight component has positive-definite covariance, the mixture density is
the weighted sum of all component densities. -/
theorem multivariateGaussianMixturePDFReal_eq_sum (hS : ∀ k, 0 < p.weights k → (S k).PosDef)
    (x : EuclideanSpace ℝ ι) :
    multivariateGaussianMixturePDFReal p m S x =
      ∑ k, (p.weights k : ℝ) * multivariateGaussianPDFReal (m k) (S k) x := by
  classical
  rw [multivariateGaussianMixturePDFReal_def]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun k _ hk ↦ ?_
  have hw : p.weights k = 0 := by
    by_contra hw
    exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hS k (pos_iff_ne_zero.mpr hw)⟩)
  simp [hw]

/-- The real-valued mixture density is nonnegative. -/
theorem multivariateGaussianMixturePDFReal_nonneg (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    0 ≤ multivariateGaussianMixturePDFReal p m S x :=
  Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (NNReal.coe_nonneg _) (multivariateGaussianPDFReal_nonneg _ _ _)

/-- The `ℝ≥0∞`-valued mixture density carries the real-valued one back through
`ENNReal.toReal`. -/
@[simp]
theorem toReal_multivariateGaussianMixturePDF (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    (multivariateGaussianMixturePDF p m S x).toReal = multivariateGaussianMixturePDFReal p m S x :=
  ENNReal.toReal_ofReal (multivariateGaussianMixturePDFReal_nonneg p m S x)

/-- The mixture density is positive everywhere as soon as one positive-weight component has
positive-definite covariance. -/
theorem multivariateGaussianMixturePDFReal_pos (h : ∃ k, 0 < p.weights k ∧ (S k).PosDef)
    (x : EuclideanSpace ℝ ι) : 0 < multivariateGaussianMixturePDFReal p m S x := by
  classical
  obtain ⟨k, hwk, hSk⟩ := h
  rw [multivariateGaussianMixturePDFReal_def]
  exact Finset.sum_pos' (fun _ _ ↦ mul_nonneg (NNReal.coe_nonneg _)
      (multivariateGaussianPDFReal_nonneg _ _ _))
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hSk⟩,
      mul_pos (by exact_mod_cast hwk) (multivariateGaussianPDFReal_pos hSk.det_pos _ _)⟩

/-- The real-valued mixture density is measurable. -/
@[fun_prop]
theorem measurable_multivariateGaussianMixturePDFReal (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    Measurable (multivariateGaussianMixturePDFReal p m S) := by
  classical
  unfold multivariateGaussianMixturePDFReal
  fun_prop

/-- The `ℝ≥0∞`-valued mixture density is measurable. -/
@[fun_prop]
theorem measurable_multivariateGaussianMixturePDF (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    Measurable (multivariateGaussianMixturePDF p m S) :=
  (measurable_multivariateGaussianMixturePDFReal p m S).ennreal_ofReal

open Classical in
/-- **Lebesgue decomposition.** A multivariate Gaussian mixture is the sum of its weighted
components whose covariance is not positive definite, each singular with respect to Lebesgue
measure by `mutuallySingular_multivariateGaussian_volume`, and of Lebesgue measure weighted by the
mixture density. -/
theorem multivariateGaussianMixtureMeasure_eq_add_withDensity (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    multivariateGaussianMixtureMeasure p m S =
      (∑ k with ¬(S k).PosDef, (p.weights k : ℝ≥0∞) • multivariateGaussian (m k) (S k)) +
        volume.withDensity (multivariateGaussianMixturePDF p m S) := by
  have hdensity : volume.withDensity (multivariateGaussianMixturePDF p m S) =
      ∑ k with (S k).PosDef, (p.weights k : ℝ≥0∞) • multivariateGaussian (m k) (S k) := by
    have hpdf (x : EuclideanSpace ℝ ι) : multivariateGaussianMixturePDF p m S x = ∑ k,
        if (S k).PosDef then (p.weights k : ℝ≥0∞) * multivariateGaussianPDF (m k) (S k) x
        else 0 := by
      rw [← Finset.sum_filter, multivariateGaussianMixturePDF_eq_ofReal,
        multivariateGaussianMixturePDFReal_def, ENNReal.ofReal_sum_of_nonneg fun k _ ↦
          mul_nonneg (NNReal.coe_nonneg _) (multivariateGaussianPDFReal_nonneg _ _ _)]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
        multivariateGaussianPDF_def]
    have hsum := withDensity_tsum (μ := (volume : Measure (EuclideanSpace ℝ ι)))
      (f := fun k x ↦ if (S k).PosDef then
        (p.weights k : ℝ≥0∞) * multivariateGaussianPDF (m k) (S k) x else 0)
      fun k ↦ Measurable.ite (MeasurableSet.const _)
        (measurable_const.mul (measurable_multivariateGaussianPDF _ _)) measurable_const
    simp only [tsum_fintype, Measure.sum_fintype] at hsum
    rw [funext hpdf, ← Finset.sum_fn, hsum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    split_ifs with hk
    · rw [multivariateGaussian_eq_withDensity hk]
      exact withDensity_smul' (μ := (volume : Measure (EuclideanSpace ℝ ι)))
        (p.weights k : ℝ≥0∞) (multivariateGaussianPDF (m k) (S k)) ENNReal.coe_ne_top
    · exact withDensity_zero
  rw [hdensity, add_comm, Finset.sum_filter_add_sum_filter_not,
    multivariateGaussianMixtureMeasure_def]

/-- If every positive-weight component has positive-definite covariance, the mixture is Lebesgue
measure weighted by the mixture density. -/
theorem multivariateGaussianMixtureMeasure_eq_withDensity
    (hS : ∀ k, 0 < p.weights k → (S k).PosDef) :
    multivariateGaussianMixtureMeasure p m S =
      volume.withDensity (multivariateGaussianMixturePDF p m S) := by
  classical
  have hsingular : ∑ k with ¬(S k).PosDef,
      (p.weights k : ℝ≥0∞) • multivariateGaussian (m k) (S k) = 0 := by
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    by_cases hwk : p.weights k = 0
    · simp [hwk]
    · exact absurd (hS k (pos_iff_ne_zero.mpr hwk)) (Finset.mem_filter.mp hk).2
  rw [multivariateGaussianMixtureMeasure_eq_add_withDensity p m S, hsingular, zero_add]

/-- The Radon–Nikodym derivative of a multivariate Gaussian mixture with respect to Lebesgue
measure is the mixture density, also when some components are degenerate. -/
theorem rnDeriv_multivariateGaussianMixtureMeasure (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    (multivariateGaussianMixtureMeasure p m S).rnDeriv volume =ᵐ[volume]
      multivariateGaussianMixturePDF p m S := by
  classical
  have hsingular : (∑ k with ¬(S k).PosDef,
      (p.weights k : ℝ≥0∞) • multivariateGaussian (m k) (S k)) ⟂ₘ
        (volume : Measure (EuclideanSpace ℝ ι)) :=
    Finset.sum_induction _ (· ⟂ₘ (volume : Measure (EuclideanSpace ℝ ι)))
      (fun _ _ ↦ Measure.MutuallySingular.add_left) Measure.MutuallySingular.zero_left
      fun k hk ↦ (mutuallySingular_multivariateGaussian_volume
        (Finset.mem_filter.mp hk).2 (m k)).smul _
  have (k : κ) : IsFiniteMeasure
      ((p.weights k : ℝ≥0∞) • multivariateGaussian (m k) (S k)) :=
    ⟨by simp [ENNReal.coe_lt_top]⟩
  have : SigmaFinite (volume.withDensity (multivariateGaussianMixturePDF p m S)) :=
    SigmaFinite.withDensity_of_ne_top' fun _ ↦ ENNReal.ofReal_ne_top
  rw [multivariateGaussianMixtureMeasure_eq_add_withDensity p m S, add_comm]
  filter_upwards [Measure.rnDeriv_add_of_mutuallySingular
      (volume.withDensity (multivariateGaussianMixturePDF p m S)) _ volume hsingular,
    Measure.rnDeriv_withDensity volume (measurable_multivariateGaussianMixturePDF p m S)]
    with x hx hx'
  rw [hx, hx']

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}

/-- A random vector whose law is a multivariate Gaussian mixture with positive-definite
positive-weight components has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_multivariateGaussianMixtureMeasure
    (hS : ∀ k, 0 < p.weights k → (S k).PosDef)
    (hX : HasLaw X (multivariateGaussianMixtureMeasure p m S) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_multivariateGaussianMixturePDF p m S).aemeasurable
    (by rwa [multivariateGaussianMixtureMeasure_eq_withDensity hS] at hX)

/-- The canonical pdf of such a random vector agrees almost everywhere with the mixture
density. -/
theorem pdf_eq_multivariateGaussianMixturePDF_of_hasLaw_multivariateGaussianMixtureMeasure
    (hS : ∀ k, 0 < p.weights k → (S k).PosDef)
    (hX : HasLaw X (multivariateGaussianMixtureMeasure p m S) P) :
    pdf X P volume =ᵐ[volume] multivariateGaussianMixturePDF p m S :=
  pdf_eq_of_hasLaw_withDensity (measurable_multivariateGaussianMixturePDF p m S).aemeasurable
    (by rwa [multivariateGaussianMixtureMeasure_eq_withDensity hS] at hX)

/-! ### Integration and transforms -/

section Integration

variable {E : Type*} [NormedAddCommGroup E] {f : EuclideanSpace ℝ ι → E}

/-- Integrability under a multivariate Gaussian mixture is integrability under every
positive-weight component. -/
theorem integrable_multivariateGaussianMixtureMeasure_iff :
    Integrable f (multivariateGaussianMixtureMeasure p m S) ↔
      ∀ k, 0 < p.weights k → Integrable f (multivariateGaussian (m k) (S k)) := by
  rw [multivariateGaussianMixtureMeasure_def, integrable_finsetSum_measure]
  simp only [Finset.mem_univ, forall_const]
  refine forall_congr' fun k ↦ ?_
  by_cases hk : p.weights k = 0
  · simp [hk]
  · rw [integrable_smul_measure (by simpa using hk) ENNReal.coe_ne_top]
    exact ⟨fun h _ ↦ h, fun h ↦ h (pos_iff_ne_zero.mpr hk)⟩

variable [NormedSpace ℝ E]

/-- The expectation of an integrable observable is the weighted sum of its component
expectations. -/
theorem integral_multivariateGaussianMixtureMeasure
    (hf : Integrable f (multivariateGaussianMixtureMeasure p m S)) :
    ∫ x, f x ∂multivariateGaussianMixtureMeasure p m S =
      ∑ k, (p.weights k : ℝ) • ∫ x, f x ∂multivariateGaussian (m k) (S k) := by
  rw [multivariateGaussianMixtureMeasure_def] at hf ⊢
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hf)]
  simp only [integral_smul_measure, ENNReal.coe_toReal]

end Integration

/-- Every linear observable of a multivariate Gaussian mixture has finite exponential moments of
all real orders. -/
@[simp]
theorem integrableExpSet_inner_multivariateGaussianMixtureMeasure (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) (θ : EuclideanSpace ℝ ι) :
    integrableExpSet (fun x ↦ ⟪θ, x⟫) (multivariateGaussianMixtureMeasure p m S) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_multivariateGaussianMixtureMeasure_iff.mpr fun k _ ↦
    integrable_of_mem_integrableExpSet (by simp [integrableExpSet_inner_multivariateGaussian])

/-- The moment-generating function of a linear observable of a multivariate Gaussian mixture with
positive-semidefinite positive-weight components is the weighted sum of the Gaussian ones. -/
theorem mgf_inner_multivariateGaussianMixtureMeasure
    (hS : ∀ k, 0 < p.weights k → (S k).PosSemidef) (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    mgf (fun x ↦ ⟪θ, x⟫) (multivariateGaussianMixtureMeasure p m S) t =
      ∑ k, (p.weights k : ℝ) *
        Real.exp (t * ⟪θ, m k⟫ + t ^ 2 / 2 * ⟪θ, (S k).toEuclideanLin θ⟫) := by
  have hf : Integrable (fun x ↦ Real.exp (t * ⟪θ, x⟫))
      (multivariateGaussianMixtureMeasure p m S) :=
    integrable_of_mem_integrableExpSet (by simp)
  rw [mgf, integral_multivariateGaussianMixtureMeasure hf]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : p.weights k = 0
  · simp [hk]
  · rw [smul_eq_mul, ← mgf, mgf_inner_multivariateGaussian (m k) θ
      (hS k (pos_iff_ne_zero.mpr hk)) t]

/-- The cumulant-generating function of a linear observable of a multivariate Gaussian mixture is
the logarithm of the weighted sum of the Gaussian moment-generating functions. -/
theorem cgf_inner_multivariateGaussianMixtureMeasure
    (hS : ∀ k, 0 < p.weights k → (S k).PosSemidef) (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    cgf (fun x ↦ ⟪θ, x⟫) (multivariateGaussianMixtureMeasure p m S) t =
      Real.log (∑ k, (p.weights k : ℝ) *
        Real.exp (t * ⟪θ, m k⟫ + t ^ 2 / 2 * ⟪θ, (S k).toEuclideanLin θ⟫)) := by
  rw [cgf, mgf_inner_multivariateGaussianMixtureMeasure hS]

/-- The characteristic function of a multivariate Gaussian mixture with positive-semidefinite
positive-weight components is the weighted sum of the Gaussian characteristic functions. -/
theorem charFun_multivariateGaussianMixtureMeasure
    (hS : ∀ k, 0 < p.weights k → (S k).PosSemidef) (t : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussianMixtureMeasure p m S) t =
      ∑ k, (p.weights k : ℂ) * Complex.exp (⟪t, m k⟫ * Complex.I - t ⬝ᵥ S k *ᵥ t / 2) := by
  let _ : MeasurableSpace κ := ⊤
  let _ : IsProbabilityMeasure
      ((categoricalMeasure p).bind fun k ↦ multivariateGaussian (m k) (S k)) := by
    rw [← multivariateGaussianMixtureMeasure_eq_bind]
    infer_instance
  rw [multivariateGaussianMixtureMeasure_eq_bind, Measure.charFun_bind _
    Measurable.of_discrete.aemeasurable, integral_categoricalMeasure]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : p.weights k = 0
  · simp [hk]
  · rw [charFun_multivariateGaussian (hS k (pos_iff_ne_zero.mpr hk)), Complex.real_smul]

/-! ### Mean and covariance -/

/-- A multivariate Gaussian mixture has finite moments of every finite order. -/
theorem memLp_id_multivariateGaussianMixtureMeasure (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) {q : ℝ≥0∞} (hq : q ≠ ∞) :
    MemLp id q (multivariateGaussianMixtureMeasure p m S) := by
  rw [multivariateGaussianMixtureMeasure_def]
  exact Finset.sum_induction _ (fun μ : Measure (EuclideanSpace ℝ ι) ↦ MemLp id q μ)
    (fun _ _ ↦ MemLp.add_measure) memLp_measure_zero fun k _ ↦
      (IsGaussian.memLp_id (multivariateGaussian (m k) (S k)) q hq).smul_measure
        ENNReal.coe_ne_top

/-- The mean of a multivariate Gaussian mixture is the weighted mean of the component means. -/
@[simp]
theorem integral_id_multivariateGaussianMixtureMeasure (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    ∫ x, x ∂multivariateGaussianMixtureMeasure p m S = ∑ k, (p.weights k : ℝ) • m k := by
  rw [integral_multivariateGaussianMixtureMeasure (f := fun x ↦ x)
    (integrable_multivariateGaussianMixtureMeasure_iff.mpr fun k _ ↦ IsGaussian.integrable_id)]
  simp

/-- **Law of total covariance** for a multivariate Gaussian mixture with positive-semidefinite
positive-weight components: the weighted component covariance plus the weighted spread of the
component means about the overall mean. -/
theorem covMatrix_multivariateGaussianMixtureMeasure
    (hS : ∀ k, 0 < p.weights k → (S k).PosSemidef) :
    covMatrix (multivariateGaussianMixtureMeasure p m S) =
      ∑ k, (p.weights k : ℝ) • (S k + Matrix.vecMulVec
        (m k - ∑ j, (p.weights j : ℝ) • m j) (m k - ∑ j, (p.weights j : ℝ) • m j)) := by
  set μ := multivariateGaussianMixtureMeasure p m S
  have hmem := memLp_id_multivariateGaussianMixtureMeasure p m S (q := 2) ENNReal.ofNat_ne_top
  have hcoord (i : ι) : MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 μ := by
    simpa only [id_eq, EuclideanSpace.coe_proj] using
      hmem.continuousLinearMap_comp (𝕜 := ℝ) (EuclideanSpace.proj i)
  have hw : ∑ k, (p.weights k : ℝ) = 1 := by exact_mod_cast p.total_of_fintype
  have hmean (i : ι) : ∫ x, x i ∂μ = ∑ k, (p.weights k : ℝ) * m k i := by
    rw [integral_multivariateGaussianMixtureMeasure (MemLp.integrable one_le_two (hcoord i))]
    simp
  have hsecond (i j : ι) :
      ∫ x, x i * x j ∂μ = ∑ k, (p.weights k : ℝ) * (S k i j + m k i * m k j) := by
    rw [integral_multivariateGaussianMixtureMeasure (f := fun x ↦ x i * x j)
      ((hcoord i).integrable_mul (hcoord j))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : p.weights k = 0
    · simp [hk]
    · rw [smul_eq_mul, integral_eval_mul_eval_multivariateGaussian (m k)
        (hS k (pos_iff_ne_zero.mpr hk))]
  ext i j
  rw [covMatrix_apply, covariance_eq_sub (hcoord i) (hcoord j)]
  simp only [Pi.mul_apply, hmean, hsecond]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, WithLp.ofLp_sub, WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply]
  set a := ∑ k, (p.weights k : ℝ) * m k i
  set b := ∑ k, (p.weights k : ℝ) * m k j
  have hexpand : ∀ k, (p.weights k : ℝ) * (S k i j + (m k i - a) * (m k j - b)) =
      (p.weights k : ℝ) * (S k i j + m k i * m k j) - b * ((p.weights k : ℝ) * m k i) -
        a * ((p.weights k : ℝ) * m k j) + a * b * (p.weights k : ℝ) := fun k ↦ by ring
  rw [Finset.sum_congr rfl fun k _ ↦ hexpand k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hw]
  ring

/-- The mean of a random vector whose law is a multivariate Gaussian mixture. -/
theorem integral_of_hasLaw_multivariateGaussianMixtureMeasure
    (hX : HasLaw X (multivariateGaussianMixtureMeasure p m S) P) :
    ∫ ω, X ω ∂P = ∑ k, (p.weights k : ℝ) • m k := by
  rw [hX.integral_eq, integral_id_multivariateGaussianMixtureMeasure]

end TauCeti.Probability
