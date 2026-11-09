/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Categorical.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Moments.Covariance
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Probability.Distributions.Gaussian.Transforms
import TauCeti.Probability.Distributions.Mixture.Basic
import TauCeti.Probability.Moments.Mixture

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
finite-mixture integration, the exponential-integrability domain, and the mean
`∑ k, pₖ • mₖ` for every parameter value. When every positive-weight component has a
positive-semidefinite covariance parameter, they also include the moment-generating function of
every linear observable, the characteristic function, and the law of total covariance
`∑ k, pₖ • (Sₖ + (mₖ - μ)(mₖ - μ)ᵀ)` with `μ` the mean.

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
  finiteMixtureMeasure p fun k ↦ multivariateGaussian (m k) (S k)

/-- The multivariate Gaussian mixture as its defining weighted sum of Gaussian laws. -/
theorem multivariateGaussianMixtureMeasure_def (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    multivariateGaussianMixtureMeasure p m S =
      ∑ k, (p.weights k : ℝ≥0∞) • multivariateGaussian (m k) (S k) :=
  finiteMixtureMeasure_def p _

/-- Every multivariate Gaussian mixture is a probability measure. -/
instance isProbabilityMeasure_multivariateGaussianMixtureMeasure (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) :
    IsProbabilityMeasure (multivariateGaussianMixtureMeasure p m S) := by
  exact isProbabilityMeasure_finiteMixtureMeasure fun _ ↦ inferInstance

/-- The multivariate Gaussian mixture is the categorical mixture of its Gaussian components. -/
theorem multivariateGaussianMixtureMeasure_eq_bind [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (p : StdSimplex ℝ≥0 κ) (m : κ → EuclideanSpace ℝ ι)
    (S : κ → Matrix ι ι ℝ) :
    multivariateGaussianMixtureMeasure p m S =
      (categoricalMeasure p).bind fun k ↦ multivariateGaussian (m k) (S k) :=
  finiteMixtureMeasure_eq_bind p _

/-- A mixture of identical multivariate Gaussian components is that Gaussian law. -/
@[simp]
theorem multivariateGaussianMixtureMeasure_const (p : StdSimplex ℝ≥0 κ)
    (μ : EuclideanSpace ℝ ι) (C : Matrix ι ι ℝ) :
    multivariateGaussianMixtureMeasure p (fun _ ↦ μ) (fun _ ↦ C) = multivariateGaussian μ C :=
  finiteMixtureMeasure_const p _

/-- Changing the parameters of zero-weight components leaves the mixture unchanged. -/
theorem multivariateGaussianMixtureMeasure_congr {m' : κ → EuclideanSpace ℝ ι}
    {S' : κ → Matrix ι ι ℝ} (h : ∀ k, 0 < p.weights k → m k = m' k ∧ S k = S' k) :
    multivariateGaussianMixtureMeasure p m S = multivariateGaussianMixtureMeasure p m' S' := by
  apply finiteMixtureMeasure_congr
  intro k hk
  obtain ⟨hm, hS⟩ := h k hk
  rw [hm, hS]

/-- Multivariate Gaussian mixtures are measurable in their weights, means, and covariance
parameters. -/
@[fun_prop]
theorem measurable_multivariateGaussianMixtureMeasure :
    Measurable fun z : StdSimplex ℝ≥0 κ × (κ → EuclideanSpace ℝ ι) × (κ → Matrix ι ι ℝ) ↦
      multivariateGaussianMixtureMeasure z.1 z.2.1 z.2.2 := by
  refine measurable_finiteMixtureMeasure
    (p := fun z : StdSimplex ℝ≥0 κ × (κ → EuclideanSpace ℝ ι) ×
      (κ → Matrix ι ι ℝ) ↦ z.1)
    (K := fun z k ↦ multivariateGaussian (z.2.1 k) (z.2.2 k)) (by fun_prop) ?_
  intro k
  exact measurable_multivariateGaussian.comp
    (f := fun z : StdSimplex ℝ≥0 κ × (κ → EuclideanSpace ℝ ι) ×
      (κ → Matrix ι ι ℝ) ↦ (z.2.1 k, z.2.2 k)) (by fun_prop)

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

omit [Fintype κ] [Fintype ι] [DecidableEq ι] in
/-- A component without positive-definite covariance has zero weight when every positive-weight
component is positive definite. -/
private theorem weights_eq_zero_of_not_posDef (hS : ∀ k, 0 < p.weights k → (S k).PosDef) {k : κ}
    (hk : ¬(S k).PosDef) : p.weights k = 0 :=
  nonpos_iff_eq_zero.mp (not_lt.mp fun hw ↦ hk (hS k hw))

/-- If every positive-weight component has positive-definite covariance, the mixture density is
the weighted sum of all component densities. -/
theorem multivariateGaussianMixturePDFReal_eq_sum_of_posDef
    (hS : ∀ k, 0 < p.weights k → (S k).PosDef) (x : EuclideanSpace ℝ ι) :
    multivariateGaussianMixturePDFReal p m S x =
      ∑ k, (p.weights k : ℝ) * multivariateGaussianPDFReal (m k) (S k) x := by
  classical
  rw [multivariateGaussianMixturePDFReal_def]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun k _ hk ↦ ?_
  simp [weights_eq_zero_of_not_posDef hS (by simpa using hk)]

open Classical in
/-- The extended mixture density as a weighted sum over the positive-definite components. -/
theorem multivariateGaussianMixturePDF_eq_sum (p : StdSimplex ℝ≥0 κ)
    (m : κ → EuclideanSpace ℝ ι) (S : κ → Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    multivariateGaussianMixturePDF p m S x =
      ∑ k with (S k).PosDef,
        (p.weights k : ℝ≥0∞) * multivariateGaussianPDF (m k) (S k) x := by
  rw [multivariateGaussianMixturePDF_eq_ofReal, multivariateGaussianMixturePDFReal_def,
    ENNReal.ofReal_sum_of_nonneg fun k _ ↦
      mul_nonneg (NNReal.coe_nonneg _) (multivariateGaussianPDFReal_nonneg _ _ _)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    multivariateGaussianPDF_def]

/-- If every positive-weight component has positive-definite covariance, the extended mixture
density is the weighted sum of all component densities. -/
theorem multivariateGaussianMixturePDF_eq_sum_of_posDef
    (hS : ∀ k, 0 < p.weights k → (S k).PosDef) (x : EuclideanSpace ℝ ι) :
    multivariateGaussianMixturePDF p m S x =
      ∑ k, (p.weights k : ℝ≥0∞) * multivariateGaussianPDF (m k) (S k) x := by
  classical
  rw [multivariateGaussianMixturePDF_eq_sum]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun k _ hk ↦ ?_
  simp [weights_eq_zero_of_not_posDef hS (by simpa using hk)]

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
      rw [multivariateGaussianMixturePDF_eq_sum, Finset.sum_filter]
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
    simp [weights_eq_zero_of_not_posDef hS (Finset.mem_filter.mp hk).2]
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
      ∀ k, 0 < p.weights k → Integrable f (multivariateGaussian (m k) (S k)) :=
  integrable_finiteMixtureMeasure_iff

variable [NormedSpace ℝ E]

/-- The expectation of an integrable observable is the weighted sum of its component
expectations. -/
theorem integral_multivariateGaussianMixtureMeasure
    (hf : Integrable f (multivariateGaussianMixtureMeasure p m S)) :
    ∫ x, f x ∂multivariateGaussianMixtureMeasure p m S =
      ∑ k, (p.weights k : ℝ) • ∫ x, f x ∂multivariateGaussian (m k) (S k) :=
  integral_finiteMixtureMeasure hf

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
  let _ : MeasurableSpace κ := ⊤
  have ht : t ∈ integrableExpSet (fun x ↦ ⟪θ, x⟫)
      ((categoricalMeasure p).bind fun k ↦ multivariateGaussian (m k) (S k)) := by
    rw [← multivariateGaussianMixtureMeasure_eq_bind]
    simp
  rw [multivariateGaussianMixtureMeasure_eq_bind, Measure.mgf_bind _
    Measurable.of_discrete.aemeasurable _ t ht, integral_categoricalMeasure]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : p.weights k = 0
  · simp [hk]
  · rw [smul_eq_mul, mgf_inner_multivariateGaussian (m k) θ
      (hS k (pos_iff_ne_zero.mpr hk)) t]

/-- The cumulant-generating function of a linear observable of a multivariate Gaussian mixture is
the logarithm of the weighted sum of the Gaussian moment-generating functions. -/
theorem cgf_inner_multivariateGaussianMixtureMeasure
    (hS : ∀ k, 0 < p.weights k → (S k).PosSemidef) (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    cgf (fun x ↦ ⟪θ, x⟫) (multivariateGaussianMixtureMeasure p m S) t =
      Real.log (∑ k, (p.weights k : ℝ) *
        Real.exp (t * ⟪θ, m k⟫ + t ^ 2 / 2 * ⟪θ, (S k).toEuclideanLin θ⟫)) := by
  rw [cgf, mgf_inner_multivariateGaussianMixtureMeasure hS θ t]

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
  exact memLp_finiteMixtureMeasure fun k _ ↦
    IsGaussian.memLp_id (multivariateGaussian (m k) (S k)) q hq

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
  let _ : MeasurableSpace κ := ⊤
  have hmem := memLp_id_multivariateGaussianMixtureMeasure p m S (q := 2) ENNReal.ofNat_ne_top
  have hcoord (i : ι) : MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2
      ((categoricalMeasure p).bind fun k ↦ multivariateGaussian (m k) (S k)) := by
    simpa only [id_eq, multivariateGaussianMixtureMeasure_eq_bind] using hmem.eval_piLp i
  ext i j
  rw [covMatrix_apply, multivariateGaussianMixtureMeasure_eq_bind,
    covariance_bind Measurable.of_discrete (.of_forall fun _ ↦ inferInstance) (hcoord i)
      (hcoord j), covariance, integral_categoricalMeasure, integral_categoricalMeasure]
  simp only [integral_eval_multivariateGaussian, integral_categoricalMeasure, smul_eq_mul,
    ← Finset.sum_add_distrib, ← mul_add, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, WithLp.ofLp_sub, WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : p.weights k = 0
  · simp [hk]
  · rw [covariance_eval_multivariateGaussian (hS k (pos_iff_ne_zero.mpr hk))]

/-- The mean of a random vector whose law is a multivariate Gaussian mixture. -/
theorem integral_of_hasLaw_multivariateGaussianMixtureMeasure
    (hX : HasLaw X (multivariateGaussianMixtureMeasure p m S) P) :
    ∫ ω, X ω ∂P = ∑ k, (p.weights k : ℝ) • m k := by
  rw [hX.integral_eq, integral_id_multivariateGaussianMixtureMeasure]

end TauCeti.Probability
