/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.MeasureTheory.Integral.OddSymmetric
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.MeasureTheory.Measure.Interval

/-!
# Symmetry of Gaussian measures

A centered Gaussian measure on a real separable Banach space is invariant under negation.
Consequently, an odd function of a Gaussian vector centered at its mean has integral zero.
This applies in particular to odd products of centered linear observables, without assuming
independence or a nonsingular covariance.
The standard real Gaussian product law is also invariant under planar reflections, linear isometry
equivalences intertwine scaled standard Gaussian measures on finite-dimensional real inner product
spaces (`TauCeti.Probability.map_linearIsometryEquiv_map_smul_stdGaussian`), centered real
Gaussian laws assign equal mass to opposite half-lines (giving positive-variance half-line mass
`2⁻¹`), and centered real Gaussian laws and their independent products are invariant under
multiplication by deterministic scalars of unit modulus.
In particular, integrals against the standard Gaussian measure are invariant under linear isometry
equivalences (`LinearIsometryEquiv.integral_comp_stdGaussian`), such as the
coordinate sign changes `TauCeti.Probability.signFlip` of `EuclideanSpace ℝ ι`, so a standard
Gaussian integral may be replaced by the integral of the average of the integrand over all sign
changes (`TauCeti.Probability.integral_eq_integral_expect_signFlip`).
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- A Gaussian measure with mean zero is invariant under negation. -/
@[simp]
theorem map_neg_eq_self (μ : Measure E) [IsGaussian μ] (hμ : (∫ x, x ∂μ) = 0) :
    μ.map (fun x ↦ -x) = μ := by
  apply Measure.ext_of_charFunDual
  ext L
  calc
    _ = charFunDual μ (-L) := by
      rw [charFunDual_apply, charFunDual_apply,
        integral_map (by fun_prop) (by fun_prop)]
      simp
    _ = _ := by
      simp only [charFunDual_eq, integral_complex_ofReal, FunLike.coe_neg, Pi.neg_apply,
        integral_neg, variance_neg, integral_dual, hμ, map_zero, neg_zero]

/-- An odd function of a Gaussian vector centered at its mean has integral zero.
The statement also holds for nonintegrable functions, with the usual Bochner integral
totalization. -/
theorem integral_comp_sub_eq_zero_of_odd (μ : Measure E) [IsGaussian μ]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : Function.Odd f) : (∫ x, f (x - μ[id]) ∂μ) = 0 := by
  let ν := μ.map (fun x ↦ x - μ[id])
  have hν : ν[id] = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [id_eq]
    rw [integral_sub integrable_fun_id (integrable_const _), integral_const]
    simp
  have : ν.IsNegInvariant := ⟨map_neg_eq_self ν hν⟩
  calc
    _ = ∫ x, f x ∂ν := by
      simpa only [ν, MeasurableEquiv.coe_addRight, sub_eq_add_neg] using
        (integral_map_equiv (μ := μ) (MeasurableEquiv.addRight (-μ[id])) f).symm
    _ = 0 := integral_eq_zero_of_odd hf

end ProbabilityTheory.IsGaussian

namespace TauCeti.Probability

open ProbabilityTheory Real Set
open scoped NNReal ENNReal

/-- Every centered real Gaussian law is invariant under negation. -/
instance isNegInvariant_gaussianReal_zero (v : ℝ≥0) : (gaussianReal 0 v).IsNegInvariant :=
  ⟨by simp [Measure.neg_def]⟩

/-- A nondegenerate centered real Gaussian law assigns measure `2⁻¹` to `(0, ∞)`. -/
@[simp] theorem gaussianReal_zero_Ioi_zero {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v (Ioi 0) = 2⁻¹ :=
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  (gaussianReal 0 v).measure_Ioi_zero_eq_inv_two (measure_singleton 0)

/-- A nondegenerate centered real Gaussian law assigns measure `2⁻¹` to `(-∞, 0)`. -/
@[simp] theorem gaussianReal_zero_Iio_zero {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v (Iio 0) = 2⁻¹ :=
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  (gaussianReal 0 v).measure_Iio_zero_eq_inv_two (measure_singleton 0)

/-- A nondegenerate centered real Gaussian law assigns measure `2⁻¹` to `[0, ∞)`. -/
@[simp] theorem gaussianReal_zero_Ici_zero {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v (Ici 0) = 2⁻¹ :=
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  (gaussianReal 0 v).measure_Ici_zero_eq_inv_two (measure_singleton 0)

/-- A nondegenerate centered real Gaussian law assigns measure `2⁻¹` to `(-∞, 0]`. -/
@[simp] theorem gaussianReal_zero_Iic_zero {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v (Iic 0) = 2⁻¹ :=
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  (gaussianReal 0 v).measure_Iic_zero_eq_inv_two (measure_singleton 0)

/-- The standard Gaussian product law is invariant under reflection across a line. -/
theorem measurePreserving_reflection_gaussianReal (θ : ℝ) :
    MeasurePreserving
      (fun p : ℝ × ℝ => (cos θ * p.1 + sin θ * p.2, sin θ * p.1 - cos θ * p.2))
      (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1))
      (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1)) := by
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation θ : ℝ × ℝ →L[ℝ] ℝ × ℝ)
      (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1))
      (Measure.prod (gaussianReal 0 1) (gaussianReal 0 1)) :=
    ⟨by fun_prop, IsGaussian.map_rotation_eq_self (μ := gaussianReal 0 1)
      (by simp [integral_id_gaussianReal]) _⟩
  have hneg : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, by simp⟩
  convert ((MeasurePreserving.id (gaussianReal 0 1)).prod hneg).comp hrot using 1
  funext p
  simp [ContinuousLinearMap.rotation_apply, sub_eq_add_neg, add_comm]

/-- Every linear isometry equivalence between finite-dimensional real inner product spaces
intertwines scaled standard Gaussian measures; in particular, a linear isometry self-equivalence
preserves every scaled standard Gaussian measure. -/
theorem map_linearIsometryEquiv_map_smul_stdGaussian {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (f : E ≃ₗᵢ[ℝ] F) (c : ℝ) :
    ((stdGaussian E).map (fun x ↦ c • x)).map f = (stdGaussian F).map (fun y ↦ c • y) := by
  rw [Measure.map_map f.continuous.measurable (by fun_prop),
    show f ∘ (fun x : E ↦ c • x) = (fun y : F ↦ c • y) ∘ f from funext (map_smul f c),
    ← Measure.map_map (by fun_prop) f.continuous.measurable, stdGaussian_map f]

end TauCeti.Probability

namespace LinearIsometryEquiv

open ProbabilityTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- A linear isometry equivalence between finite-dimensional real inner product spaces carries the
standard Gaussian measure of the source to that of the target. -/
theorem measurePreserving_stdGaussian (f : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving f (stdGaussian E) (stdGaussian F) :=
  ⟨f.continuous.measurable, stdGaussian_map f⟩

/-- Integrals against the standard Gaussian measure are invariant under linear isometry
equivalences between finite-dimensional real inner product spaces. -/
theorem integral_comp_stdGaussian {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E ≃ₗᵢ[ℝ] F) (φ : F → G) :
    ∫ x, φ (f x) ∂stdGaussian E = ∫ y, φ y ∂stdGaussian F :=
  f.measurePreserving_stdGaussian.integral_comp f.toHomeomorph.measurableEmbedding φ

end LinearIsometryEquiv

namespace TauCeti.Probability

open ProbabilityTheory

section SignFlip

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Changing the signs of the coordinates of `EuclideanSpace ℝ ι` according to `ε : ι → ℤˣ`, as a
linear isometry equivalence. -/
def signFlip (ε : ι → ℤˣ) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i ↦
    if ε i = 1 then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ

/-- The `i`-th coordinate of `signFlip ε g` is `ε i • g i`. -/
@[simp]
theorem signFlip_apply (ε : ι → ℤˣ) (g : EuclideanSpace ℝ ι) (i : ι) :
    signFlip ε g i = ε i • g i := by
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [signFlip, h]

/-- Changing the signs of the coordinates is an involution. -/
@[simp]
theorem signFlip_symm (ε : ι → ℤˣ) : (signFlip ε).symm = signFlip ε := by
  refine LinearIsometryEquiv.ext fun g ↦ ?_
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext i
  simp [smul_smul, Int.units_mul_self]

/-- A standard Gaussian integral equals the standard Gaussian integral of the average of the
integrand over all coordinate sign changes. -/
theorem integral_eq_integral_expect_signFlip [DecidableEq ι] {φ : EuclideanSpace ℝ ι → ℝ}
    (hφ : Integrable φ (stdGaussian (EuclideanSpace ℝ ι))) :
    ∫ g, φ g ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ g, 𝔼 ε : ι → ℤˣ, φ (signFlip ε g) ∂stdGaussian (EuclideanSpace ℝ ι) := by
  have hint (ε : ι → ℤˣ) :
      Integrable (fun g ↦ φ (signFlip ε g)) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ((signFlip ε).measurePreserving_stdGaussian.integrable_comp_emb
      (signFlip ε).toHomeomorph.measurableEmbedding).2 hφ
  simp_rw [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _ fun ε _ ↦ hint ε]
  simp [LinearIsometryEquiv.integral_comp_stdGaussian]

end SignFlip

end TauCeti.Probability

namespace ProbabilityTheory

open scoped NNReal

/-- Multiplying a centered real Gaussian random variable by a scalar of unit modulus preserves its
law. -/
theorem HasLaw.gaussianReal_const_mul_of_abs_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    {c : ℝ} (hc : |c| = 1) :
    HasLaw (fun ω ↦ c * X ω) (gaussianReal 0 v) P := by
  have hc2 : NNReal.mk (c ^ 2) (sq_nonneg c) = 1 :=
    NNReal.eq (by simp [← sq_abs, hc])
  simpa [hc2] using gaussianReal_const_mul hX c

/-- Multiplying independent centered real Gaussian random variables by deterministic signs `η i`
with `|η i| = 1` preserves their joint product law. -/
theorem iIndepFun.hasLaw_pi_mul_gaussianReal_of_abs_eq_one {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} {g : ι → Ω → ℝ} {σ : ι → ℝ≥0}
    (hindep : iIndepFun g P) (hlaw : ∀ i, HasLaw (g i) (gaussianReal 0 (σ i)) P)
    {η : ι → ℝ} (hη : ∀ i, |η i| = 1) :
    HasLaw (fun ω i ↦ η i * g i ω) (Measure.pi fun i ↦ gaussianReal 0 (σ i)) P :=
  (hindep.comp (fun i x ↦ η i * x) fun _ ↦ by fun_prop).hasLaw_pi fun i ↦
    (hlaw i).gaussianReal_const_mul_of_abs_eq_one (hη i)

end ProbabilityTheory
