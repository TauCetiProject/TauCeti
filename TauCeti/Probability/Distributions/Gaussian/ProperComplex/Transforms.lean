/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Basic
public import TauCeti.Probability.Distributions.Gaussian.Transforms
public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Real projections of proper complex Gaussian laws

For a complex vector `q`, the real linear observable `Re (qᴴ z)` of a proper complex
Gaussian is a scalar Gaussian. Its mean is `Re (qᴴ m)` and its variance is
`Re (qᴴ C q) / 2`. This identifies its moment- and cumulant-generating functions and
characteristic function, including singular covariance and zero-variance directions.
Every real exponential moment exists, even at the invalid-covariance Dirac fallback.

The scalar law is obtained from `map_inner_multivariateGaussian` in split real
coordinates, using `Matrix.dotProduct_realify_mulVec` for the variance.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexOrder Matrix

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real linear observable of a proper complex Gaussian has scalar Gaussian law, with
half the complex covariance quadratic form as its variance. -/
@[simp]
theorem map_re_dotProduct_properComplexGaussianMeasure (m q : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    (properComplexGaussianMeasure m C).map (fun z ↦ (star q ⬝ᵥ z).re) =
      gaussianReal (star q ⬝ᵥ m).re ((star q ⬝ᵥ C *ᵥ q).re / 2).toNNReal := by
  have hcov :
      ⟪complexToRealEuclidean ι q,
        (complexGaussianRealCovariance C).toEuclideanLin (complexToRealEuclidean ι q)⟫ =
        (star q ⬝ᵥ C *ᵥ q).re / 2 := by
    -- For complex scalars, RCLike.re and RCLike.im are definitionally Complex.re and Complex.im.
    have hcoords : (complexToRealEuclidean ι q).ofLp =
        Sum.elim (fun i ↦ RCLike.re (q i)) (fun i ↦ RCLike.im (q i)) :=
      funext (complexToRealEuclidean_apply ι q)
    calc
      _ = complexToRealEuclidean ι q ⬝ᵥ
          (complexGaussianRealCovariance C) *ᵥ complexToRealEuclidean ι q :=
        Matrix.inner_toEuclideanCLM _ _ _
      _ = (star q ⬝ᵥ C *ᵥ q).re / 2 := by
        simp only [complexGaussianRealCovariance_def, Matrix.smul_mulVec, dotProduct_smul,
          smul_eq_mul, hcoords]
        rw [Matrix.dotProduct_realify_mulVec]
        simp [div_eq_mul_inv, mul_comm]
  have hmap := map_inner_multivariateGaussian (complexToRealEuclidean ι m)
    (complexToRealEuclidean ι q) ((posSemidef_complexGaussianRealCovariance_iff C).2 hC)
  rw [← map_complexToRealEuclidean_properComplexGaussianMeasure,
    Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  simpa only [Function.comp_def, inner_complexToRealEuclidean, hcov] using hmap

/-- Every real linear observable has finite exponential moments of all real orders,
including at invalid covariances where the law is Dirac. -/
@[simp]
theorem integrableExpSet_re_dotProduct_properComplexGaussianMeasure (m q : ι → ℂ)
    (C : Matrix ι ι ℂ) :
    integrableExpSet (fun z ↦ (star q ⬝ᵥ z).re) (properComplexGaussianMeasure m C) =
      Set.univ := by
  simp_rw [← inner_complexToRealEuclidean ι q]
  -- The composed continuous linear map coerces definitionally to the inner-product observable.
  exact IsGaussian.integrableExpSet_dual (μ := properComplexGaussianMeasure m C)
    ((innerSL ℝ (complexToRealEuclidean ι q)).comp
      (complexToRealEuclidean ι).toContinuousLinearMap)

/-- The moment-generating function of a real projection of a proper complex Gaussian. -/
@[simp]
theorem mgf_re_dotProduct_properComplexGaussianMeasure (m q : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (t : ℝ) :
    mgf (fun z ↦ (star q ⬝ᵥ z).re) (properComplexGaussianMeasure m C) t =
      Real.exp (t * (star q ⬝ᵥ m).re + t ^ 2 / 4 * (star q ⬝ᵥ C *ᵥ q).re) := by
  rw [← mgf_id_map (by fun_prop), map_re_dotProduct_properComplexGaussianMeasure m q hC,
    mgf_id_gaussianReal]
  simp only [← RCLike.re_to_complex, hC.coe_toNNReal_re_dotProduct_div_two q]
  congr 1
  ring

/-- The cumulant-generating function of a real projection is a quadratic polynomial. -/
@[simp]
theorem cgf_re_dotProduct_properComplexGaussianMeasure (m q : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (t : ℝ) :
    cgf (fun z ↦ (star q ⬝ᵥ z).re) (properComplexGaussianMeasure m C) t =
      t * (star q ⬝ᵥ m).re + t ^ 2 / 4 * (star q ⬝ᵥ C *ᵥ q).re := by
  rw [cgf, mgf_re_dotProduct_properComplexGaussianMeasure m q hC, Real.log_exp]

/-- The characteristic function of the scalar law of a real projection. -/
theorem charFun_map_re_dotProduct_properComplexGaussianMeasure (m q : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (t : ℝ) :
    charFun ((properComplexGaussianMeasure m C).map (fun z ↦ (star q ⬝ᵥ z).re)) t =
      Complex.exp (t * (star q ⬝ᵥ m).re * Complex.I -
        t ^ 2 / 4 * (star q ⬝ᵥ C *ᵥ q).re) := by
  rw [map_re_dotProduct_properComplexGaussianMeasure m q hC, charFun_gaussianReal]
  simp only [← RCLike.re_to_complex, hC.coe_toNNReal_re_dotProduct_div_two q]
  push_cast
  congr 1
  ring

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {Z : Ω → ι → ℂ} {m : ι → ℂ} {C : Matrix ι ι ℂ}

/-- A real projection of a proper complex Gaussian random vector has the corresponding
scalar Gaussian law, including zero directional variance. -/
theorem HasLaw.re_dotProduct_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef) (q : ι → ℂ) :
    HasLaw (fun ω ↦ (star q ⬝ᵥ Z ω).re)
      (gaussianReal (star q ⬝ᵥ m).re ((star q ⬝ᵥ C *ᵥ q).re / 2).toNNReal) P := by
  rw [← map_re_dotProduct_properComplexGaussianMeasure m q hC]
  exact (hasLaw_map (X := fun z : ι → ℂ ↦ (star q ⬝ᵥ z).re) (by fun_prop)).comp hZ

end ProbabilityTheory
