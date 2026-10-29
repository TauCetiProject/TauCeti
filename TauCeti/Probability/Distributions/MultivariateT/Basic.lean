/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# Multivariate t laws

The multivariate t law `multivariateTMeasure m S ν` on `EuclideanSpace ℝ ι` is the law of
`m + √(ν / V) • Z`, where `Z` is a centred multivariate Gaussian vector with covariance `S` and
`V` is an independent chi-squared variable with `ν` degrees of freedom. It is defined for a
positive semidefinite scale matrix `S` and positive degrees of freedom `ν`; every other parameter
gives the zero measure. The matrix `S` is a scale parameter, not the covariance of the law.

Singular scale matrices are allowed. The law is then concentrated on the affine subspace
`m + range S`, and at zero scale it is the point mass at `m` for every `ν > 0`. Affine maps,
including rectangular and rank-deficient ones, transform the location and scale parameters by
the same rule as for Gaussian laws and leave the degrees of freedom unchanged.

## Main results

* `TauCeti.Probability.multivariateTMeasure`: the multivariate t law.
* `TauCeti.Probability.isProbabilityMeasure_multivariateTMeasure`: valid parameters give a
  probability measure.
* `TauCeti.Probability.multivariateTMeasure_zero_scale`: zero scale gives the point mass at the
  location.
* `TauCeti.Probability.hasLaw_multivariateT_of_gaussian_chiSquared`: the random-variable
  construction from independent Gaussian and chi-squared variables.
* `TauCeti.Probability.map_affine_multivariateTMeasure`: closure under affine maps.
* `TauCeti.Probability.ae_mem_affineRange_multivariateTMeasure`: concentration on
  `m + range S`.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

open Classical in
/-- The multivariate t law with location `m`, scale matrix `S` and `ν` degrees of freedom: the
law of `m + √(ν / V) • Z` for independent `Z` with law `multivariateGaussian 0 S` and `V` with
law `chiSquaredMeasure ν`. It is the zero measure unless `0 < ν` and `S` is positive
semidefinite. -/
def multivariateTMeasure (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν : ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  if 0 < ν ∧ S.PosSemidef then
    ((multivariateGaussian 0 S).prod (chiSquaredMeasure ν)).map
      fun z => m + √(ν / z.2) • z.1
  else 0

/-- For valid parameters, the multivariate t law is the Gaussian--chi-squared scale mixture
pushforward. -/
theorem multivariateTMeasure_of_posSemidef (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    {ν : ℝ} (hν : 0 < ν) (hS : S.PosSemidef) :
    multivariateTMeasure m S ν =
      ((multivariateGaussian 0 S).prod (chiSquaredMeasure ν)).map
        fun z => m + √(ν / z.2) • z.1 :=
  ite_eq_left ⟨hν, hS⟩

/-- Nonpositive degrees of freedom give the zero measure. -/
@[simp]
theorem multivariateTMeasure_of_nonpos (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) {ν : ℝ}
    (hν : ν ≤ 0) : multivariateTMeasure m S ν = 0 :=
  ite_eq_right fun h => (not_lt.mpr hν) h.1

/-- A scale matrix that is not positive semidefinite gives the zero measure. -/
@[simp]
theorem multivariateTMeasure_of_not_posSemidef (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (ν : ℝ) (hS : ¬ S.PosSemidef) : multivariateTMeasure m S ν = 0 :=
  ite_eq_right fun h => hS h.2

/-- The location-scale map `(z, v) ↦ m + √(ν / v) • z` is measurable. -/
private theorem measurable_scaleMixture {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (m : E) (ν : ℝ) :
    Measurable fun z : E × ℝ => m + √(ν / z.2) • z.1 := by
  fun_prop

/-- A multivariate t law with valid parameters is a probability measure. -/
theorem isProbabilityMeasure_multivariateTMeasure (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    {ν : ℝ} (hν : 0 < ν) (hS : S.PosSemidef) :
    IsProbabilityMeasure (multivariateTMeasure m S ν) := by
  have := isProbabilityMeasure_chiSquaredMeasure hν.le
  rw [multivariateTMeasure_of_posSemidef m hν hS]
  infer_instance

/-- A multivariate t law with zero scale is the point mass at its location, for every positive
number of degrees of freedom. -/
@[simp]
theorem multivariateTMeasure_zero_scale (m : EuclideanSpace ℝ ι) {ν : ℝ} (hν : 0 < ν) :
    multivariateTMeasure m 0 ν = Measure.dirac m := by
  have := isProbabilityMeasure_chiSquaredMeasure hν.le
  rw [multivariateTMeasure_of_posSemidef m hν Matrix.PosSemidef.zero,
    multivariateGaussian_zero_right, Measure.dirac_prod,
    Measure.map_map (measurable_scaleMixture m ν) measurable_prodMk_left]
  simp [Function.comp_def]

section HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → EuclideanSpace ℝ ι}
  {V : Ω → ℝ}

/-- If `Z` is a centred Gaussian vector with covariance `S` and `V` is an independent
chi-squared variable with `ν > 0` degrees of freedom, then `m + √(ν / V) • Z` has the
multivariate t law with location `m`, scale `S` and `ν` degrees of freedom. -/
theorem hasLaw_multivariateT_of_gaussian_chiSquared (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} {ν : ℝ} (hν : 0 < ν) (hS : S.PosSemidef) (hZV : IndepFun Z V P)
    (hZ : HasLaw Z (multivariateGaussian 0 S) P) (hV : HasLaw V (chiSquaredMeasure ν) P) :
    HasLaw (fun ω => m + √(ν / V ω) • Z ω) (multivariateTMeasure m S ν) P := by
  have := hZ.isProbabilityMeasure
  have := isProbabilityMeasure_chiSquaredMeasure hν.le
  have hmix : HasLaw (fun z : EuclideanSpace ℝ ι × ℝ => m + √(ν / z.2) • z.1)
      (multivariateTMeasure m S ν) ((multivariateGaussian 0 S).prod (chiSquaredMeasure ν)) :=
    ⟨(measurable_scaleMixture m ν).aemeasurable,
      (multivariateTMeasure_of_posSemidef m hν hS).symm⟩
  exact hmix.fun_comp (hZV.hasLaw_prod hZ hV)

end HasLaw

/-- **Affine images of multivariate t laws.** The image under `x ↦ L x + c` is the multivariate
t law with location `L m + c`, scale `L * S * Lᵀ` and the same degrees of freedom. The matrix
`L` may be rectangular or rank deficient. -/
@[simp]
theorem map_affine_multivariateTMeasure (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (ν : ℝ) (L : Matrix κ ι ℝ) (c : EuclideanSpace ℝ κ) :
    (multivariateTMeasure m S ν).map (fun x => L.toEuclideanLin x + c) =
      multivariateTMeasure (L.toEuclideanLin m + c) (L * S * L.transpose) ν := by
  rcases le_or_gt ν 0 with hν | hν
  · rw [multivariateTMeasure_of_nonpos _ _ hν, multivariateTMeasure_of_nonpos _ _ hν,
      Measure.map_zero]
  have := isProbabilityMeasure_chiSquaredMeasure hν.le
  have hLS : (L * S * L.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same L
  have hG : (multivariateGaussian 0 S).map L.toEuclideanLin =
      multivariateGaussian 0 (L * S * L.transpose) := by
    simpa using map_affine_multivariateGaussian 0 hS L 0
  have hL : Measurable L.toEuclideanLin :=
    L.toEuclideanLin.continuous_of_finiteDimensional.measurable
  rw [multivariateTMeasure_of_posSemidef _ hν hS, multivariateTMeasure_of_posSemidef _ hν hLS,
    ← hG, ← Measure.map_id (μ := chiSquaredMeasure ν),
    Measure.map_prod_map _ _ hL measurable_id, Measure.map_id,
    Measure.map_map (by fun_prop) (measurable_scaleMixture m ν),
    Measure.map_map (measurable_scaleMixture _ ν) (hL.prodMap measurable_id)]
  congr 1
  funext z
  simp [add_right_comm]

/-- A multivariate t law is concentrated on the affine subspace through its location whose
direction is the range of its scale matrix. -/
theorem ae_mem_affineRange_multivariateTMeasure (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (ν : ℝ) :
    ∀ᵐ x ∂multivariateTMeasure m S ν,
      x ∈ (AffineSubspace.mk' m (LinearMap.range (Matrix.toEuclideanLin S)) :
        Set (EuclideanSpace ℝ ι)) := by
  by_cases h : 0 < ν ∧ S.PosSemidef
  swap
  · simp [multivariateTMeasure, h]
  have hA : MeasurableSet (AffineSubspace.mk' m (LinearMap.range (Matrix.toEuclideanLin S)) :
      Set (EuclideanSpace ℝ ι)) :=
    (AffineSubspace.closed_of_finiteDimensional _).measurableSet
  rw [multivariateTMeasure_of_posSemidef m h.1 h.2]
  refine (ae_map_iff (measurable_scaleMixture m ν).aemeasurable hA).mpr ?_
  have hZ := ae_mem_affineRange_multivariateGaussian h.2 (0 : EuclideanSpace ℝ ι)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hZ] with z hz
  simp only [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, sub_zero,
    add_sub_cancel_left] at hz ⊢
  exact Submodule.smul_mem _ _ hz

end TauCeti.Probability
