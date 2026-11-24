/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic

/-!
# Conditioning on two identical Gaussian observations

For the centred Gaussian vector `(Z, Z, Z)`, retain the first coordinate and observe the final
two. The observed covariance is the singular all-ones matrix. Its covariance pseudoinverse gives
the average of the two displayed observations, so the conditional kernel is Dirac at that average.
In particular, an observation `(z, z)` determines the retained coordinate to be `z`.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The covariance of a retained standard Gaussian coordinate together with two identical
observations of it. -/
def gaussianIdenticalObservationCovariance :
    Matrix (Unit ⊕ Fin 2) (Unit ⊕ Fin 2) ℝ :=
  Matrix.vecMulVec 1 1

/-- Every entry of `gaussianIdenticalObservationCovariance` is one. -/
@[simp]
theorem gaussianIdenticalObservationCovariance_apply (i j : Unit ⊕ Fin 2) :
    gaussianIdenticalObservationCovariance i j = 1 := by
  simp [gaussianIdenticalObservationCovariance, Matrix.vecMulVec_apply]

/-- The covariance of one retained coordinate and two identical observations is positive
semidefinite. -/
theorem posSemidef_gaussianIdenticalObservationCovariance :
    gaussianIdenticalObservationCovariance.PosSemidef := by
  simpa [gaussianIdenticalObservationCovariance] using
    Matrix.posSemidef_vecMulVec_self_star (1 : Unit ⊕ Fin 2 → ℝ)

/-- The pseudoinverse of the singular two-by-two all-ones observed covariance has every entry
equal to one quarter. -/
theorem covariancePseudoInverse_gaussianIdenticalObservationCovariance_inr :
    (gaussianIdenticalObservationCovariance.submatrix Sum.inr Sum.inr).covariancePseudoInverse =
      (1 / 4 : ℝ) • gaussianIdenticalObservationCovariance.submatrix Sum.inr Sum.inr := by
  let C := gaussianIdenticalObservationCovariance.submatrix Sum.inr Sum.inr
  let D := (1 / 4 : ℝ) • C
  have hC : C.PosSemidef := posSemidef_gaussianIdenticalObservationCovariance.submatrix Sum.inr
  have hentry (i j : Fin 2) : C i j = 1 := by simp [C]
  have hDentry (i j : Fin 2) : D i j = 1 / 4 := by simp [D, hentry]
  have h₁ : C * D * C = C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, hentry, hDentry]
  have h₂ : D * C * D = D := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, hentry, hDentry]
  have h₃ : (C * D).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, hentry, hDentry]
  have h₄ : (D * C).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, hentry, hDentry]
  exact (Matrix.eq_covariancePseudoInverse_of_penrose hC h₁ h₂ h₃ h₄).symm

/-- Conditioning on two displayed copies of the same standard Gaussian has regression mean equal
to the average of the displayed observations. -/
@[simp]
theorem gaussianCondMean_gaussianIdenticalObservationCovariance
    (x₂ : EuclideanSpace ℝ (Fin 2)) :
    (0 : EuclideanSpace ℝ (Unit ⊕ Fin 2)).gaussianCondMean
        gaussianIdenticalObservationCovariance x₂ =
      EuclideanSpace.single () ((x₂ 0 + x₂ 1) / 2) := by
  rw [EuclideanSpace.gaussianCondMean_def,
    covariancePseudoInverse_gaussianIdenticalObservationCovariance_inr]
  ext i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
    EuclideanSpace.sumEquivProd]
  ring

/-- Conditioning on the two identical observations leaves zero residual covariance. -/
@[simp]
theorem gaussianCondCov_gaussianIdenticalObservationCovariance :
    gaussianIdenticalObservationCovariance.gaussianCondCov = 0 := by
  rw [Matrix.gaussianCondCov_def,
    covariancePseudoInverse_gaussianIdenticalObservationCovariance_inr]
  ext i j
  simp [Matrix.mul_apply]
  ring

/-- The displayed conditional kernel is Dirac at the average of the two observations. -/
theorem gaussianCondKernel_gaussianIdenticalObservationCovariance
    (x₂ : EuclideanSpace ℝ (Fin 2)) :
    (0 : EuclideanSpace ℝ (Unit ⊕ Fin 2)).gaussianCondKernel
        gaussianIdenticalObservationCovariance x₂ =
      Measure.dirac (EuclideanSpace.single () ((x₂ 0 + x₂ 1) / 2)) := by
  rw [EuclideanSpace.gaussianCondKernel_apply,
    gaussianCondMean_gaussianIdenticalObservationCovariance,
    gaussianCondCov_gaussianIdenticalObservationCovariance,
    multivariateGaussian_zero_right]

/-- In particular, observing `(z, z)` determines the retained coordinate to be `z`, despite the
singular observed covariance. -/
theorem gaussianCondKernel_gaussianIdenticalObservationCovariance_replicate (z : ℝ) :
    (0 : EuclideanSpace ℝ (Unit ⊕ Fin 2)).gaussianCondKernel
        gaussianIdenticalObservationCovariance (WithLp.toLp 2 ![z, z]) =
      Measure.dirac (EuclideanSpace.single () z) := by
  rw [gaussianCondKernel_gaussianIdenticalObservationCovariance]
  simp

/-- For a Gaussian vector with one retained coordinate and two identical observations, the regular
conditional distribution is Dirac at the average of the displayed observations. -/
theorem condDistrib_multivariateGaussian_gaussianIdenticalObservationCovariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (X : Ω → EuclideanSpace ℝ (Unit ⊕ Fin 2))
    (hX : HasLaw X
      (multivariateGaussian 0 gaussianIdenticalObservationCovariance) P) :
    ∀ᵐ x₂ ∂P.map fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2,
      condDistrib (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).1)
          (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2) P x₂ =
        Measure.dirac (EuclideanSpace.single () ((x₂ 0 + x₂ 1) / 2)) := by
  filter_upwards [condDistrib_multivariateGaussian X 0 hX
    posSemidef_gaussianIdenticalObservationCovariance] with x₂ hx₂
  rw [hx₂, gaussianCondKernel_gaussianIdenticalObservationCovariance]

end TauCeti.Probability
