/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic

import TauCeti.Data.Matrix.Mul
import TauCeti.Probability.Distributions.Gaussian.Conditional.RankOne

/-!
# Conditioning on identical Gaussian observations

For a Gaussian vector with positive constant covariance and a nonempty observed block,
`EuclideanSpace.gaussianCondKernel_matrixOf_const` gives a point mass at the retained means
shifted by the average observed deviation, at every ambient input. For a common mean, this
reduces to the average observation. Copies of a scalar Gaussian have common mean and constant
covariance by `TauCeti.Probability.gaussianReal_map_toLp_const`.

In particular, for `(Z, Z, Z)` with `Z` standard Gaussian, the covariance of the last two
coordinates is the singular all-ones matrix. An observation `(z, z)` determines the retained
coordinate to be `z`.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory

namespace EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- With positive constant covariance and a nonempty observed block, the conditional Gaussian
kernel is Dirac at the retained means shifted by the average observed deviation. This holds at
every ambient observation, including outside the affine support. -/
theorem gaussianCondKernel_matrixOf_const [Nonempty κ] (m : EuclideanSpace ℝ (ι ⊕ κ))
    {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ κ) :
    m.gaussianCondKernel (Matrix.of fun _ _ ↦ c) x =
      Measure.dirac (WithLp.toLp 2 fun i ↦ m (Sum.inl i) +
        (∑ j, (x j - m (Sum.inr j))) / Fintype.card κ) := by
  have hcov : (Matrix.of fun _ _ ↦ c : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) =
      vecMulVec (fun _ ↦ √c) (fun _ ↦ √c) := by
    rw [vecMulVec_const_const, Real.mul_self_sqrt hc.le]
  have hload : ∃ j : κ, (fun _ : ι ⊕ κ ↦ √c) (Sum.inr j) ≠ 0 :=
    ⟨Classical.arbitrary κ, (Real.sqrt_pos.2 hc).ne'⟩
  rw [hcov, m.gaussianCondKernel_vecMulVec_self hload]
  congr 1
  ext i
  rw [gaussianCondMean_vecMulVec_self_apply]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Real.sq_sqrt hc.le, ← mul_assoc, Real.mul_self_sqrt hc.le]
  rw [mul_comm (Fintype.card κ : ℝ) c, mul_div_mul_left _ _ hc.ne']

end EuclideanSpace

namespace TauCeti.Probability

section

open EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- For a constant mean and positive constant covariance, the conditional Gaussian kernel
uses the average observation at every ambient input, including off the diagonal support. -/
@[simp 1100]
theorem gaussianCondKernel_toLp_const_matrixOf_const [Nonempty κ] (μ : ℝ) {c : ℝ}
    (hc : 0 < c) (x : EuclideanSpace ℝ κ) :
    gaussianCondKernel (WithLp.toLp 2 (fun _ : ι ⊕ κ ↦ μ))
        (Matrix.of fun _ _ ↦ c) x =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ (∑ j, x j) / Fintype.card κ)) := by
  rw [gaussianCondKernel_matrixOf_const _ hc]
  congr 1
  ext i
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hn]
  ring

/-- At a constant observation, the constant-parameter conditional Gaussian kernel is the
Dirac law at that observation, for any common mean and positive variance. -/
@[simp 1200]
theorem gaussianCondKernel_toLp_const_matrixOf_const_toLp_const [Nonempty κ] (μ : ℝ)
    {c : ℝ} (hc : 0 < c) (z : ℝ) :
    gaussianCondKernel (WithLp.toLp 2 (fun _ : ι ⊕ κ ↦ μ))
        (Matrix.of fun _ _ ↦ c) (WithLp.toLp 2 (fun _ ↦ z)) =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ z)) := by
  simpa using gaussianCondKernel_toLp_const_matrixOf_const (ι := ι) μ hc
    (WithLp.toLp 2 (fun _ : κ ↦ z))

/-- With zero mean and positive constant covariance, regression is the average observation,
including at ambient inputs outside the diagonal support. -/
@[simp 1100]
theorem gaussianCondKernel_zero_matrixOf_const [Nonempty κ] {c : ℝ}
    (hc : 0 < c) (x : EuclideanSpace ℝ κ) :
    (0 : EuclideanSpace ℝ (ι ⊕ κ)).gaussianCondKernel (Matrix.of fun _ _ ↦ c) x =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ (∑ j, x j) / Fintype.card κ)) := by
  simpa only [← Pi.zero_def, WithLp.toLp_zero] using
    gaussianCondKernel_toLp_const_matrixOf_const (ι := ι) 0 hc x

end

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
  have hcov : gaussianIdenticalObservationCovariance = Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
    ext i j
    simp
  rw [hcov, gaussianCondKernel_zero_matrixOf_const zero_lt_one]
  congr 1
  ext i
  simp [Fin.sum_univ_two]

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
