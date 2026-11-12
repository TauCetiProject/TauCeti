/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.LowDimension
import TauCeti.MeasureTheory.Constructions.EuclideanSpace

/-!
# Gaussian conditioning on redundant observations

A rank-one jointly Gaussian vector consists of affine functions of one scalar Gaussian.
Any nonconstant observed block therefore determines the retained block exactly. The conditional
covariance vanishes, and the pseudoinverse regression formula gives a Dirac law, even though
an observed block with several coordinates has singular covariance.

In particular, observing two copies of a standard Gaussian determines that Gaussian. The
conditional kernel is specified at every ambient observation: for two identical copies, its
extension off the diagonal uses the average of the observed coordinates.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-- For a rank-one joint covariance, a nonzero observed loading removes all conditional
variance, including when the observed covariance is singular. -/
@[simp]
theorem gaussianCondCov_vecMulVec (u : ι → ℝ) (v : κ → ℝ) (hv : v ≠ 0) :
    (vecMulVec (Sum.elim u v) (Sum.elim u v)).gaussianCondCov = 0 := by
  have hd : v ⬝ᵥ v ≠ 0 := fun h ↦ hv (dotProduct_self_eq_zero.mp h)
  have h₂₂ : (vecMulVec (Sum.elim u v) (Sum.elim u v)).submatrix Sum.inr Sum.inr =
      vecMulVec v v := rfl
  have h₁₂ : (vecMulVec (Sum.elim u v) (Sum.elim u v)).submatrix Sum.inl Sum.inr =
      vecMulVec u v := rfl
  have h₂₁ : (vecMulVec (Sum.elim u v) (Sum.elim u v)).submatrix Sum.inr Sum.inl =
      vecMulVec v u := rfl
  have h₁₁ : (vecMulVec (Sum.elim u v) (Sum.elim u v)).submatrix Sum.inl Sum.inl =
      vecMulVec u u := rfl
  rw [Matrix.gaussianCondCov_def, h₂₂, h₁₂, h₂₁, h₁₁,
    covariancePseudoInverse_vecMulVec]
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_smul,
    Matrix.smul_mul, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul,
    Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  field_simp
  ring

end TauCeti.Probability

namespace EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- For a rank-one covariance, regression onto a nonzero observed loading recovers the
latent scalar by its least-squares coordinate, at every ambient observed value. At zero
observed loading, the formula returns the unconditional mean. -/
theorem gaussianCondMean_vecMulVec (m : EuclideanSpace ℝ (ι ⊕ κ))
    (u : ι → ℝ) (v : κ → ℝ) (x : EuclideanSpace ℝ κ) :
    m.gaussianCondMean (vecMulVec (Sum.elim u v) (Sum.elim u v)) x =
      (sumEquivProd m).1 + WithLp.toLp 2
        (fun i ↦ u i * (v ⬝ᵥ (x - (sumEquivProd m).2)) / (v ⬝ᵥ v)) := by
  have h₂₂ : (vecMulVec (Sum.elim u v) (Sum.elim u v)).submatrix Sum.inr Sum.inr =
      vecMulVec v v := rfl
  have h₁₂ : (vecMulVec (Sum.elim u v) (Sum.elim u v)).submatrix Sum.inl Sum.inr =
      vecMulVec u v := rfl
  rw [gaussianCondMean_def, h₂₂, h₁₂, covariancePseudoInverse_vecMulVec]
  congr 1
  ext i
  simp only [Matrix.toLpLin_apply, Matrix.mul_smul, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, Matrix.smul_mulVec, vecMulVec_mulVec, Pi.smul_apply,
    op_smul_eq_smul, smul_eq_mul, WithLp.ofLp_toLp, WithLp.ofLp_sub]
  by_cases hd : v ⬝ᵥ v = 0
  · simp [dotProduct_self_eq_zero.mp hd]
  · field_simp

variable [DecidableEq ι]

/-- A nonconstant block of a rank-one jointly Gaussian vector determines the retained block.
This formula also specifies the kernel away from the observed affine support. -/
theorem gaussianCondKernel_vecMulVec (m : EuclideanSpace ℝ (ι ⊕ κ))
    (u : ι → ℝ) (v : κ → ℝ) (hv : v ≠ 0) (x : EuclideanSpace ℝ κ) :
    m.gaussianCondKernel (vecMulVec (Sum.elim u v) (Sum.elim u v)) x =
      Measure.dirac ((sumEquivProd m).1 + WithLp.toLp 2
        (fun i ↦ u i * (v ⬝ᵥ (x - (sumEquivProd m).2)) / (v ⬝ᵥ v))) := by
  rw [gaussianCondKernel_apply, TauCeti.Probability.gaussianCondCov_vecMulVec u v hv,
    gaussianCondMean_vecMulVec, TauCeti.Probability.multivariateGaussian_zero_right]

end EuclideanSpace

namespace TauCeti.Probability

/-- Replicating a standard Gaussian gives the centered Gaussian with every covariance entry
one. This includes the empty coordinate type. -/
theorem map_replicate_gaussianReal (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (gaussianReal 0 1).map (fun z ↦ WithLp.toLp 2 (fun _ : ι ↦ z)) =
      multivariateGaussian 0 (Matrix.of fun _ _ : ι ↦ (1 : ℝ)) := by
  let L : Matrix ι Unit ℝ := Matrix.of fun _ _ ↦ 1
  have h := map_affine_multivariateGaussian (0 : EuclideanSpace ℝ Unit)
    Matrix.PosSemidef.one L 0
  rw [EuclideanSpace.multivariateGaussian_eq_map_single] at h
  simp only [PiLp.zero_apply, Matrix.one_apply_eq, Real.toNNReal_one] at h
  rw [Measure.map_map (by fun_prop) (EuclideanSpace.measurable_single default), Matrix.mul_one] at h
  have hcov : L * Lᵀ = Matrix.of (fun _ _ : ι ↦ (1 : ℝ)) := by
    ext i j
    simp [L, Matrix.mul_apply]
  have hL (z : ℝ) : L.toEuclideanLin (EuclideanSpace.single () z) =
      WithLp.toLp 2 (fun _ : ι ↦ z) := by
    ext i
    simp [L, Matrix.toLpLin_apply]
  simpa only [map_zero, add_zero, Function.comp_def, hL, hcov] using h

end TauCeti.Probability

namespace EuclideanSpace

/-- Conditioning one copy of a standard Gaussian on a nonempty block of identical copies
uses the average observation at every ambient input, including off the diagonal support. -/
theorem gaussianCondKernel_replicate {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (x : EuclideanSpace ℝ κ) :
    (0 : EuclideanSpace ℝ (Unit ⊕ κ)).gaussianCondKernel
        (Matrix.of fun _ _ ↦ (1 : ℝ)) x =
      Measure.dirac (WithLp.toLp 2 (fun _ : Unit ↦ (∑ j, x j) / Fintype.card κ)) := by
  have hv : (fun _ : κ ↦ (1 : ℝ)) ≠ 0 := by
    intro h
    obtain ⟨j⟩ := ‹Nonempty κ›
    exact one_ne_zero (congrFun h j)
  simpa [vecMulVec, dotProduct, EuclideanSpace.sumEquivProd] using
    EuclideanSpace.gaussianCondKernel_vecMulVec (0 : EuclideanSpace ℝ (Unit ⊕ κ))
      (fun _ ↦ 1) (fun _ ↦ 1) hv x

end EuclideanSpace

namespace TauCeti.Probability

/-- Observing two identical copies determines the retained Gaussian, although the observed
covariance has rank one in dimension two. -/
@[simp 1100]
theorem gaussianCondKernel_duplicate (z : ℝ) :
    (0 : EuclideanSpace ℝ (Unit ⊕ Fin 2)).gaussianCondKernel
        (Matrix.of fun _ _ ↦ (1 : ℝ)) (WithLp.toLp 2 (fun _ ↦ z)) =
      Measure.dirac (WithLp.toLp 2 (fun _ : Unit ↦ z)) := by
  simpa [Fin.sum_univ_two, ← two_mul] using
    EuclideanSpace.gaussianCondKernel_replicate (WithLp.toLp 2 (fun _ : Fin 2 ↦ z))

/-- The conditional law of a standard Gaussian given two copies of itself is a Dirac law.
The formula uses the average to specify the extension outside the diagonal observed support. -/
theorem condDistrib_gaussian_duplicate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) :
    condDistrib (fun ω ↦ WithLp.toLp 2 (fun _ : Unit ↦ Z ω))
        (fun ω ↦ WithLp.toLp 2 (fun _ : Fin 2 ↦ Z ω)) P =ᵐ[
      P.map (fun ω ↦ WithLp.toLp 2 (fun _ : Fin 2 ↦ Z ω))]
      (fun x ↦ Measure.dirac (WithLp.toLp 2 (fun _ : Unit ↦ (x 0 + x 1) / 2))) := by
  let X : Ω → EuclideanSpace ℝ (Unit ⊕ Fin 2) :=
    fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω)
  have hX : HasLaw X (multivariateGaussian 0 (Matrix.of fun _ _ ↦ (1 : ℝ))) P := by
    rw [← map_replicate_gaussianReal]
    exact (hasLaw_map (X := fun z : ℝ ↦ WithLp.toLp 2 (fun _ : Unit ⊕ Fin 2 ↦ z))
      (by fun_prop)).comp hZ
  have hS : (Matrix.of fun _ _ : Unit ⊕ Fin 2 ↦ (1 : ℝ)).PosSemidef := by
    simpa [Matrix.vecMulVec] using
      Matrix.posSemidef_vecMulVec_self_star (fun _ : Unit ⊕ Fin 2 ↦ (1 : ℝ))
  have h := condDistrib_multivariateGaussian X 0 hX hS
  have hk : ⇑((0 : EuclideanSpace ℝ (Unit ⊕ Fin 2)).gaussianCondKernel
      (Matrix.of fun _ _ ↦ (1 : ℝ))) =
      (fun x ↦ Measure.dirac (WithLp.toLp 2 (fun _ : Unit ↦ (x 0 + x 1) / 2))) := by
    funext x
    simpa [Fin.sum_univ_two] using EuclideanSpace.gaussianCondKernel_replicate x
  rw [hk] at h
  simpa [X, EuclideanSpace.sumEquivProd] using h

end TauCeti.Probability
