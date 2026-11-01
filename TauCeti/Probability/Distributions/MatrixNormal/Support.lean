/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.MatrixNormal.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix

import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Support of matrix normal laws

For positive semidefinite row and column covariances, vectorization identifies the support of a
matrix normal law with the affine range of the Kronecker covariance. This also gives an
almost-sure carrier for random matrices with that law.

If the Kronecker covariance is not positive definite, the matrix normal law is singular with
respect to product Lebesgue measure on matrix entries. This includes zero and other singular
covariances; invalid covariance parameters instead give the point mass at the mean.

## References

* A. K. Gupta and D. K. Nagar, *Matrix Variate Distributions*, Chapman & Hall/CRC, 2000,
  chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Kronecker

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The support of a matrix normal law with positive semidefinite covariances is the inverse
vectorization of the affine range of its Kronecker covariance. -/
@[simp]
theorem support_matrixNormalMeasure (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ}
    {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) :
    (matrixNormalMeasure M U V).support =
      {X | WithLp.toLp 2 X.vec ∈
        (AffineSubspace.mk' (WithLp.toLp 2 M.vec)
          (LinearMap.range (Matrix.toEuclideanLin (V ⊗ₖ U))) :
            Set (EuclideanSpace ℝ (κ × ι)))} := by
  let e : EuclideanSpace ℝ (κ × ι) ≃ₜ Matrix ι κ ℝ :=
    { toFun := fun x ↦ Matrix.of fun i j ↦ x.ofLp (j, i)
      invFun := fun X ↦ WithLp.toLp 2 X.vec
      left_inv := fun x ↦ by ext ⟨j, i⟩; rfl
      right_inv := fun X ↦ by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by
        exact (PiLp.continuous_toLp 2 _).comp <|
          continuous_pi fun ij ↦ continuous_id.matrix_elem ij.2 ij.1 }
  -- Identify the measurable-equivalence coercion with the homeomorphism coercion expected below.
  have he : ((matrixVecMeasurableEquiv 2).symm : EuclideanSpace ℝ (κ × ι) →
      Matrix ι κ ℝ) = e :=
    funext fun x ↦ matrixVecMeasurableEquiv_symm_apply 2 x
  rw [matrixNormalMeasure_of_posSemidef M hU hV]
  rw [he]
  rw [Measure.support_map_homeomorph,
    support_multivariateGaussian (hV.kronecker hU)]
  rw [e.image_eq_preimage_symm]
  rfl

/-- A matrix normal law with positive semidefinite covariances is almost surely in the inverse
vectorization of the affine range of its Kronecker covariance. -/
theorem ae_mem_affineRange_matrixNormalMeasure (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ}
    {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) :
    ∀ᵐ X ∂matrixNormalMeasure M U V,
      WithLp.toLp 2 X.vec ∈
        (AffineSubspace.mk' (WithLp.toLp 2 M.vec)
          (LinearMap.range (Matrix.toEuclideanLin (V ⊗ₖ U))) :
            Set (EuclideanSpace ℝ (κ × ι))) := by
  let A : Set (EuclideanSpace ℝ (κ × ι)) :=
    AffineSubspace.mk' (WithLp.toLp 2 M.vec)
      (LinearMap.range (Matrix.toEuclideanLin (V ⊗ₖ U)))
  have hA : MeasurableSet A := AffineSubspace.closed_of_finiteDimensional _ |>.measurableSet
  have h : ∀ᵐ X ∂matrixNormalMeasure M U V, (matrixVecMeasurableEquiv 2) X ∈ A := by
    apply (ae_map_iff (MeasurableEquiv.measurable (matrixVecMeasurableEquiv 2)).aemeasurable hA).1
    -- `map_vec_matrixNormalMeasure` is stated for the explicit vectorization function.
    have he : (matrixVecMeasurableEquiv 2 : Matrix ι κ ℝ → EuclideanSpace ℝ (κ × ι)) =
        (fun X ↦ WithLp.toLp 2 X.vec) :=
      funext fun X ↦ matrixVecMeasurableEquiv_apply 2 X
    rw [he, map_vec_matrixNormalMeasure M hU hV]
    exact ae_mem_affineRange_multivariateGaussian (hV.kronecker hU) (WithLp.toLp 2 M.vec)
  simpa only [A, matrixVecMeasurableEquiv_apply] using h

/-- Invalid row or column covariance parameters give singleton support at the mean. -/
@[simp]
theorem support_matrixNormalMeasure_of_not_posSemidef (M : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (h : ¬(U.PosSemidef ∧ V.PosSemidef)) :
    (matrixNormalMeasure M U V).support = {M} := by
  rw [matrixNormalMeasure_of_not_posSemidef M h, Measure.support_dirac, closure_singleton]

/-- A matrix normal law with singular Kronecker covariance is singular with respect to product
Lebesgue measure on its entries. -/
theorem mutuallySingular_matrixNormalMeasure_volume (M : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hUV : ¬(V ⊗ₖ U).PosDef) :
    matrixNormalMeasure M U V ⟂ₘ (volume : Measure (Matrix ι κ ℝ)) := by
  by_cases h : U.PosSemidef ∧ V.PosSemidef
  · have hsing := (matrixVecMeasurableEquiv (m := ι) (n := κ) (α := ℝ) 2).symm.measurableEmbedding
      |>.mutuallySingular_map
        (mutuallySingular_multivariateGaussian_volume hUV (WithLp.toLp 2 M.vec))
    rw [(volume_preserving_matrixVecMeasurableEquiv (m := ι) (n := κ)).symm.map_eq] at hsing
    rwa [← matrixNormalMeasure_of_posSemidef M h.1 h.2] at hsing
  · rw [matrixNormalMeasure_of_not_posSemidef M h]
    have hne : Nonempty (κ × ι) := by
      by_contra hempty
      let _ : IsEmpty (κ × ι) := not_nonempty_iff.mp hempty
      apply hUV
      exact ⟨Subsingleton.elim _ _, fun x hx ↦ absurd (Subsingleton.elim x 0) hx⟩
    let _ : Nonempty κ := ⟨hne.some.1⟩
    let _ : Nonempty ι := ⟨hne.some.2⟩
    have hnull : NullSingletonClass (volume : Measure (Matrix ι κ ℝ)) := ⟨fun X ↦ by
      have hx : (volume : Measure (EuclideanSpace ℝ (κ × ι)))
          {(matrixVecMeasurableEquiv 2) X} = 0 := measure_singleton _
      rw [← (volume_preserving_matrixVecMeasurableEquiv (m := ι) (n := κ)).map_eq,
        (matrixVecMeasurableEquiv 2).map_apply] at hx
      have hpre : (matrixVecMeasurableEquiv 2) ⁻¹' {(matrixVecMeasurableEquiv 2) X} = {X} := by
        ext Y
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact (matrixVecMeasurableEquiv 2).injective.eq_iff
      rwa [hpre] at hx⟩
    let _ := hnull
    exact mutuallySingular_dirac M volume

/-- At a singular Kronecker covariance, the ambient Radon--Nikodym derivative of a matrix normal
law vanishes almost everywhere. -/
theorem rnDeriv_matrixNormalMeasure_of_not_posDef (M : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hUV : ¬(V ⊗ₖ U).PosDef) :
    (matrixNormalMeasure M U V).rnDeriv volume =ᵐ[volume] 0 :=
  (mutuallySingular_matrixNormalMeasure_volume M hUV).rnDeriv_ae_eq_zero

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Matrix ι κ ℝ} {M : Matrix ι κ ℝ}
  {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}

/-- A random matrix with a matrix normal law lies almost surely in the affine range of its
Kronecker covariance after vectorization. -/
theorem HasLaw.ae_mem_affineRange_matrixNormalMeasure
    (hX : HasLaw X (matrixNormalMeasure M U V) P)
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    ∀ᵐ ω ∂P, WithLp.toLp 2 (X ω).vec ∈
      (AffineSubspace.mk' (WithLp.toLp 2 M.vec)
        (LinearMap.range (Matrix.toEuclideanLin (V ⊗ₖ U))) :
          Set (EuclideanSpace ℝ (κ × ι))) := by
  have hA : MeasurableSet
      (AffineSubspace.mk' (WithLp.toLp 2 M.vec)
        (LinearMap.range (Matrix.toEuclideanLin (V ⊗ₖ U))) :
          Set (EuclideanSpace ℝ (κ × ι))) :=
    AffineSubspace.closed_of_finiteDimensional _ |>.measurableSet
  have hsource : ∀ᵐ Y ∂matrixNormalMeasure M U V,
      (matrixVecMeasurableEquiv 2) Y ∈
        (AffineSubspace.mk' (WithLp.toLp 2 M.vec)
          (LinearMap.range (Matrix.toEuclideanLin (V ⊗ₖ U))) :
            Set (EuclideanSpace ℝ (κ × ι))) := by
    simpa only [matrixVecMeasurableEquiv_apply] using
      TauCeti.Probability.ae_mem_affineRange_matrixNormalMeasure M hU hV
  have hout := (hX.ae_iff (measurableSet_setOfPred.mp <|
    hA.preimage (matrixVecMeasurableEquiv 2).measurable)).2 hsource
  simpa only [matrixVecMeasurableEquiv_apply] using hout

end ProbabilityTheory
