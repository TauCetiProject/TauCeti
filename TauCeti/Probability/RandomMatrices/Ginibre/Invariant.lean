/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Density
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Unitary invariance of Ginibre and complex Gaussian Gram laws

A rectangular standard complex Ginibre matrix is invariant under multiplication by deterministic
unitaries on either side. Its Gram matrix therefore has a unitary-conjugation-invariant law.
The proofs use the proper complex Gaussian covariance transformation under the vectorized
matrix map `X ↦ U * X * V`. The invariance is stated both as equality of pushforward measures
and for random matrices with the prescribed law.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS, 2012, §2.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Kronecker

namespace TauCeti.Probability

/-- Left and right unitary multiplication preserve the rectangular complex Ginibre law. -/
theorem map_mul_mul_ginibreComplex (m n : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (ginibreComplex m n).map (fun X ↦ U * X * V) = ginibreComplex m n := by
  let e := matrixVecMeasurableEquiv (m := Fin m) (n := Fin n) (α := ℂ) 0
  apply MeasurableEquiv.map_measurableEquiv_injective e
  have hU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hV' : Vᵀ * (Vᵀ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.transpose_mem_unitaryGroup_iff.mpr hV)
  have hL : (Vᵀ ⊗ₖ U) * (Vᵀ ⊗ₖ U)ᴴ = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU', hV',
      Matrix.one_kronecker_one]
  have h := map_mulVec_pi_properComplexGaussianScalar_of_mul_conjTranspose_eq_one
    (Vᵀ ⊗ₖ U) hL
  rw [← properComplexGaussianMeasure_one_eq_pi, ← map_vec_ginibreComplex m n,
    Measure.map_map (by fun_prop) measurable_matrix_vec] at h
  have heq (X : Matrix (Fin m) (Fin n) ℂ) :
      (Vᵀ ⊗ₖ U) *ᵥ X.vec = (U * X * V).vec := by
    simpa only [Matrix.transpose_transpose] using Matrix.kronecker_mulVec_vec U X Vᵀ
  simp_rw [Function.comp_def, heq] at h
  rw [Measure.map_map e.measurable (by fun_prop)]
  have hto : Measurable (WithLp.toLp 0 : (Fin n × Fin m → ℂ) → _) := by fun_prop
  have h' := congrArg (fun μ : Measure (Fin n × Fin m → ℂ) ↦ μ.map (WithLp.toLp 0)) h
  rw [Measure.map_map hto (by fun_prop), Measure.map_map hto measurable_matrix_vec] at h'
  have he : (e : Matrix (Fin m) (Fin n) ℂ → _) = WithLp.toLp 0 ∘ Matrix.vec :=
    funext (matrixVecMeasurableEquiv_apply 0)
  rw [he]
  exact h'

/-- The standard complex Gaussian Gram law is invariant under unitary conjugation. -/
theorem map_unitary_conj_gaussianGramComplex (m n : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    (gaussianGramComplex m n).map (fun A ↦ U * A * Uᴴ) = gaussianGramComplex m n := by
  have h := congrArg
    (fun μ : Measure (Matrix (Fin m) (Fin n) ℂ) ↦ μ.map (fun X ↦ X * Xᴴ))
      (map_mul_mul_ginibreComplex m n U 1 hU (by simp))
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  rw [gaussianGramComplex_def, Measure.map_map (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, Matrix.mul_one, Matrix.conjTranspose_mul,
    Matrix.mul_assoc] using h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}

/-- Two-sided deterministic unitary multiplication preserves the law of a complex Ginibre
random matrix. -/
theorem HasLaw.unitary_mul_mul_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    HasLaw (fun ω ↦ U * X ω * V) (ginibreComplex m n) P :=
  (HasLaw.mk (by fun_prop) (map_mul_mul_ginibreComplex m n U V hU hV)).comp hX

/-- The Gram matrix of a complex Ginibre random matrix has the complex Gaussian Gram law. -/
theorem HasLaw.gram_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P) :
    HasLaw (fun ω ↦ X ω * (X ω)ᴴ) (gaussianGramComplex m n) P :=
  (HasLaw.mk (by fun_prop) (gaussianGramComplex_def m n).symm).comp hX

/-- Unitary conjugation preserves the standard complex Gaussian Gram law on any sample space. -/
theorem HasLaw.unitary_conj_gaussianGramComplex {A : Ω → Matrix (Fin m) (Fin m) ℂ}
    (hA : HasLaw A (gaussianGramComplex m n) P)
    (U : Matrix (Fin m) (Fin m) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    HasLaw (fun ω ↦ U * A ω * Uᴴ) (gaussianGramComplex m n) P :=
  (HasLaw.mk (by fun_prop) (map_unitary_conj_gaussianGramComplex m n U hU)).comp hA

end ProbabilityTheory
