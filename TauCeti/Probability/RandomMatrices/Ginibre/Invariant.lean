/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Basic
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Symmetries of Ginibre and complex Gaussian Gram laws

A rectangular standard complex Ginibre matrix is invariant under multiplication by deterministic
unitaries on either side. More generally, rectangular matrices with orthonormal rows on the left
and orthonormal columns on the right send it to the standard law in the target shape. Its Gram
matrix therefore has a unitary-conjugation-invariant law and obeys orthonormal compression.
Transpose and conjugate transpose swap the Ginibre dimensions; the companion Gram matrix
`Xᴴ * X` has the Gaussian Gram law with dimension and sample size exchanged.
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

/-- Transposing a complex Ginibre matrix swaps its row and column dimensions. -/
@[simp]
theorem map_transpose_ginibreComplex (m n : ℕ) :
    (ginibreComplex m n).map Matrix.transpose = ginibreComplex n m := by
  rw [ginibreComplex_eq_map_properComplexGaussianMeasure n m, ← map_vec_ginibreComplex m n,
    Measure.map_map (by fun_prop) measurable_matrix_vec]
  exact congrArg (fun f ↦ (ginibreComplex m n).map f) (by
    funext X
    ext i j
    simp)

/-- Conjugate-transposing a complex Ginibre matrix swaps its row and column dimensions. -/
@[simp]
theorem map_conjTranspose_ginibreComplex (m n : ℕ) :
    (ginibreComplex m n).map Matrix.conjTranspose = ginibreComplex n m := by
  have h := map_star_properComplexGaussianMeasure (0 : Fin n × Fin m → ℂ) 1
  rw [star_zero, Matrix.transpose_one] at h
  rw [ginibreComplex_eq_map_properComplexGaussianMeasure n m, ← h, ← map_vec_ginibreComplex m n,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) measurable_matrix_vec]
  exact congrArg (fun f ↦ (ginibreComplex m n).map f) (by
    funext X
    ext i j
    simp)

/-- The companion Gram matrix of an `m × n` complex Ginibre matrix has dimension `n` and
sample size `m`. -/
theorem map_conjTranspose_mul_self_ginibreComplex (m n : ℕ) :
    (ginibreComplex m n).map (fun X ↦ Xᴴ * X) = gaussianGramComplex n m := by
  rw [gaussianGramComplex_def, ← map_conjTranspose_ginibreComplex m n,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Matrix.conjTranspose_conjTranspose]

/-- Multiplication by rectangular matrices with orthonormal rows on the left and
orthonormal columns on the right sends a standard complex Ginibre law to the smaller shape. -/
theorem map_mul_mul_ginibreComplex_of_mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one
    {m n m' n' : ℕ}
    (U : Matrix (Fin m') (Fin m) ℂ) (V : Matrix (Fin n) (Fin n') ℂ)
    (hU : U * Uᴴ = 1) (hV : Vᴴ * V = 1) :
    (ginibreComplex m n).map (fun X ↦ U * X * V) = ginibreComplex m' n' := by
  let e := matrixVecMeasurableEquiv (m := Fin m') (n := Fin n') (α := ℂ) 0
  apply MeasurableEquiv.map_measurableEquiv_injective e
  have hV' : Vᵀ * (Vᵀ)ᴴ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose] using congrArg Matrix.transpose hV
  have hL : (Vᵀ ⊗ₖ U) * (Vᵀ ⊗ₖ U)ᴴ = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV',
      Matrix.one_kronecker_one]
  have h := map_mulVec_pi_properComplexGaussianScalar_of_mul_conjTranspose_eq_one
    (Vᵀ ⊗ₖ U) hL
  simp only [← properComplexGaussianMeasure_zero_one_eq_pi, ← map_vec_ginibreComplex] at h
  rw [Measure.map_map (by fun_prop) measurable_matrix_vec] at h
  have heq (X : Matrix (Fin m) (Fin n) ℂ) :
      (Vᵀ ⊗ₖ U) *ᵥ X.vec = (U * X * V).vec := by
    simpa only [Matrix.transpose_transpose] using Matrix.kronecker_mulVec_vec U X Vᵀ
  simp_rw [Function.comp_def, heq] at h
  rw [Measure.map_map e.measurable (by fun_prop)]
  have hto : Measurable (WithLp.toLp 0 : (Fin n' × Fin m' → ℂ) → _) := by fun_prop
  have h' := congrArg (fun μ : Measure (Fin n' × Fin m' → ℂ) ↦ μ.map (WithLp.toLp 0)) h
  rw [Measure.map_map hto (by fun_prop), Measure.map_map hto measurable_matrix_vec] at h'
  have he : (e : Matrix (Fin m') (Fin n') ℂ → _) = WithLp.toLp 0 ∘ Matrix.vec :=
    funext (matrixVecMeasurableEquiv_apply 0)
  rw [he]
  exact h'

/-- Left and right unitary multiplication preserve the rectangular complex Ginibre law. -/
theorem map_unitary_mul_mul_ginibreComplex (m n : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (ginibreComplex m n).map (fun X ↦ U * X * V) = ginibreComplex m n :=
  map_mul_mul_ginibreComplex_of_mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one
    U V (Matrix.mem_unitaryGroup_iff.mp hU)
    (Matrix.mem_unitaryGroup_iff'.mp hV)

/-- Compression by a rectangular matrix with orthonormal rows preserves the standard complex
Gaussian Gram law with the compressed row dimension and unchanged sample size. -/
theorem map_mul_mul_conjTranspose_gaussianGramComplex_of_mul_conjTranspose_eq_one
    {m m' : ℕ} (n : ℕ) (U : Matrix (Fin m') (Fin m) ℂ) (hU : U * Uᴴ = 1) :
    (gaussianGramComplex m n).map (fun A ↦ U * A * Uᴴ) = gaussianGramComplex m' n := by
  have h := congrArg
    (fun μ : Measure (Matrix (Fin m') (Fin n) ℂ) ↦ μ.map (fun X ↦ X * Xᴴ))
      (map_mul_mul_ginibreComplex_of_mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one
        U (1 : Matrix (Fin n) (Fin n) ℂ) hU (by simp))
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  rw [gaussianGramComplex_def, gaussianGramComplex_def,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, Matrix.mul_one, Matrix.conjTranspose_mul,
    Matrix.mul_assoc] using h

/-- The standard complex Gaussian Gram law is invariant under unitary conjugation. -/
theorem map_unitary_conj_gaussianGramComplex (m n : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    (gaussianGramComplex m n).map (fun A ↦ U * A * Uᴴ) = gaussianGramComplex m n :=
  map_mul_mul_conjTranspose_gaussianGramComplex_of_mul_conjTranspose_eq_one n U
    (Matrix.mem_unitaryGroup_iff.mp hU)

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}

/-- Transposing a complex Ginibre random matrix swaps its row and column dimensions. -/
theorem HasLaw.transpose_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P) :
    HasLaw (fun ω ↦ (X ω)ᵀ) (ginibreComplex n m) P :=
  (HasLaw.mk (by fun_prop) (map_transpose_ginibreComplex m n)).comp hX

/-- Conjugate-transposing a complex Ginibre random matrix swaps its dimensions. -/
theorem HasLaw.conjTranspose_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P) :
    HasLaw (fun ω ↦ (X ω)ᴴ) (ginibreComplex n m) P :=
  (HasLaw.mk (by fun_prop) (map_conjTranspose_ginibreComplex m n)).comp hX

/-- The companion Gram matrix of a complex Ginibre random matrix has the complex Gaussian
Gram law with dimension and sample size exchanged. -/
theorem HasLaw.conjTranspose_mul_self_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P) :
    HasLaw (fun ω ↦ (X ω)ᴴ * X ω) (gaussianGramComplex n m) P :=
  (HasLaw.mk (by fun_prop) (map_conjTranspose_mul_self_ginibreComplex m n)).comp hX

/-- Rectangular orthonormal multiplication sends a complex Ginibre random matrix to the
standard complex Ginibre law in the target shape. -/
theorem HasLaw.mul_mul_ginibreComplex_of_mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one
    {m' n' : ℕ}
    {X : Ω → Matrix (Fin m) (Fin n) ℂ} (hX : HasLaw X (ginibreComplex m n) P)
    (U : Matrix (Fin m') (Fin m) ℂ) (V : Matrix (Fin n) (Fin n') ℂ)
    (hU : U * Uᴴ = 1) (hV : Vᴴ * V = 1) :
    HasLaw (fun ω ↦ U * X ω * V) (ginibreComplex m' n') P :=
  (HasLaw.mk (by fun_prop)
    (map_mul_mul_ginibreComplex_of_mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one
      U V hU hV)).comp hX

/-- Rectangular orthonormal compression of a complex Gaussian Gram random matrix has the
complex Gaussian Gram law in the target dimension. -/
theorem HasLaw.mul_mul_conjTranspose_gaussianGramComplex_of_mul_conjTranspose_eq_one {m' : ℕ}
    {A : Ω → Matrix (Fin m) (Fin m) ℂ} (hA : HasLaw A (gaussianGramComplex m n) P)
    (U : Matrix (Fin m') (Fin m) ℂ) (hU : U * Uᴴ = 1) :
    HasLaw (fun ω ↦ U * A ω * Uᴴ) (gaussianGramComplex m' n) P :=
  (HasLaw.mk (by fun_prop)
    (map_mul_mul_conjTranspose_gaussianGramComplex_of_mul_conjTranspose_eq_one n U hU)).comp hA

/-- Two-sided deterministic unitary multiplication preserves the law of a complex Ginibre
random matrix. -/
theorem HasLaw.unitary_mul_mul_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    HasLaw (fun ω ↦ U * X ω * V) (ginibreComplex m n) P :=
  hX.mul_mul_ginibreComplex_of_mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one
    U V (Matrix.mem_unitaryGroup_iff.mp hU)
    (Matrix.mem_unitaryGroup_iff'.mp hV)

/-- Unitary conjugation preserves the standard complex Gaussian Gram law on any sample space. -/
theorem HasLaw.unitary_conj_gaussianGramComplex {A : Ω → Matrix (Fin m) (Fin m) ℂ}
    (hA : HasLaw A (gaussianGramComplex m n) P)
    (U : Matrix (Fin m) (Fin m) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    HasLaw (fun ω ↦ U * A ω * Uᴴ) (gaussianGramComplex m n) P :=
  hA.mul_mul_conjTranspose_gaussianGramComplex_of_mul_conjTranspose_eq_one U
    (Matrix.mem_unitaryGroup_iff.mp hU)

end ProbabilityTheory
