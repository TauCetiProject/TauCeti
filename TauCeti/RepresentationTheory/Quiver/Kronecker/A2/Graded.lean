/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.A2.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Betti
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.Pairing

/-!
# Graded Cartan, Betti, and Euler conventions for the one-arrow quiver

Give the path algebra of `1 ⟶ 2` its path-length grading and order the vertices source first.
Its graded Cartan matrix is `[1, 0; q, 1]`: the source projective has a degree-zero source
simple and a degree-one target simple. The minimal linear resolutions of the vertex simples have
Betti Poincaré matrix `[1, 0; q t, 1]`, whose evaluation at `t = -1` is `[1, 0; -q, 1]`, the
inverse of the graded Cartan matrix. The categorical q-Euler matrix of the vertex simples is
`[1, -q⁻¹; 0, 1]`, not `[1, -q; 0, 1]`, because the pairing is q-antilinear in its first
variable. These matrices are inverse conjugate transposes.

The results below identify all three displayed matrices with the actual Laurent Grothendieck-group
constructions, compute the two columns of the graded Cartan map, verify `C(q) · B(q, -1) = I`,
and recover the ordinary Cartan and Euler matrices by evaluation at `q = 1`. The Euler-form
identification uses the finite-support Ext computation from the first-arrow resolutions, not a
totalized infinite sum.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for the projective resolutions and Cartan conventions.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for the graded
  Cartan matrix and the q-antilinear convention for the Euler form.
-/

public section

noncomputable section

namespace TauCeti.Quiver.Kronecker

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe u v

/-- The path-length-graded Cartan matrix of `1 ⟶ 2`, with simples in the rows and projectives
in the columns, in source-first order. -/
def gradedCartanMatrixA2 : Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  !![1, 0; T 1, 1]

/-- The entries of the graded Cartan matrix of `1 ⟶ 2`. -/
@[simp]
theorem gradedCartanMatrixA2_apply (i j : Fin 2) :
    gradedCartanMatrixA2 i j = !![1, 0; T 1, 1] i j := by
  rw [gradedCartanMatrixA2]

/-- The q-Euler matrix of `1 ⟶ 2`, q-antilinear in the row variable and q-linear in the
column variable, in source-first order. -/
def gradedEulerMatrixA2 : Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  !![1, -T (-1); 0, 1]

/-- The entries of the q-Euler matrix of `1 ⟶ 2`. -/
@[simp]
theorem gradedEulerMatrixA2_apply (i j : Fin 2) :
    gradedEulerMatrixA2 i j = !![1, -T (-1); 0, 1] i j := by
  rw [gradedEulerMatrixA2]

/-- The conjugate transpose of the graded Cartan matrix is a left inverse of the q-Euler
matrix. The coefficient involution is `LaurentPolynomial.invert`. -/
@[simp]
theorem gradedCartanMatrixA2_map_invert_transpose_mul_gradedEulerMatrixA2 :
    (gradedCartanMatrixA2.map (invert (R := ℤ)))ᵀ * gradedEulerMatrixA2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The q-Euler matrix is also a left inverse of the conjugate-transposed graded Cartan
matrix. -/
@[simp]
theorem gradedEulerMatrixA2_mul_gradedCartanMatrixA2_map_invert_transpose :
    gradedEulerMatrixA2 * (gradedCartanMatrixA2.map (invert (R := ℤ)))ᵀ = 1 :=
  mul_eq_one_comm.mp gradedCartanMatrixA2_map_invert_transpose_mul_gradedEulerMatrixA2

/-- The Betti Poincaré matrix of the minimal linear resolutions of the graded vertex simples of
`1 ⟶ 2`, with projectives in the rows and simples in the columns, in source-first order. -/
def gradedBettiMatrixA2 : Matrix (Fin 2) (Fin 2) (PowerSeries (LaurentPolynomial ℤ)) :=
  !![1, 0; PowerSeries.C (T 1) * PowerSeries.X, 1]

/-- The graded Cartan matrix and the `t = -1` evaluation of the Betti Poincaré matrix of `1 ⟶ 2`
satisfy `C(q) · B(q, -1) = I`. -/
@[simp]
theorem gradedCartanMatrixA2_mul_eval_neg_one_trunc_gradedBettiMatrixA2 :
    gradedCartanMatrixA2 *
      gradedBettiMatrixA2.map (fun P => (PowerSeries.trunc 2 P).eval (-1)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradedBettiMatrixA2, Matrix.mul_apply, Fin.sum_univ_two,
      PowerSeries.trunc_one, PowerSeries.trunc_C_mul, PowerSeries.trunc_X, Polynomial.eval_X]

/-- The `t = -1` evaluation of the Betti Poincaré matrix of `1 ⟶ 2` is also a left inverse of the
graded Cartan matrix. -/
@[simp]
theorem eval_neg_one_trunc_gradedBettiMatrixA2_mul_gradedCartanMatrixA2 :
    gradedBettiMatrixA2.map (fun P => (PowerSeries.trunc 2 P).eval (-1)) *
      gradedCartanMatrixA2 = 1 :=
  mul_eq_one_comm.mp gradedCartanMatrixA2_mul_eval_neg_one_trunc_gradedBettiMatrixA2

/-- Setting `q = 1` in the graded Cartan matrix gives the ordinary Cartan matrix. -/
@[simp]
theorem map_laurentEval_one_gradedCartanMatrixA2 :
    gradedCartanMatrixA2.map (laurentEval (1 : ℤˣ)) = cartanMatrixA2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Setting `q = 1` in the q-Euler matrix gives the ordinary Euler matrix. -/
@[simp]
theorem map_laurentEval_one_gradedEulerMatrixA2 :
    gradedEulerMatrixA2.map (laurentEval (1 : ℤˣ)) = eulerMatrixA2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {A : Type v} [Unique A] (k : Type u) [Field k]

/-- The categorical graded Cartan matrix of the one-arrow path algebra is `[1, 0; q, 1]`.
In particular, the off-diagonal multiplicity is a positive, not a negative, internal shift. -/
theorem submatrix_gradedCartanMatrix_eq_gradedCartanMatrixA2 :
    (gradedCartanMatrix (PathAlgebra.integerGrade k (Kronecker A))
      (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A))
      (PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A))).submatrix
        ![src, tgt] ![src, tgt] = gradedCartanMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  -- Read the two rows of the path-counting identity `(1 - q Aᵀ) C = 1`. Keep the
  -- categorical matrix opaque to simp, so that only this triangular system is solved.
  have h := PathAlgebra.one_sub_T_smul_transpose_mul_gradedCartanMatrix_eq_one k (Kronecker A)
  refine Matrix.ext fun i j => ?_
  have hs := congrFun₂ h src (![src, tgt] j)
  have ht := congrFun₂ h tgt (![src, tgt] j)
  fin_cases i <;> fin_cases j <;>
    simp [-gradedCartanMatrix_apply, Matrix.mul_apply, Matrix.one_apply,
      sum_univ, Nat.card_eq_fintype_card, Function.swap] at hs ht ⊢ <;>
    simp_all [-gradedCartanMatrix_apply]
  -- Only entry (1, 0) remains: `ht` gives its value via `-q + C₁₀ = 0`.
  -- Simplification does not rearrange this additive equation, so solve it linearly.
  linear_combination ht

/-- Each graded vertex-projective class maps to the corresponding column of the graded
Cartan matrix, expressed in the source-first vertex-simple basis. -/
theorem gradedCartanMap_gradedVertexProjectiveClass (j : Fin 2) :
    gradedCartanMap (PathAlgebra.integerGrade k (Kronecker A))
        (PathAlgebra.gradedVertexProjectiveClass k (Kronecker A) (![src, tgt] j)) =
      gradedCartanMatrixA2 0 j •
          PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) src +
        gradedCartanMatrixA2 1 j •
          PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) tgt := by
  let _ := PathAlgebra.integerGradedAlgebra k (Kronecker A)
  have h := gradedCartanMap_basis_apply_eq_sum (PathAlgebra.integerGrade k (Kronecker A))
    (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A))
    (PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A)) (![src, tgt] j)
  rw [PathAlgebra.gradedVertexProjectiveClassBasis_apply] at h
  rw [h]
  have hs := congrFun₂ (submatrix_gradedCartanMatrix_eq_gradedCartanMatrixA2 (A := A) k) 0 j
  have ht := congrFun₂ (submatrix_gradedCartanMatrix_eq_gradedCartanMatrixA2 (A := A) k) 1 j
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hs ht
  rw [sum_univ, hs, ht]

/-- The graded Cartan map sends the source projective to `[S₁] + q[S₂]`. This is an equality
of classes in the actual Laurent Grothendieck group of finite graded path-algebra modules. -/
theorem gradedCartanMap_gradedVertexProjectiveClass_src :
    gradedCartanMap (PathAlgebra.integerGrade k (Kronecker A))
        (PathAlgebra.gradedVertexProjectiveClass k (Kronecker A) src) =
      PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) src +
        (T 1 : LaurentPolynomial ℤ) •
          PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) tgt := by
  simpa using gradedCartanMap_gradedVertexProjectiveClass (A := A) k 0

/-- The graded Cartan map sends the target projective to `[S₂]`, without an internal shift. -/
theorem gradedCartanMap_gradedVertexProjectiveClass_tgt :
    gradedCartanMap (PathAlgebra.integerGrade k (Kronecker A))
        (PathAlgebra.gradedVertexProjectiveClass k (Kronecker A) tgt) =
      PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) tgt := by
  simpa using gradedCartanMap_gradedVertexProjectiveClass (A := A) k 1

/-- The categorical Betti Poincaré matrix of the minimal resolutions of the graded vertex simples
of the one-arrow path algebra is `[1, 0; q t, 1]`. -/
theorem submatrix_bettiPoincareMatrix_eq_gradedBettiMatrixA2 :
    (bettiPoincareMatrix (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A))
      (fun j => PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A) j)).submatrix
        ![src, tgt] ![src, tgt] = gradedBettiMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  refine Matrix.ext fun i j => ?_
  rw [Matrix.submatrix_apply,
    PathAlgebra.bettiPoincareMatrix_gradedVertexSimple_apply k (Kronecker A) _
      (fun l => PathAlgebra.isMinimal_gradedVertexSimpleProjectiveResolution k (Kronecker A) l)]
  fin_cases i <;> fin_cases j <;> simp [gradedBettiMatrixA2, Nat.card_eq_fintype_card]

variable [HasExt.{max u v}
  (GradedModuleCat.{max u v} (PathAlgebra.integerGrade k (Kronecker A)))]

/-- The categorical q-Euler form of the vertex-simple classes has matrix `[1, -q⁻¹; 0, 1]`.
This computes the pairing from the graded Ext groups, with their proved finiteness and support. -/
theorem gradedExtEulerForm_A2_eq :
    (fun i j : Fin 2 ↦ PathAlgebra.gradedExtEulerForm k (Kronecker A)
      (PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) (![src, tgt] i))
      (PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) (![src, tgt] j))) =
        gradedEulerMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  ext i j
  rw [PathAlgebra.gradedExtEulerForm_basis]
  fin_cases i <;> fin_cases j <;> simp [Nat.card_eq_fintype_card]

end TauCeti.Quiver.Kronecker
