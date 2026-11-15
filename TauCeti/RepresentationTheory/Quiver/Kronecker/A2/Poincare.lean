/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.A2.Graded
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.Poincare

/-!
# Linear resolutions and Poincaré matrices of the one-arrow quiver

Give the path algebra of `1 ⟶ 2` its path-length grading and order the vertices source first
(`![src, tgt]`). This file checks the linear-resolution, Poincaré-matrix, and Koszul
Cartan--Poincaré conventions on that smallest nontrivial directed quiver:

* In `K₀^gr(proj kQ)`, the source simple `S₁` has linear projective resolution
  `0 ⟶ P₂{1} ⟶ P₁ ⟶ S₁ ⟶ 0`, so `[P₀(S₁)] = [P₁]` and `[P₁(S₁)] = q [P₂]`; the target simple `S₂`
  is already projective (`P₀(S₂) = P₂`, `P₁(S₂) = 0`). With projectives in the rows and resolved
  simples in the columns, the degree-`0` and degree-`1` resolution-term coordinate matrices are
  `1` and `[0, 0; q, 0]`, whose alternating sum `1 - [0, 0; q, 0] = [1, 0; -q, 1]` inverts the
  graded Cartan matrix `C = [1, 0; q, 1]`.
* The diagonal Ext Poincaré matrix is `P(X) = [1, X; 0, 1]`, and the full bigraded Ext Poincaré
  matrix is `[1, (1, 1); 0, 1]`. Every entry is diagonally supported, its Alexander- and
  Maslov-graded Euler characteristics coincide at `P(-q) = [1, -q; 0, 1] = Ē`, and
  `Cᵀ P(-q) = [1, q; 0, 1] [1, -q; 0, 1] = 1`.
* Specializing `P(X)` at `X = -1` recovers the ordinary Ringel Euler matrix `[1, -1; 0, 1]`.

## Main definitions and results

* `TauCeti.Quiver.Kronecker.diagonalExtPoincareMatrixA2` and
  `TauCeti.Quiver.Kronecker.bigradedExtPoincareMatrixA2`: the explicit `2 × 2` diagonal and
  bigraded Ext Poincaré matrices of `1 ⟶ 2` in source-first order.
* `TauCeti.Quiver.Kronecker.laurentK0_finiteProjectiveTerm_A2_src_one`,
  `TauCeti.Quiver.Kronecker.laurentK0_finiteProjectiveTerm_A2_tgt_one`, and
  `TauCeti.Quiver.Kronecker.repr_finiteProjectiveTerm_A2_one_matrix`: Grothendieck classes and
  projective-row / simple-column coordinate matrices of the linear resolution terms.
* `TauCeti.Quiver.Kronecker.submatrix_diagonalExtPoincareMatrix_eq_diagonalExtPoincareMatrixA2`
  and
  `TauCeti.Quiver.Kronecker.submatrix_bigradedExtPoincareMatrix_eq_bigradedExtPoincareMatrixA2`:
  identification of the categorical Poincaré matrices of `Kronecker A` (`[Unique A]`) with the
  explicit `2 × 2` matrices.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2.
-/

public section

noncomputable section

namespace TauCeti.Quiver.Kronecker

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe u v t

/-! ### Explicit `2 × 2` Poincaré matrices and algebraic checks -/

/-- The diagonal Ext Poincaré matrix `[1, X; 0, 1]` of the one-arrow quiver `1 ⟶ 2`, in
source-first vertex order. -/
def diagonalExtPoincareMatrixA2 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  !![1, Polynomial.X; 0, 1]

/-- Entries of `diagonalExtPoincareMatrixA2`. -/
@[simp]
theorem diagonalExtPoincareMatrixA2_apply (i j : Fin 2) :
    diagonalExtPoincareMatrixA2 i j = !![1, Polynomial.X; 0, 1] i j := by
  rw [diagonalExtPoincareMatrixA2]

/-- The full bigraded Ext Poincaré matrix `[1, (1, 1); 0, 1]` of the one-arrow quiver `1 ⟶ 2`, in
source-first vertex order. -/
def bigradedExtPoincareMatrixA2 : Matrix (Fin 2) (Fin 2) Bigraded.Series :=
  !![1, AddMonoidAlgebra.single (1, 1) 1; 0, 1]

/-- Entries of `bigradedExtPoincareMatrixA2`. -/
@[simp]
theorem bigradedExtPoincareMatrixA2_apply (i j : Fin 2) :
    bigradedExtPoincareMatrixA2 i j = !![1, AddMonoidAlgebra.single (1, 1) 1; 0, 1] i j := by
  rw [bigradedExtPoincareMatrixA2]

/-- Every entry of `bigradedExtPoincareMatrixA2` is supported on the diagonal `m = a`. -/
theorem isDiagonal_bigradedExtPoincareMatrixA2 (i j : Fin 2) :
    Bigraded.IsDiagonal (bigradedExtPoincareMatrixA2 i j) := by
  rw [Bigraded.isDiagonal_iff]
  intro m a hma
  fin_cases i <;> fin_cases j <;>
    simp [AddMonoidAlgebra.one_def, Finsupp.single_apply, Prod.ext_iff] <;>
    omega

/-- Evaluating `diagonalExtPoincareMatrixA2` at `-q` gives the conjugate (`q ↦ q⁻¹`) of the
q-Euler matrix `[1, -q⁻¹; 0, 1]`, namely `[1, -q; 0, 1]`. -/
@[simp]
theorem map_eval₂_neg_T_diagonalExtPoincareMatrixA2 :
    diagonalExtPoincareMatrixA2.map (Polynomial.eval₂ C (-T 1)) =
      gradedEulerMatrixA2.map (invert (R := ℤ)) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

/-- **Koszul Cartan--Poincaré identity on `1 ⟶ 2`**: `Cᵀ P(-q) = 1`. -/
theorem gradedCartanMatrixA2_transpose_mul_diagonalExtPoincareMatrixA2_map :
    gradedCartanMatrixA2ᵀ *
      diagonalExtPoincareMatrixA2.map (Polynomial.eval₂ C (-T 1)) = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Two-sided form of the Koszul Cartan--Poincaré identity on `1 ⟶ 2`: `P(-q) Cᵀ = 1`. -/
theorem diagonalExtPoincareMatrixA2_map_mul_gradedCartanMatrixA2_transpose :
    diagonalExtPoincareMatrixA2.map (Polynomial.eval₂ C (-T 1)) *
      gradedCartanMatrixA2ᵀ = 1 :=
  mul_eq_one_comm.mp gradedCartanMatrixA2_transpose_mul_diagonalExtPoincareMatrixA2_map

/-- Applying `Bigraded.euler` entrywise to `bigradedExtPoincareMatrixA2` recovers `P(-q)`. -/
@[simp]
theorem map_euler_bigradedExtPoincareMatrixA2 :
    bigradedExtPoincareMatrixA2.map Bigraded.euler =
      diagonalExtPoincareMatrixA2.map (Polynomial.eval₂ C (-T 1)) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

/-- Applying `Bigraded.maslovEuler` entrywise to `bigradedExtPoincareMatrixA2` agrees with
`Bigraded.euler` and equals `P(-q)`. -/
@[simp]
theorem map_maslovEuler_bigradedExtPoincareMatrixA2 :
    bigradedExtPoincareMatrixA2.map Bigraded.maslovEuler =
      diagonalExtPoincareMatrixA2.map (Polynomial.eval₂ C (-T 1)) := by
  rw [← map_euler_bigradedExtPoincareMatrixA2]
  refine Matrix.ext fun i j => ((Bigraded.euler_eq_maslovEuler_iff_isDiagonal _
    (Or.inl fun m a hlt =>
      (Bigraded.isDiagonal_iff _).mp
        (isDiagonal_bigradedExtPoincareMatrixA2 i j) m a hlt.ne')).mpr
    (isDiagonal_bigradedExtPoincareMatrixA2 i j)).symm

/-- Evaluating `diagonalExtPoincareMatrixA2` at `X = -1` recovers the ordinary Ringel Euler matrix
`[1, -1; 0, 1]`. -/
@[simp]
theorem map_eval_neg_one_diagonalExtPoincareMatrixA2 :
    diagonalExtPoincareMatrixA2.map (Polynomial.eval (-1)) = eulerMatrixA2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ### Linear resolution terms in `K₀^gr(proj kQ)` for `Kronecker A` -/

section ResolutionClasses

attribute [local instance] PathAlgebra.integerGradedAlgebra

variable {A : Type v} [Unique A] (k : Type u)

section CommRing

variable [CommRing k]

/-- In `K₀^gr(proj kQ)` for `1 ⟶ 2`, the degree-`1` resolution term of the source simple `S₁` has
class `q • [P₂]`: the shift exponent is `+1`. -/
theorem laurentK0_finiteProjectiveTerm_A2_src_one :
    letI : Fintype A := Unique.fintype
    LaurentK0.of.{max u v}
        (gradedFiniteProjectiveModulesExactStructure
          (PathAlgebra.integerGrade k (Kronecker A)))
        ((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
          src).finiteProjectiveTerm 1) =
      (T 1 : LaurentPolynomial ℤ) •
        PathAlgebra.gradedVertexProjectiveClass k (Kronecker A) tgt := by
  let _ : Fintype A := Unique.fintype
  rw [PathAlgebra.laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_one_eq_sum,
    sum_univ]
  simp [Nat.card_eq_fintype_card]

/-- In `K₀^gr(proj kQ)` for `1 ⟶ 2`, the degree-`1` resolution term of the target simple `S₂` has
class `0`: the sink vertex has no outgoing arrows. -/
theorem laurentK0_finiteProjectiveTerm_A2_tgt_one :
    letI : Fintype A := Unique.fintype
    LaurentK0.of.{max u v}
        (gradedFiniteProjectiveModulesExactStructure
          (PathAlgebra.integerGrade k (Kronecker A)))
        ((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
          tgt).finiteProjectiveTerm 1) = 0 := by
  let _ : Fintype A := Unique.fintype
  rw [PathAlgebra.laurentK0_finiteProjectiveTerm_gradedVertexSimpleProjectiveResolution_one_eq_sum,
    sum_univ]
  simp [Nat.card_eq_fintype_card]

end CommRing

section Field

variable [Field k]

/-- With projectives in the rows (`![src, tgt] i`) and resolved simples in the columns
(`![src, tgt] j`), the homological-degree-`0` resolution-term coordinates form the identity
matrix. -/
theorem repr_finiteProjectiveTerm_A2_zero_matrix :
    letI : Fintype A := Unique.fintype
    (Matrix.of fun i j : Fin 2 =>
      (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A)).repr
        (LaurentK0.of.{max u v} _
          ((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
            (![src, tgt] j)).finiteProjectiveTerm 0))
        (![src, tgt] i)) = 1 := by
  let _ : Fintype A := Unique.fintype
  refine Matrix.ext fun i j => ?_
  rw [Matrix.of_apply,
    PathAlgebra.gradedVertexProjectiveClassBasis_repr_finiteProjectiveTerm_zero]
  fin_cases i <;> fin_cases j <;> simp

/-- With projectives in the rows (`![src, tgt] i`) and resolved simples in the columns
(`![src, tgt] j`), the homological-degree-`1` resolution-term coordinates form `[0, 0; q, 0]`:
hence `∑ₙ (-1)ⁿ [Pₙ(Sⱼ)]` has matrix `1 - [0, 0; q, 0] = [1, 0; -q, 1] = C⁻¹`. -/
theorem repr_finiteProjectiveTerm_A2_one_matrix :
    letI : Fintype A := Unique.fintype
    (Matrix.of fun i j : Fin 2 =>
      (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A)).repr
        (LaurentK0.of.{max u v} _
          ((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
            (![src, tgt] j)).finiteProjectiveTerm 1))
        (![src, tgt] i)) = !![0, 0; T 1, 0] := by
  let _ : Fintype A := Unique.fintype
  refine Matrix.ext fun i j => ?_
  rw [Matrix.of_apply,
    PathAlgebra.gradedVertexProjectiveClassBasis_repr_finiteProjectiveTerm_one]
  fin_cases i <;> fin_cases j <;> simp [Nat.card_eq_fintype_card]

/-! ### Categorical Poincaré matrices of `Kronecker A` -/

variable [HasExt.{t}
  (GradedModuleCat.{max u v} (PathAlgebra.integerGrade k (Kronecker A)))]

/-- Complete bigraded Ext dimensions between the source-first graded vertex simples of `1 ⟶ 2`. -/
theorem finrank_gradedExt_gradedVertexSimple_A2 (i j : Fin 2) (n : ℕ) (p : ℤ) :
    Module.finrank k
        (GradedExt.{t}
          (GradedModuleCat.shift (PathAlgebra.integerGrade k (Kronecker A)))
          (PathAlgebra.gradedVertexSimple k (Kronecker A) (![src, tgt] i))
          (PathAlgebra.gradedVertexSimple k (Kronecker A) (![src, tgt] j)) n p) =
      if n = 0 ∧ p = 0 then (if i = j then 1 else 0)
      else if n = 1 ∧ p = 1 then (if i = 0 ∧ j = 1 then 1 else 0)
      else 0 := by
  let _ : Fintype A := Unique.fintype
  rw [PathAlgebra.finrank_gradedExt_gradedVertexSimple]
  fin_cases i <;> fin_cases j <;> simp [Nat.card_eq_fintype_card]

/-- For any truncation bound `b ≥ 2`, the categorical diagonal Ext Poincaré matrix of the
one-arrow path algebra in source-first order is `[1, X; 0, 1]`. -/
theorem submatrix_diagonalExtPoincareMatrix_eq_diagonalExtPoincareMatrixA2
    {b : ℕ} (hb : 2 ≤ b) :
    (diagonalExtPoincareMatrix.{t} k
        (PathAlgebra.gradedVertexSimple k (Kronecker A)) b).submatrix
      ![src, tgt] ![src, tgt] = diagonalExtPoincareMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  ext i j
  rw [Matrix.submatrix_apply, diagonalExtPoincareMatrix_apply,
    PathAlgebra.diagonalExtPoincarePolynomial_gradedVertexSimple k (Kronecker A) _ _ hb]
  fin_cases i <;> fin_cases j <;> simp [Nat.card_eq_fintype_card]

/-- For any truncation bound `b ≥ 2`, the categorical full bigraded Ext Poincaré matrix of the
one-arrow path algebra in source-first order is `[1, (1, 1); 0, 1]`. -/
theorem submatrix_bigradedExtPoincareMatrix_eq_bigradedExtPoincareMatrixA2
    (h : ∀ x y : Kronecker A,
      IsGradedExtInternallyFinite.{t} k
        (GradedModuleCat.shift (PathAlgebra.integerGrade k (Kronecker A)))
        (PathAlgebra.gradedVertexSimple k (Kronecker A) x)
        (PathAlgebra.gradedVertexSimple k (Kronecker A) y))
    {b : ℕ} (hb : 2 ≤ b) :
    (bigradedExtPoincareMatrix
        (PathAlgebra.gradedVertexSimple k (Kronecker A)) h b).submatrix
      ![src, tgt] ![src, tgt] = bigradedExtPoincareMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  ext i j
  rw [Matrix.submatrix_apply, bigradedExtPoincareMatrix_apply,
    PathAlgebra.bigradedExtPoincareSeries_gradedVertexSimple k (Kronecker A) _ _ _ hb]
  fin_cases i <;> fin_cases j <;> simp [Nat.card_eq_fintype_card]

end Field

end ResolutionClasses

end TauCeti.Quiver.Kronecker
