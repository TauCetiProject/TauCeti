/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Matrix.IntegralCast
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic

/-!
# The rational form of a minuscule weight table

The raising and lowering generators named by a minuscule weight table have zero-one integer
entries, while its diagonal Cartan generators contain the integral weights. Coercing these entries
into `ℚ` gives matrices satisfying the same Serre relations: entrywise coercion is a homomorphism
of Lie rings and the adjoint action does not depend on the base ring. The resulting matrices define
a representation of the rational Serre algebra on the rational coordinate space of the index type.

## Main declarations

* `TauCeti.MinusculeWeightTable.raisingMatrixQ`, `loweringMatrixQ` and `cartanGeneratorMatrixQ`:
  the rational Chevalley generators.
* `TauCeti.MinusculeWeightTable.rationalSerreRepresentation`: the representation of the rational
  Serre presentation they define.

## Main results

* `TauCeti.MinusculeWeightTable.raisingMatrixQ_apply`, `loweringMatrixQ_apply` and
  `cartanGeneratorMatrixQ_apply`: their entry formulas.
* `TauCeti.MinusculeWeightTable.raisingMatrixQ_pow_two` and `loweringMatrixQ_pow_two`: the raising
  and lowering matrices are square-zero.
* `TauCeti.MinusculeWeightTable.Symmetry.raisingMatrixQ_submatrix` and
  `loweringMatrixQ_submatrix`: a table symmetry carries each rational raising or lowering matrix to
  the one at the image node.
* `TauCeti.MinusculeWeightTable.isSerreSystemQ`: the rational generators satisfy the Serre
  relations of the table's Cartan matrix.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

attribute [local instance 100] LieRing.ofAssociativeRing

variable {B ι : Type*} [Fintype ι] [DecidableEq ι] (T : MinusculeWeightTable B ι)

/-! ## The rational Chevalley generators -/

/-- The rational raising matrix of the `i`-th simple root. -/
noncomputable def raisingMatrixQ (i : B) : Matrix ι ι ℚ :=
  matrixIntCastLieHom ℚ (T.raisingMatrix i)

/-- The rational lowering matrix of the `i`-th simple root. -/
noncomputable def loweringMatrixQ (i : B) : Matrix ι ι ℚ :=
  matrixIntCastLieHom ℚ (T.loweringMatrix i)

/-- The rational Cartan generator matrix of the `i`-th simple coroot. -/
noncomputable def cartanGeneratorMatrixQ (i : B) : Matrix ι ι ℚ :=
  matrixIntCastLieHom ℚ (T.cartanGeneratorMatrix i)

/-- The entries of a rational raising matrix are the zero-one coefficients of the integral one. -/
@[simp]
theorem raisingMatrixQ_apply (i : B) (a b : ι) :
    T.raisingMatrixQ i a b =
      if T.weight b i = -1 ∧ a = T.reflection i b then 1 else 0 := by
  rw [raisingMatrixQ, matrixIntCastLieHom_apply, T.raisingMatrix_apply]
  split_ifs <;> norm_num

/-- The entries of a rational lowering matrix are the zero-one coefficients of the integral
one. -/
@[simp]
theorem loweringMatrixQ_apply (i : B) (a b : ι) :
    T.loweringMatrixQ i a b =
      if T.weight b i = 1 ∧ a = T.reflection i b then 1 else 0 := by
  rw [loweringMatrixQ, matrixIntCastLieHom_apply, T.loweringMatrix_apply]
  split_ifs <;> norm_num

/-- The rational Cartan generator is diagonal with the table's weights on its diagonal. -/
@[simp]
theorem cartanGeneratorMatrixQ_apply (i : B) (a b : ι) :
    T.cartanGeneratorMatrixQ i a b = if a = b then (T.weight b i : ℚ) else 0 := by
  rw [cartanGeneratorMatrixQ, matrixIntCastLieHom_apply, T.cartanGeneratorMatrix_apply]
  split_ifs <;> norm_num

/-- Every rational raising matrix is square-zero. -/
@[simp]
theorem raisingMatrixQ_pow_two (i : B) : T.raisingMatrixQ i ^ 2 = 0 := by
  rw [raisingMatrixQ, pow_two, ← matrixIntCastLieHom_mul, ← pow_two, T.raisingMatrix_pow_two,
    map_zero]

/-- Every rational lowering matrix is square-zero. -/
@[simp]
theorem loweringMatrixQ_pow_two (i : B) : T.loweringMatrixQ i ^ 2 = 0 := by
  rw [loweringMatrixQ, pow_two, ← matrixIntCastLieHom_mul, ← pow_two, T.loweringMatrix_pow_two,
    map_zero]

variable {T} in
/-- Reindexing a rational raising matrix by a table symmetry gives the rational raising matrix at
the original node. -/
@[simp]
theorem Symmetry.raisingMatrixQ_submatrix (S : T.Symmetry) (i : B) :
    (T.raisingMatrixQ (S.nodePerm i)).submatrix S.indexPerm S.indexPerm = T.raisingMatrixQ i := by
  ext a b
  rw [Matrix.submatrix_apply, raisingMatrixQ, raisingMatrixQ, matrixIntCastLieHom_apply,
    matrixIntCastLieHom_apply, S.raisingMatrix_apply]

variable {T} in
/-- Reindexing a rational lowering matrix by a table symmetry gives the rational lowering matrix at
the original node. -/
@[simp]
theorem Symmetry.loweringMatrixQ_submatrix (S : T.Symmetry) (i : B) :
    (T.loweringMatrixQ (S.nodePerm i)).submatrix S.indexPerm S.indexPerm =
      T.loweringMatrixQ i := by
  ext a b
  rw [Matrix.submatrix_apply, loweringMatrixQ, loweringMatrixQ, matrixIntCastLieHom_apply,
    matrixIntCastLieHom_apply, S.loweringMatrix_apply]

/-! ## The rational Serre presentation -/

variable [DecidableEq B]

omit [DecidableEq B] in
/-- **The rational matrices of a minuscule weight table satisfy the Serre relations of its Cartan
matrix.** -/
theorem isSerreSystemQ :
    TauCeti.IsSerreSystem ℚ T.cartanMatrix T.cartanGeneratorMatrixQ T.raisingMatrixQ
      T.loweringMatrixQ := by
  have h := T.isSerreSystem.map (matrixIntCastLieHom ℚ)
  have hH : matrixIntCastLieHom ℚ ∘ T.cartanGeneratorMatrix = T.cartanGeneratorMatrixQ := rfl
  have hE : matrixIntCastLieHom ℚ ∘ T.raisingMatrix = T.raisingMatrixQ := rfl
  have hF : matrixIntCastLieHom ℚ ∘ T.loweringMatrix = T.loweringMatrixQ := rfl
  rw [hH, hE, hF] at h
  exact h.changeScalars

/-- The rational representation of the Serre presentation named by a minuscule weight table. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ T.cartanMatrix →ₗ⁅ℚ⁆ Matrix ι ι ℚ :=
  TauCeti.serreLift T.isSerreSystemQ

/-- The rational representation sends a Cartan generator to its diagonal weight matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreH (i : B) :
    T.rationalSerreRepresentation (TauCeti.serreH ℚ T.cartanMatrix i) =
      T.cartanGeneratorMatrixQ i :=
  TauCeti.serreLift_serreH T.isSerreSystemQ i

/-- The rational representation sends a positive generator to its raising matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreE (i : B) :
    T.rationalSerreRepresentation (TauCeti.serreE ℚ T.cartanMatrix i) = T.raisingMatrixQ i :=
  TauCeti.serreLift_serreE T.isSerreSystemQ i

/-- The rational representation sends a negative generator to its lowering matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreF (i : B) :
    T.rationalSerreRepresentation (TauCeti.serreF ℚ T.cartanMatrix i) = T.loweringMatrixQ i :=
  TauCeti.serreLift_serreF T.isSerreSystemQ i

end TauCeti.MinusculeWeightTable
