/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Trace-free skew-Hermitian matrix Lie algebras

The skew-Hermitian matrices of trace zero form a Lie algebra over any commutative scalar
ring fixed by the involution. The coefficient ring may be any commutative star ring, with
no topology or characteristic assumption. When the coefficient ring has trivial star and its
additive group is torsion-free, skewness forces zero trace. Taking the coefficient ring itself
as scalars then recovers `so`.

## Main declarations

* `TauCeti.Lie.specialUnitaryMatrixLieAlgebra`: the trace-free skew-Hermitian Lie subalgebra.
* `TauCeti.Lie.mem_specialUnitaryMatrixLieAlgebra_iff`:
  the skew-Hermitian and trace-zero membership condition.
* `TauCeti.Lie.specialUnitaryMatrixLieAlgebra_self_eq_so`:
  the trivial-star case over the coefficient ring itself.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222
  (2015), Proposition 3.24, for the real and complex matrix Lie algebras.
* Mathlib, `Algebra/Lie/Classical.lean`, for the special linear and orthogonal Lie algebras.
-/

public section

open scoped Matrix

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R₀ : Type*) (n : Type*) (R : Type*) [CommRing R₀] [Star R₀] [TrivialStar R₀]
  [Fintype n] [DecidableEq n] [CommRing R] [StarRing R] [Algebra R₀ R] [StarModule R₀ R]

/-- The trace-free skew-Hermitian matrices, over scalars fixed by the involution. -/
def specialUnitaryMatrixLieAlgebra : LieSubalgebra R₀ (Matrix n n R) where
  carrier := {A | Aᴴ = -A ∧ A.trace = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    simp only [Set.mem_ofPred_eq, Matrix.conjTranspose_add, hA.1, hB.1, neg_add,
      Matrix.trace_add, hA.2, hB.2, add_zero, and_self]
  smul_mem' := by
    intro c A hA
    simp only [Set.mem_ofPred_eq, Matrix.conjTranspose_smul, star_trivial, hA.1,
      smul_neg, Matrix.trace_smul, hA.2, smul_zero, and_self]
  lie_mem' := by
    intro A B hA hB
    constructor
    · simp only [Ring.lie_def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        hA.1, hB.1, neg_mul_neg]
      simp only [neg_sub]
    · exact LieAlgebra.matrix_trace_commutator_zero n R A B

variable {n R} in
/-- Membership is exactly skew-Hermitianity and trace zero. -/
@[simp]
theorem mem_specialUnitaryMatrixLieAlgebra_iff (A : Matrix n n R) :
    A ∈ specialUnitaryMatrixLieAlgebra R₀ n R ↔ Aᴴ = -A ∧ A.trace = 0 := Iff.rfl

/-- Over the coefficient ring itself, trivial star and no additive torsion identify the
trace-free skew-Hermitian Lie algebra with the orthogonal Lie algebra. -/
@[simp]
theorem specialUnitaryMatrixLieAlgebra_self_eq_so [TrivialStar R]
    [IsAddTorsionFree R] :
    specialUnitaryMatrixLieAlgebra R n R = LieAlgebra.Orthogonal.so n R := by
  ext A
  rw [mem_specialUnitaryMatrixLieAlgebra_iff, LieAlgebra.Orthogonal.mem_so,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    and_iff_left_iff_imp]
  intro hA
  have h := congrArg Matrix.trace hA
  rwa [Matrix.trace_transpose, Matrix.trace_neg, self_eq_neg] at h

end TauCeti.Lie
