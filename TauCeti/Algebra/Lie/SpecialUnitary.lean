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
no topology or characteristic assumption. When its star is trivial and its additive group is
torsion-free, skewness already forces zero trace, recovering the scalar restriction of `so`.

## Main declarations

* `TauCeti.Lie.specialUnitaryMatrixLieAlgebra`: the trace-free skew-Hermitian Lie subalgebra.
* `TauCeti.Lie.mem_specialUnitaryMatrixLieAlgebra_iff`: its entrywise membership condition.
* `TauCeti.Lie.specialUnitaryMatrixLieAlgebra_self_eq_so`: the trivial-star case.

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

/-- With trivial star and no additive torsion, the trace condition follows from skewness. -/
@[simp]
theorem specialUnitaryMatrixLieAlgebra_self_eq_so [TrivialStar R]
    [IsAddTorsionFree R] :
    specialUnitaryMatrixLieAlgebra R n R = LieAlgebra.Orthogonal.so n R := by
  ext A
  change (Aᴴ = -A ∧ A.trace = 0) ↔ A ∈ LieAlgebra.Orthogonal.so n R
  rw [LieAlgebra.Orthogonal.mem_so, Matrix.conjTranspose_eq_transpose_of_trivial,
    and_iff_left_iff_imp]
  intro hA
  have h := congrArg Matrix.trace hA
  rw [Matrix.trace_transpose, Matrix.trace_neg] at h
  apply eq_of_nsmul_eq_nsmul_of_addCommute (show (2 : ℕ) ≠ 0 by decide)
    (AddCommute.all A.trace 0)
  simpa only [two_smul, add_zero] using eq_neg_iff_add_eq_zero.mp h

end TauCeti.Lie
