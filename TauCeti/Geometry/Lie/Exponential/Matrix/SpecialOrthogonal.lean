/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Basic.Real.Star
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Exponential.OneParameter
public import TauCeti.Geometry.Lie.Exponential.Unitary

/-!
# Matrix exponential lines in the real special orthogonal group

This file identifies the real matrices whose exponential lines lie in the matrix special orthogonal
group. The characterization supplies canonical matrix coordinates for comparing one-parameter
subgroups of a concrete special orthogonal carrier with skew-adjoint infinitesimal actions.

The orthogonal group is the unitary group of `Matrix n n ℝ`, so the orthogonal statements are the
Banach star algebra results `exp_mem_unitary_of_mem_skewAdjoint` and
`TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint` read at that algebra; only the
determinant condition cutting out the special orthogonal group is proved from scratch here.

## Main results

* `Matrix.exp_mem_specialOrthogonalGroup_of_mem_so` sends a skew-symmetric matrix to a special
  orthogonal exponential.
* `Matrix.forall_exp_smul_mem_orthogonalGroup_iff_mem_so` characterizes the matrices whose entire
  exponential lines lie in the matrix orthogonal group.
* `Matrix.forall_exp_smul_mem_specialOrthogonalGroup_iff_mem_so` characterizes the matrices whose
  entire exponential lines lie in the matrix special orthogonal group.
-/

public section

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing
-- Select the matrix topology underlying the operator norm, and continuity of the star for it.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

/-- The matrix exponential of an element of the real orthogonal Lie algebra is orthogonal.  Over
`ℝ` skew-symmetric is skew-adjoint and the orthogonal group is the unitary group, so this is
Mathlib's `exp_mem_unitary_of_mem_skewAdjoint`. -/
theorem exp_mem_orthogonalGroup_of_mem_so (A : Matrix n n ℝ)
    (hA : A ∈ LieAlgebra.Orthogonal.so n ℝ) :
    exp A ∈ orthogonalGroup n ℝ :=
  exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.mem_iff.mpr ((LieAlgebra.Orthogonal.mem_so n ℝ A).mp hA))

/-- The exponential of a real skew-symmetric matrix has determinant one. -/
theorem det_exp_eq_one_of_transpose_eq_neg (A : Matrix n n ℝ) (hA : Aᵀ = -A) :
    (exp A).det = 1 := by
  have hAso : A ∈ LieAlgebra.Orthogonal.so n ℝ :=
    (LieAlgebra.Orthogonal.mem_so n ℝ A).mpr hA
  have hsq : Set.EqOn ((fun s : ℝ => (exp (s • A)).det) ^ 2)
      ((fun _ : ℝ => (1 : ℝ)) ^ 2) Set.univ := by
    intro s _
    simp only [Pi.pow_apply]
    have hsso := (LieAlgebra.Orthogonal.so n ℝ).smul_mem s hAso
    have hdet := Matrix.det_of_mem_unitary
      (exp_mem_orthogonalGroup_of_mem_so (s • A) hsso)
    calc
      (exp (s • A)).det ^ 2 = star (exp (s • A)).det * (exp (s • A)).det := by
        rw [star_trivial, pow_two]
      _ = 1 := Unitary.star_mul_self_of_mem hdet
      _ = (1 : ℝ) ^ 2 := by norm_num
  have hone := (isPreconnected_univ : IsPreconnected (Set.univ : Set ℝ)).eq_of_sq_eq
    (f := fun s : ℝ => (exp (s • A)).det) (g := fun _ : ℝ => (1 : ℝ))
    ((differentiable_exp_smul_const ℝ A).continuous.matrix_det.continuousOn)
    continuous_const.continuousOn hsq (by intro _ _; norm_num)
    (y := 0) (by simp) (by simp)
  simpa using hone (Set.mem_univ (1 : ℝ))

/-- The exponential of an element of the real orthogonal Lie algebra is special orthogonal. -/
theorem exp_mem_specialOrthogonalGroup_of_mem_so (A : Matrix n n ℝ)
    (hA : A ∈ LieAlgebra.Orthogonal.so n ℝ) :
    exp A ∈ specialOrthogonalGroup n ℝ := by
  rw [mem_specialOrthogonalGroup_iff]
  exact ⟨exp_mem_orthogonalGroup_of_mem_so A hA,
    det_exp_eq_one_of_transpose_eq_neg A ((LieAlgebra.Orthogonal.mem_so n ℝ A).mp hA)⟩

/-- A real matrix generates a one-parameter subgroup of the orthogonal group exactly when it is
skew-symmetric.  This is `TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint` at the algebra
`Matrix n n ℝ`, where the unitary group is the orthogonal group and skew-adjoint is
skew-symmetric. -/
@[simp]
theorem forall_exp_smul_mem_orthogonalGroup_iff_mem_so (A : Matrix n n ℝ) :
    (∀ t : ℝ, exp (t • A) ∈ orthogonalGroup n ℝ) ↔
      A ∈ LieAlgebra.Orthogonal.so n ℝ :=
  (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint A).trans
    (by rw [skewAdjoint.mem_iff, LieAlgebra.Orthogonal.mem_so]; rfl)

/-- A real matrix generates a one-parameter subgroup of the special orthogonal group exactly when
it is skew-symmetric. -/
@[simp]
theorem forall_exp_smul_mem_specialOrthogonalGroup_iff_mem_so (A : Matrix n n ℝ) :
    (∀ t : ℝ, exp (t • A) ∈ specialOrthogonalGroup n ℝ) ↔
      A ∈ LieAlgebra.Orthogonal.so n ℝ := by
  constructor
  · intro h
    exact (forall_exp_smul_mem_orthogonalGroup_iff_mem_so A).mp fun t =>
      (mem_specialOrthogonalGroup_iff.mp (h t)).1
  · intro hA t
    exact exp_mem_specialOrthogonalGroup_of_mem_so (t • A)
      ((LieAlgebra.Orthogonal.so n ℝ).smul_mem t hA)

end Matrix
