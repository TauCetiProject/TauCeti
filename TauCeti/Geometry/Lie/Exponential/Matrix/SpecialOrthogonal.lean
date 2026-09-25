/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Geometry.Lie.Exponential.Matrix.Compatibility
public import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Matrix exponential lines in the real special orthogonal group

This file identifies the real matrices whose exponential lines lie in the matrix special orthogonal
group. The characterization supplies canonical matrix coordinates for comparing one-parameter
subgroups of a concrete special orthogonal carrier with skew-adjoint infinitesimal actions.

## Main results

* `Matrix.exp_mem_specialOrthogonalGroup_of_mem_so` sends a skew-symmetric matrix to a special
  orthogonal exponential.
* `Matrix.forall_exp_smul_mem_specialOrthogonalGroup_iff_mem_so` characterizes the matrices whose
  entire exponential lines lie in the matrix special orthogonal group.
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Multiplying the exponential of a matrix by the exponential of its negative gives one. -/
theorem exp_neg_mul_exp (A : Matrix n n ℝ) : exp (-A) * exp A = 1 := by
  rw [← Matrix.exp_add_of_commute (-A) A (Commute.refl A).neg_left]
  simp

/-- The exponential of a real skew-symmetric matrix is orthogonal. -/
theorem exp_mem_orthogonalGroup_of_transpose_eq_neg (A : Matrix n n ℝ) (hA : Aᵀ = -A) :
    exp A ∈ orthogonalGroup n ℝ := by
  rw [mem_orthogonalGroup_iff', ← exp_transpose, hA]
  exact exp_neg_mul_exp A

/-- The exponential of a real skew-symmetric matrix has determinant one. -/
theorem det_exp_eq_one_of_transpose_eq_neg (A : Matrix n n ℝ) (hA : Aᵀ = -A) :
    (exp A).det = 1 := by
  have hsq : Set.EqOn ((fun s : ℝ => (exp (s • A)).det) ^ 2)
      ((fun _ : ℝ => (1 : ℝ)) ^ 2) Set.univ := by
    intro s _
    simp only [Pi.pow_apply]
    have hskew : (s • A)ᵀ = -(s • A) := by rw [transpose_smul, hA, smul_neg]
    have hdet := Matrix.det_of_mem_unitary
      (exp_mem_orthogonalGroup_of_transpose_eq_neg (s • A) hskew)
    simpa only [Set.mem_ofPred_eq, star_trivial, pow_two, one_mul] using hdet.1
  have hone := (isPreconnected_univ : IsPreconnected (Set.univ : Set ℝ)).eq_of_sq_eq
    (f := fun s : ℝ => (exp (s • A)).det) (g := fun _ : ℝ => (1 : ℝ))
    ((differentiable_exp_smul_const ℝ A).continuous.matrix_det.continuousOn)
    continuous_const.continuousOn hsq (by intro _ _; norm_num)
    (y := 0) (by simp) (by simp)
  simpa using hone (Set.mem_univ (1 : ℝ))

/-- The exponential of a real skew-symmetric matrix is special orthogonal. -/
theorem exp_mem_specialOrthogonalGroup_of_transpose_eq_neg
    (A : Matrix n n ℝ) (hA : Aᵀ = -A) :
    exp A ∈ specialOrthogonalGroup n ℝ := by
  rw [mem_specialOrthogonalGroup_iff]
  exact ⟨exp_mem_orthogonalGroup_of_transpose_eq_neg A hA,
    det_exp_eq_one_of_transpose_eq_neg A hA⟩

/-- The exponential of an element of the real orthogonal Lie algebra is special orthogonal. -/
theorem exp_mem_specialOrthogonalGroup_of_mem_so (A : Matrix n n ℝ)
    (hA : A ∈ LieAlgebra.Orthogonal.so n ℝ) :
    exp A ∈ specialOrthogonalGroup n ℝ := by
  rw [LieAlgebra.Orthogonal.mem_so] at hA
  exact exp_mem_specialOrthogonalGroup_of_transpose_eq_neg A hA

/-- A real matrix generates a one-parameter subgroup of the special orthogonal group exactly when
it is skew-symmetric. -/
@[simp]
theorem forall_exp_smul_mem_specialOrthogonalGroup_iff_mem_so (A : Matrix n n ℝ) :
    (∀ t : ℝ, exp (t • A) ∈ specialOrthogonalGroup n ℝ) ↔
      A ∈ LieAlgebra.Orthogonal.so n ℝ := by
  rw [LieAlgebra.Orthogonal.mem_so]
  constructor
  · intro h
    apply TauCeti.expUnitHom_injective (R := Matrix n n ℝ)
    apply ContinuousMonoidHom.ext
    intro t
    apply Units.ext
    rw [← ofAdd_toAdd t]
    simp only [TauCeti.expUnitHom_apply, TauCeti.expUnit_coe]
    have horth := (Matrix.mem_specialOrthogonalGroup_iff.mp (h (Multiplicative.toAdd t))).1
    rw [Matrix.mem_orthogonalGroup_iff'] at horth
    calc
      exp ((Multiplicative.toAdd t) • Aᵀ) =
          exp (((Multiplicative.toAdd t) • A)ᵀ) := by rw [Matrix.transpose_smul]
      _ = (exp ((Multiplicative.toAdd t) • A))ᵀ := Matrix.exp_transpose _
      _ = exp ((Multiplicative.toAdd t) • (-A)) := by
        rw [smul_neg]
        apply (Matrix.isUnit_exp ((Multiplicative.toAdd t) • A)).mul_right_cancel
        exact horth.trans (exp_neg_mul_exp _).symm
  · intro hA t
    have hskew : (t • A)ᵀ = -(t • A) := by rw [transpose_smul, hA, smul_neg]
    exact exp_mem_specialOrthogonalGroup_of_transpose_eq_neg (t • A) hskew

end Matrix
