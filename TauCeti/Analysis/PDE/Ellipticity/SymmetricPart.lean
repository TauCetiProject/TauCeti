/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.Trace.TransposeMul

/-!
# The symmetric part of a coefficient matrix

This file defines the symmetric part `S = (A + Aᵀ) / 2` of a real coefficient matrix `A`, used
to reduce divergence-form operators to symmetric coefficients.

## Main declarations

* `TauCeti.PDE.coefficientSymmetricPart`: the symmetric part `S = (A + Aᵀ) / 2` of `A`, linear
  (`_zero`, `_add`, `_smul`, `_neg`, `_sum`), transpose-invariant (`_transpose`) and commuting
  with congruences `A ↦ O A Oᵀ` (`_mul_mul_transpose`). `S` and `tr (Sᵀ S)` vanish iff `Aᵀ = -A`
  (`_eq_zero_iff`, `TauCeti.PDE.trace_transpose_coefficientSymmetricPart_mul_self_eq_zero_iff`).
-/

public section

namespace TauCeti

namespace PDE

open Matrix

section SymmetricPart

variable {n : Type*}

/-- The symmetric part `(A + Aᵀ) / 2` of a coefficient matrix.

For energy estimates the diagonal quadratic form of `A` agrees with that of
`coefficientSymmetricPart A`, while the resulting matrix is symmetric. This is the
finite-dimensional bookkeeping needed before the integrated energy form is specialized to
self-adjoint elliptic operators. -/
noncomputable def coefficientSymmetricPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

lemma coefficientSymmetricPart_def (A : Matrix n n ℝ) :
    coefficientSymmetricPart A = (1 / 2 : ℝ) • (A + Aᵀ) := (rfl)

/-- The symmetric part of a coefficient matrix is symmetric. -/
lemma coefficientSymmetricPart_isSymm (A : Matrix n n ℝ) : (coefficientSymmetricPart A).IsSymm :=
  (isSymm_add_transpose_self A).smul (1 / 2 : ℝ)

/-- The entries of the symmetric part are the averages of opposite entries. -/
@[simp]
lemma coefficientSymmetricPart_apply (A : Matrix n n ℝ) (i j : n) :
    coefficientSymmetricPart A i j = (A i j + A j i) / 2 := by
  simp [coefficientSymmetricPart, div_eq_mul_inv, mul_comm]

/-- A symmetric coefficient matrix is unchanged by taking its symmetric part. -/
@[simp]
lemma coefficientSymmetricPart_eq_self_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) :
    coefficientSymmetricPart A = A := by
  ext i j
  rw [coefficientSymmetricPart_apply, hA.apply i j]
  ring

@[simp]
lemma coefficientSymmetricPart_transpose (A : Matrix n n ℝ) :
    coefficientSymmetricPart Aᵀ = coefficientSymmetricPart A := by
  rw [coefficientSymmetricPart_def, coefficientSymmetricPart_def, transpose_transpose, add_comm]

lemma coefficientSymmetricPart_zero : coefficientSymmetricPart (0 : Matrix n n ℝ) = 0 := by
  rw [coefficientSymmetricPart_def, transpose_zero, add_zero, smul_zero]

lemma coefficientSymmetricPart_add (A B : Matrix n n ℝ) :
    coefficientSymmetricPart (A + B) = coefficientSymmetricPart A + coefficientSymmetricPart B := by
  rw [coefficientSymmetricPart_def, coefficientSymmetricPart_def, coefficientSymmetricPart_def,
    transpose_add, add_add_add_comm, smul_add]

lemma coefficientSymmetricPart_smul (c : ℝ) (A : Matrix n n ℝ) :
    coefficientSymmetricPart (c • A) = c • coefficientSymmetricPart A := by
  rw [coefficientSymmetricPart_def, coefficientSymmetricPart_def, transpose_smul, ← smul_add,
    smul_comm]

lemma coefficientSymmetricPart_neg (A : Matrix n n ℝ) :
    coefficientSymmetricPart (-A) = -coefficientSymmetricPart A := by
  rw [← neg_one_smul ℝ A, coefficientSymmetricPart_smul, neg_one_smul]

lemma coefficientSymmetricPart_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℝ) :
    coefficientSymmetricPart (∑ a ∈ s, A a) = ∑ a ∈ s, coefficientSymmetricPart (A a) :=
  map_sum (AddMonoidHom.mk' coefficientSymmetricPart coefficientSymmetricPart_add) A s

/-- The symmetric part vanishes exactly on skew-symmetric matrices. -/
lemma coefficientSymmetricPart_eq_zero_iff {A : Matrix n n ℝ} :
    coefficientSymmetricPart A = 0 ↔ Aᵀ = -A := by
  rw [coefficientSymmetricPart_def, smul_eq_zero, or_iff_right (by norm_num),
    add_eq_zero_iff_eq_neg']

/-- The squared symmetric part `e(A) : e(A)` vanishes exactly on skew-symmetric matrices. -/
lemma trace_transpose_coefficientSymmetricPart_mul_self_eq_zero_iff [Fintype n] {A : Matrix n n ℝ} :
    ((coefficientSymmetricPart A)ᵀ * coefficientSymmetricPart A).trace = 0 ↔ Aᵀ = -A := by
  rw [trace_transpose_mul_self_eq_zero_iff, coefficientSymmetricPart_eq_zero_iff]

/-- Taking the symmetric part commutes with every congruence `A ↦ O A Oᵀ`. -/
lemma coefficientSymmetricPart_mul_mul_transpose {m : Type*} [Fintype n] (O : Matrix m n ℝ)
    (A : Matrix n n ℝ) :
    coefficientSymmetricPart (O * A * Oᵀ) = O * coefficientSymmetricPart A * Oᵀ := by
  simp [coefficientSymmetricPart_def, transpose_mul, Matrix.mul_assoc, Matrix.mul_add,
    Matrix.add_mul]

end SymmetricPart

end PDE

end TauCeti
