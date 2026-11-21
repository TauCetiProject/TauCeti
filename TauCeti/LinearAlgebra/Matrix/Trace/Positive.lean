/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive diagonal-weighted matrix traces

Nonnegative diagonal weights give a positive functional on matrices. Strictly positive weights
make this functional faithful on squares, including for rectangular matrices. These facts allow
finite matrix representations with nonuniform weights to detect null vectors of trace forms.
-/

public section

namespace Matrix

variable {R m n : Type*} [Ring R] [PartialOrder R] [StarRing R] [IsOrderedRing R]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- A nonnegative diagonal weighting of the trace is nonnegative on positive-semidefinite
matrices. The weighted product itself need not be Hermitian. -/
theorem PosSemidef.trace_diagonal_mul_nonneg {A : Matrix n n R} (hA : A.PosSemidef)
    {w : n → R} (hw : ∀ i, 0 ≤ w i) : 0 ≤ (diagonal w * A).trace := by
  classical
  simpa only [trace, diag_apply, diagonal_mul] using
    Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦
      mul_nonneg (hw i) (hA.diag_nonneg (i := i)))

/-- Strictly positive diagonal weights give a faithful trace on matrix squares. -/
@[simp↓]
theorem trace_diagonal_mul_conjTranspose_mul_self_eq_zero_iff
    [StarOrderedRing R] [IsProperStar R] [NoZeroDivisors R] {w : n → R}
    (hw : ∀ i, 0 < w i) (A : Matrix m n R) :
    (diagonal w * (Aᴴ * A)).trace = 0 ↔ A = 0 := by
  classical
  constructor
  · intro h
    have hA := posSemidef_conjTranspose_mul_self A
    have hsum : ∑ i, w i * (Aᴴ * A) i i = 0 := by
      simpa [trace, diagonal_mul] using h
    have hdiag (i : n) : (Aᴴ * A) i i = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ mul_nonneg (hw j).le (hA.diag_nonneg (i := j)))).mp hsum i
        (Finset.mem_univ i)
      exact (mul_eq_zero.mp hi).resolve_left (hw i).ne'
    exact trace_conjTranspose_mul_self_eq_zero_iff.mp (by simp [trace, hdiag])
  · rintro rfl
    simp

end Matrix
