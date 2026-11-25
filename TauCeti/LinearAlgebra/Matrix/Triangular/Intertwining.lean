/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Intertwiners of upper triangular matrices

Over a commutative semiring where nonzero factors can be cancelled, an intertwiner of two upper
triangular matrices is upper triangular if the diagonal entries satisfy the indicated separation.
This controls changes of basis between triangular forms with a fixed ordering of distinct
eigenvalues.
-/

public section

namespace Matrix

/-- Over a commutative semiring where nonzero factors can be cancelled, if upper triangular
matrices `A` and `B` satisfy `A i i ≠ B j j` whenever `j < i`, then every intertwiner `P`
satisfying `A * P = P * B` is upper triangular. -/
theorem IsUpperTriangular.isUpperTriangular_of_mul_eq_mul {ι R : Type*}
    [Fintype ι] [LinearOrder ι] [CommSemiring R] [IsRightCancelMulZero R] {A B P : Matrix ι ι R}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (hP : A * P = P * B)
    (hsep : ∀ ⦃i j⦄, j < i → A i i ≠ B j j) : P.IsUpperTriangular := by
  intro i
  -- In entry (i,j), the left product only uses later rows and the right product earlier columns.
  refine wellFounded_gt.induction (C := fun i ↦ ∀ ⦃j : ι⦄, j < i → P i j = 0) i ?_
  intro i ih j
  refine wellFounded_lt.induction (C := fun j ↦ j < i → P i j = 0) j ?_
  intro j jh hji
  have hleft : (A * P) i j = A i i * P i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hA h, zero_mul]
      · rw [ih k h (hji.trans h), mul_zero]
    · simp
  have hright : (P * B) i j = P i j * B j j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with h | h
      · rw [jh k h (h.trans hji), zero_mul]
      · rw [hB h, mul_zero]
    · simp
  have h := congr_fun₂ hP i j
  rw [hleft, hright, mul_comm (P i j)] at h
  exact (mul_eq_mul_right_iff.mp h).resolve_left (hsep hji)

end Matrix
