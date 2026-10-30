/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrix adjugation

This file records dimension-independent consequences of the standard matrix adjugate identities.

The adjugate identity `adj A * A = det A • 1` also acts on vectors with entries in a module: if a
family `v` of elements of a `K`-module satisfies the linear relations `∑ⱼ A i j • v j = 0`, then
`det A` kills every `v k` (`Matrix.det_smul_eq_zero_of_sum_smul_eq_zero`). This is the
determinant trick behind the Cayley–Hamilton and Nakayama arguments for finitely generated modules.

The same identity cancels a square matrix `A` with `A * B = c • 1` for a non-zero-divisor `c`, so
that `B * A = c • 1` as well (`Matrix.mul_eq_smul_one_comm`). For `c = 1` this is
`mul_eq_one_comm`; for general `c` it compares a form with its `c`-scaled dual, whose Gram matrix
is `c` times the inverse Gram matrix.
-/

public section

namespace Matrix

variable {K : Type*} [CommRing K]

/-- For a square matrix with finite indices, the left adjugate equation is equivalent to
determinant one. -/
@[simp]
theorem adjugate_mul_self_eq_one_iff_det_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) :
    Matrix.adjugate A * A = 1 ↔ A.det = 1 := by
  cases isEmpty_or_nonempty n with
  | inl _ =>
      constructor
      · intro _
        simp
      · intro _
        exact Subsingleton.elim _ _
  | inr _ =>
      constructor
      · intro h
        rw [Matrix.adjugate_mul] at h
        let i : n := Classical.choice (inferInstance : Nonempty n)
        have hii := congrArg (fun M : Matrix n n K ↦ M i i) h
        simpa using hii
      · intro h
        rw [Matrix.adjugate_mul, h, one_smul]

/-- **The determinant trick.** If a family `v` of elements of a module satisfies the linear
relations `∑ⱼ A i j • v j = 0` for every `i`, then `det A` kills every member of the family. -/
theorem det_smul_eq_zero_of_sum_smul_eq_zero {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] [Module K M] (A : Matrix ι ι K) {v : ι → M}
    (hv : ∀ i, ∑ j, A i j • v j = 0) (k : ι) : A.det • v k = 0 := by
  calc A.det • v k = ∑ j, (A.adjugate * A) k j • v j := by
        simp [adjugate_mul, smul_apply, one_apply, ite_smul]
    _ = ∑ i, A.adjugate k i • ∑ j, A i j • v j := by
        simp only [mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = 0 := by simp [hv]

/-- **Inverses up to a scalar commute.** If `A * B = c • 1` for square matrices over a commutative
ring and a non-zero-divisor `c`, then `B * A = c • 1`. -/
theorem mul_eq_smul_one_comm {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n K} {c : K}
    (hc : c ∈ nonZeroDivisors K) : A * B = c • 1 ↔ B * A = c • 1 := by
  suffices key : ∀ A B : Matrix n n K, A * B = c • 1 → B * A = c • 1 from ⟨key A B, key B A⟩
  intro A B h
  -- `det A` divides a power of `c`, so it is a non-zero-divisor and cancels `A` on the left.
  have hdet : A.det ∈ nonZeroDivisors K := by
    have := congrArg det h
    rw [det_mul, det_smul, det_one, mul_one] at this
    exact (mul_mem_nonZeroDivisors.mp (this ▸ pow_mem hc _)).1
  refine (isRegular_of_isLeftRegular_det
    (isRegular_iff_mem_nonZeroDivisors.mpr hdet).left).left ?_
  change A * (B * A) = A * (c • 1)
  rw [← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

end Matrix
