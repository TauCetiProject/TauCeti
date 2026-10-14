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
    [AddCommGroup M] [Module K M] (A : Matrix ι ι K) {v : ι → M}
    (hv : ∀ i, ∑ j, A i j • v j = 0) (k : ι) : A.det • v k = 0 := by
  calc A.det • v k = ∑ j, (A.adjugate * A) k j • v j := by
        simp [adjugate_mul, smul_apply, one_apply, ite_smul]
    _ = ∑ i, A.adjugate k i • ∑ j, A i j • v j := by
        simp only [mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = 0 := by simp [hv]

end Matrix
