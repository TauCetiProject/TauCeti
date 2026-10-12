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

end Matrix
