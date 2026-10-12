/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Scalar multiples of determinant-one matrices

Over an algebraically closed field, every invertible matrix is a determinant-one matrix
times a scalar matrix. Consequently, a subspace stable under the special linear group
and scalar matrices is stable under the general linear group.

The factorization uses Mathlib's `ProjectiveSpecialLinearGroup.toPGL_surj_of_roots`,
the surjectivity of `PSL → PGL` when units have roots.
The empty matrix index is included.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, an invertible matrix is a determinant-one
matrix times a scalar matrix. This also holds for the empty matrix index. -/
theorem exists_toGL_mul_scalar_eq (g : GL ι K) :
    ∃ (s : SpecialLinearGroup ι K) (z : Kˣ),
      SpecialLinearGroup.toGL s * scalar ι z = g := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have := h
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  | inr h =>
    have := h
    have hsurj := ProjectiveSpecialLinearGroup.toPGL_surj_of_roots
      (n := ι) (R := K) fun r => by
        obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (r : K) (Fintype.card_pos (α := ι))
        have hx0 : x ≠ 0 := by
          intro he
          exact r.ne_zero (by simpa [he, ne_of_gt (Fintype.card_pos (α := ι))] using hx.symm)
        exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx)⟩
    obtain ⟨s, hs⟩ := hsurj (ProjGenLinGroup.mk g)
    induction s using QuotientGroup.induction_on with
    | H s =>
      obtain ⟨z, hz⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hs
      exact ⟨s, z, hz⟩

end Matrix.GeneralLinearGroup
