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

The factorization uses Mathlib's `ProjectiveSpecialLinearGroup.toPGL_surj_of_roots`
when units have roots, and `ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed` over
algebraically closed fields.
The empty matrix index is included.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]

/-- If every unit has a root of degree equal to the matrix size, an invertible matrix
is a determinant-one matrix times a scalar matrix. -/
theorem exists_toGL_mul_scalar_eq_of_roots [CommRing K] (g : GL ι K)
    (hK : ∀ r : Kˣ, ∃ z : Kˣ, z ^ Fintype.card ι = r) :
    ∃ (s : SpecialLinearGroup ι K) (z : Kˣ),
      SpecialLinearGroup.toGL s * scalar ι z = g := by
  obtain ⟨s, hs⟩ := ProjectiveSpecialLinearGroup.toPGL_surj_of_roots hK (ProjGenLinGroup.mk g)
  induction s using QuotientGroup.induction_on with
  | H s =>
    obtain ⟨z, hz⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hs
    exact ⟨s, z, hz⟩

variable [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, an invertible matrix is a determinant-one
matrix times a scalar matrix. This also holds for the empty matrix index. -/
theorem exists_toGL_mul_scalar_eq (g : GL ι K) :
    ∃ (s : SpecialLinearGroup ι K) (z : Kˣ),
      SpecialLinearGroup.toGL s * scalar ι z = g := by
  classical
  obtain ⟨s, hs⟩ := (ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed
    (n := ι) (F := K)).symm.surjective (ProjGenLinGroup.mk g)
  have hs' : ProjectiveSpecialLinearGroup.toPGL s = ProjGenLinGroup.mk g := by
    -- Both branches of Mathlib's equivalence invert the same inclusion into PGL.
    simp only [ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed,
      ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty] at hs
    split_ifs at hs <;> exact hs
  induction s using QuotientGroup.induction_on with
  | H s =>
    obtain ⟨z, hz⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hs'
    exact ⟨s, z, hz⟩

end Matrix.GeneralLinearGroup
