/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import Mathlib.Tactic.NormNum.IsSquare

/-!
# The determinant obstruction to lifting a projective matrix to SL

The determinant of a projective matrix is well defined modulo nth powers of units, where n
is the matrix size. Its kernel is precisely the image of SL. For nonempty matrices the resulting
map is surjective, and identifies the quotient of PGL by that image with units modulo nth powers.
All these statements hold over a commutative ring, for the pointwise quotient defining PGL.

In size two this detects the distinction between the full adjoint torus and the image of the
simply connected torus: the class of diag(a,1) lifts to SL exactly when a is a square unit.
In particular diag(2,1) over the rationals does not lift. Thus a group-scheme central quotient
need not be a surjection on rational points.

The construction uses Mathlib's `Matrix.ProjGenLinGroup.lift`, the scalar criterion
`Matrix.ProjGenLinGroup.mk_eq_mk_iff`, and the first isomorphism theorem.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(c) and
  Corollary 5 to Theorem 4′.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped MatrixGroups

namespace Matrix.ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A projective matrix has a determinant-one representative exactly when its determinant
is an nth power of a unit. -/
theorem mk_mem_range_toPGL_iff {g : GL n R} :
    mk g ∈ (SpecialLinearGroup.toPGL (n := n) (R := R)).range ↔
      ∃ u : Rˣ, u ^ Fintype.card n = g.det := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨u, hu⟩ := mk_eq_mk_iff.mp hs
    exact ⟨u, by simpa using congrArg GeneralLinearGroup.det hu⟩
  · rintro ⟨u, hu⟩
    have hd : (g * GeneralLinearGroup.scalar n u⁻¹).det = 1 := by
      simp [hu, map_mul, GeneralLinearGroup.det_scalar]
    obtain ⟨s, hs⟩ := SpecialLinearGroup.range_toGL_eq_ker_det.ge hd
    refine ⟨s, ?_⟩
    exact mk_eq_mk_iff.mpr ⟨u, by simp [hs, mul_assoc]⟩

/-- The determinant of a projective matrix, taken modulo nth powers of units. -/
def detClass : PGL(n, R) →* Rˣ ⧸ (powMonoidHom (α := Rˣ) (Fintype.card n)).range :=
  lift ((QuotientGroup.mk' _).comp GeneralLinearGroup.det) (by
    ext u
    simp only [MonoidHom.comp_apply, GeneralLinearGroup.det_scalar,
      QuotientGroup.mk'_apply, MonoidHom.one_apply]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩)

/-- On a matrix representative, the determinant class is the class of its determinant. -/
@[simp]
theorem detClass_mk {g : GL n R} :
    detClass (mk g) = QuotientGroup.mk g.det :=
  (rfl)

/-- The kernel of the determinant class consists exactly of the projective matrices which
lift to SL. -/
theorem ker_detClass :
    (detClass (n := n) (R := R)).ker = (SpecialLinearGroup.toPGL (n := n) (R := R)).range := by
  ext x
  induction x using induction_on with
  | mk g =>
    rw [MonoidHom.mem_ker, detClass_mk, QuotientGroup.eq_one_iff, mk_mem_range_toPGL_iff]
    simp only [MonoidHom.mem_range, powMonoidHom_apply]

/-- The image of SL is a normal subgroup of the pointwise projective general linear group. -/
instance normal_range_toPGL :
    (SpecialLinearGroup.toPGL (n := n) (R := R)).range.Normal := by
  rw [← ker_detClass]
  infer_instance

/-- Every unit class is the determinant class of a projective matrix of nonzero size. -/
theorem detClass_surjective [Nonempty n] :
    Function.Surjective (detClass (n := n) (R := R)) := by
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, rfl⟩ := GeneralLinearGroup.det_surjective (n := n) u
  exact ⟨mk g, detClass_mk⟩

/-- The pointwise cokernel of SL → PGL is the group of units modulo nth powers. -/
noncomputable def quotientRangeToPGLEquiv [Nonempty n] :
    PGL(n, R) ⧸ (SpecialLinearGroup.toPGL (n := n) (R := R)).range ≃*
      Rˣ ⧸ (powMonoidHom (α := Rˣ) (Fintype.card n)).range :=
  (QuotientGroup.quotientMulEquivOfEq ker_detClass.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective detClass detClass_surjective)

/-- The cokernel comparison sends the class represented by g to its determinant class. -/
@[simp]
theorem quotientRangeToPGLEquiv_mk [Nonempty n] (g : PGL(n, R)) :
    quotientRangeToPGLEquiv (QuotientGroup.mk g) = detClass g :=
  (rfl)

/-- In size two, the normalized diagonal torus element diag(a,1) lifts to SL exactly when a
is a square in the unit group. -/
theorem mk_diagGL_mem_range_toPGL_iff {a : Rˣ} :
    mk (TauCeti.diagGL ![a, 1]) ∈ (SpecialLinearGroup.toPGL (n := Fin 2) (R := R)).range ↔
      IsSquare a := by
  rw [mk_mem_range_toPGL_iff]
  simp [isSquare_iff_exists_sq, eq_comm]

/-- The rational projective matrix diag(2,1) is not the image of any determinant-one matrix. -/
theorem mk_diagGL_two_notMem_range_toPGL :
    mk (TauCeti.diagGL ![Units.mk0 (2 : ℚ) (by norm_num), 1]) ∉
      (SpecialLinearGroup.toPGL (n := Fin 2) (R := ℚ)).range := by
  rw [mk_diagGL_mem_range_toPGL_iff]
  rintro ⟨u, hu⟩
  have hs : IsSquare (2 : ℚ) := ⟨(u : ℚ), congrArg Units.val hu⟩
  norm_num at hs

end Matrix.ProjGenLinGroup
