/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup.Determinant

/-!
# The real projective special linear group has index two in the projective general linear group

In even dimension the sign of the determinant is well defined on `PGL(n, ℝ)`, since scaling a
matrix by `λ` multiplies its determinant by the positive number `λⁿ`. This is Mathlib's
`Matrix.ProjGenLinGroup.signDet`. Its kernel is the image of `PSL(n, ℝ)`: a positive determinant
has a real `n`-th root, so a matrix of positive determinant is a scalar multiple of a matrix of
determinant one, and conversely the determinant of a scalar multiple of a determinant-one matrix is
an even power. For nonempty matrices the sign is onto `{±1}`, so the image of `PSL(n, ℝ)` is a
normal subgroup of index two. For `n = 2` this places the orientation-preserving isometries
`PSL(2, ℝ)` of the hyperbolic plane inside `PGL(2, ℝ)`, whose other coset consists of the
orientation-reversing ones.

## Main results

* `Matrix.ProjGenLinGroup.ker_signDet`: the kernel of the sign of the determinant on
  `PGL(n, ℝ)` is the image of `PSL(n, ℝ)`.
* `Matrix.ProjGenLinGroup.signDet_surjective`: for nonempty matrices the sign is onto.
* `Matrix.ProjGenLinGroup.index_range_toPGL`: for nonempty matrices the image of `PSL(n, ℝ)` has
  index two in `PGL(n, ℝ)`.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press, 1992, Chapter 1.
-/

public section

open scoped MatrixGroups

namespace Matrix.ProjGenLinGroup

variable {n : Type*} [Fintype n] [DecidableEq n] [Fact (Even (Fintype.card n))]

/-- In even dimension, a real projective matrix comes from `PSL(n, ℝ)` exactly when its
determinant is positive. -/
theorem ker_signDet :
    (signDet (n := n) (R := ℝ)).ker =
      (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := ℝ)).range := by
  have hN : Even (Fintype.card n) := Fact.out
  ext x
  induction x using induction_on with
  | mk g =>
    rw [ProjectiveSpecialLinearGroup.range_toPGL, mk_mem_range_toPGL_iff, MonoidHom.mem_ker,
      ← Units.val_inj, val_signDet_mk, Units.val_one, sign_eq_one_iff]
    refine ⟨fun hg ↦ ?_, fun ⟨u, hu⟩ ↦ hu ▸ hN.pow_pos u.ne_zero⟩
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨1, Units.ext (by simp)⟩
    · refine ⟨Units.mk0 ((g.det : ℝ) ^ ((Fintype.card n : ℝ)⁻¹))
        (Real.rpow_pos_of_pos hg _).ne', Units.ext ?_⟩
      simpa using Real.rpow_inv_natCast_pow hg.le Fintype.card_ne_zero

/-- For nonempty real matrices of even size, the sign of the determinant is onto `{±1}`. -/
theorem signDet_surjective [Nonempty n] :
    Function.Surjective (signDet (n := n) (R := ℝ)) := by
  intro s
  have hs : ((s : SignType) : ℝ) ≠ 0 := by
    have := s.ne_zero
    cases h : (s : SignType) <;> simp_all
  obtain ⟨g, hg⟩ := GeneralLinearGroup.det_surjective (n := n) (Units.mk0 _ hs)
  refine ⟨mk g, Units.ext ?_⟩
  rw [val_signDet_mk, hg, Units.val_mk0]
  cases (s : SignType) <;> simp

/-- The image of `PSL(n, ℝ)` has finite index in `PGL(n, ℝ)` in even dimension. -/
instance finiteIndex_range_toPGL :
    (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := ℝ)).range.FiniteIndex := by
  rw [← ker_signDet]
  infer_instance

/-- For nonempty real matrices of even size, the image of `PSL(n, ℝ)` has index two in
`PGL(n, ℝ)`. -/
theorem index_range_toPGL [Nonempty n] :
    (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := ℝ)).range.index = 2 := by
  rw [← ker_signDet, Subgroup.index_ker, MonoidHom.range_eq_top.mpr signDet_surjective,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  decide

end Matrix.ProjGenLinGroup
