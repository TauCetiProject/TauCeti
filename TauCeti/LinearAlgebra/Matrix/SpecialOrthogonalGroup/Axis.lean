/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Frame

import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.CrossProduct

/-!
# The axis of a rotation of `ℝ³`

**Euler's rotation theorem** says that every rotation of three-dimensional space is a rotation
about an axis: it fixes a line pointwise. In matrix form, a matrix `g` with `g gᵀ = 1` and
`det g = 1` in odd dimension satisfies `det (g - 1) = 0`, because

`det (g - 1) = det (g (1 - g)ᵀ) = det (1 - g) = (-1) ^ n det (g - 1) = -det (g - 1)`.

So over a field in which `2 ≠ 0`, the matrix `g` fixes a nonzero vector, and over `ℝ` a unit
vector.

A nonidentity rotation of `ℝ³` fixes exactly two unit vectors, the two endpoints `±v` of its axis
on the unit sphere. The reason is that a rotation of `R³` fixing two vectors `u` and `w` also fixes
their cross product, since rotations preserve the cross product; when `u ⨯₃ w` is not isotropic the
three vectors form a basis, so the rotation is the identity. Two unit vectors of `ℝ³` whose cross
product vanishes are equal or opposite (`TauCeti.eq_or_eq_neg_of_cross_dotProduct_eq_zero`).

These are the facts about single rotations that the pole-counting argument for finite rotation
groups rests on; see `TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Pole.lean`.

## Main results

* `Matrix.det_sub_one_eq_zero_of_mem_specialOrthogonalGroup`: in odd dimension, `det (g - 1) = 0`
  for a rotation `g`, over any commutative ring in which `2` is regular.
* `Matrix.exists_ne_zero_mulVec_eq_self_of_mem_specialOrthogonalGroup`: in odd dimension, a
  rotation over a field of characteristic not two fixes a nonzero vector.
* `Matrix.eq_one_of_mulVec_eq_self_of_isUnit_cross_dotProduct`: a rotation of `R³` fixing `u` and
  `w` with `(u ⨯₃ w) ⬝ᵥ (u ⨯₃ w)` a unit is the identity.
* `Matrix.exists_dotProduct_self_eq_one_mulVec_eq_self`: **Euler's rotation theorem**, every
  rotation of `ℝ³` fixes a unit vector.
* `Matrix.eq_or_eq_neg_of_mulVec_eq_self`: a nonidentity rotation of `K³`, over an ordered field
  `K`, fixing two unit vectors fixes them as the two endpoints of one axis: they are equal or
  opposite.
* `Matrix.exists_setOf_mulVec_eq_self_eq_pair`: the unit vectors fixed by a nonidentity rotation
  of `ℝ³` are exactly a pair `{v, -v}`.

## References

* M. Artin, *Algebra*, second edition, Pearson, 2011, Section 5.1 (Euler's rotation theorem) and
  Section 6.12 (the poles of a rotation).
-/

public section

open Matrix TauCeti.Matrix.SpecialOrthogonalGroup

namespace Matrix

section CommRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **Euler's rotation theorem, determinant form.** In odd dimension, a rotation `g` satisfies
`det (g - 1) = 0`, over any commutative ring in which `2` is regular. -/
theorem det_sub_one_eq_zero_of_mem_specialOrthogonalGroup (h2 : IsRegular (2 : R))
    (hn : Odd (Fintype.card n)) {g : Matrix n n R} (hg : g ∈ specialOrthogonalGroup n R) :
    (g - 1).det = 0 := by
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.mp hg
  have hgT : g * gᵀ = 1 := (mem_orthogonalGroup_iff n R).mp hO
  -- `g - 1 = g (1 - gᵀ)`, and `1 - gᵀ` is the transpose of `-(g - 1)`.
  have hfac : g - 1 = g * (-(g - 1))ᵀ := by
    rw [transpose_neg, transpose_sub, transpose_one, mul_neg, mul_sub, hgT, mul_one, neg_sub]
  have hneg : (g - 1).det = -(g - 1).det := by
    conv_lhs => rw [hfac]
    rw [det_mul, hdet, one_mul, det_transpose, det_neg, hn.neg_one_pow, neg_one_mul]
  exact h2.left (by linear_combination hneg : 2 * (g - 1).det = 2 * 0)

/-- **A rotation of `R³` fixing two vectors is the identity**, as soon as the cross product of the
two vectors has invertible square: then the vectors and their cross product, which the rotation
also fixes, form a basis. Over `ℝ` the hypothesis says that the vectors are linearly
independent. -/
theorem eq_one_of_mulVec_eq_self_of_isUnit_cross_dotProduct {g : Matrix (Fin 3) (Fin 3) R}
    (hg : g ∈ specialOrthogonalGroup (Fin 3) R) {u w : Fin 3 → R} (hu : g *ᵥ u = u)
    (hw : g *ᵥ w = w) (huw : IsUnit ((u ⨯₃ w) ⬝ᵥ (u ⨯₃ w))) : g = 1 := by
  have hframe : g * ofFrame u w = ofFrame u w := by
    rw [← ofFrame_mulVec_mulVec hg, hu, hw]
  have hdet : IsUnit (ofFrame u w).det := by
    rwa [det_ofFrame]
  have := congrArg (· * (ofFrame u w)⁻¹) hframe
  simpa only [mul_assoc, mul_nonsing_inv _ hdet, mul_one] using this

end CommRing

/-- In odd dimension, **a rotation over a field of characteristic not two fixes a nonzero
vector**. -/
theorem exists_ne_zero_mulVec_eq_self_of_mem_specialOrthogonalGroup {n K : Type*} [Fintype n]
    [DecidableEq n] [Field K] [NeZero (2 : K)] (hn : Odd (Fintype.card n)) {g : Matrix n n K}
    (hg : g ∈ specialOrthogonalGroup n K) : ∃ v ≠ 0, g *ᵥ v = v := by
  obtain ⟨v, hv, h⟩ := exists_mulVec_eq_zero_iff.mpr
    (det_sub_one_eq_zero_of_mem_specialOrthogonalGroup (.of_ne_zero two_ne_zero) hn hg)
  exact ⟨v, hv, by rwa [sub_mulVec, one_mulVec, sub_eq_zero] at h⟩

/-- **A nonidentity rotation of `K³` fixing two unit vectors fixes them as the two endpoints of one
axis**: they are equal or opposite. Here `K` is an ordered field, such as `ℝ`. -/
theorem eq_or_eq_neg_of_mulVec_eq_self {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {g : Matrix (Fin 3) (Fin 3) K}
    (hg : g ∈ specialOrthogonalGroup (Fin 3) K) (hg1 : g ≠ 1) {u w : Fin 3 → K}
    (hu1 : u ⬝ᵥ u = 1) (hw1 : w ⬝ᵥ w = 1) (hu : g *ᵥ u = u) (hw : g *ᵥ w = w) :
    w = u ∨ w = -u := by
  refine TauCeti.eq_or_eq_neg_of_cross_dotProduct_eq_zero hu1 hw1 (by_contra fun h ↦ hg1 ?_)
  exact eq_one_of_mulVec_eq_self_of_isUnit_cross_dotProduct hg hu hw (Ne.isUnit h)

/-- **Euler's rotation theorem**: every rotation of `ℝ³` fixes a unit vector, a point of the unit
sphere on its axis. -/
theorem exists_dotProduct_self_eq_one_mulVec_eq_self {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g ∈ specialOrthogonalGroup (Fin 3) ℝ) : ∃ v, v ⬝ᵥ v = 1 ∧ g *ᵥ v = v := by
  obtain ⟨v, hv, hgv⟩ := exists_ne_zero_mulVec_eq_self_of_mem_specialOrthogonalGroup
    (by decide) hg
  have hpos : 0 < v ⬝ᵥ v :=
    (Fintype.sum_nonneg fun i ↦ mul_self_nonneg (v i)).lt_of_ne
      (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹ • v, ?_, by rw [mulVec_smul, hgv]⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- **The unit vectors fixed by a nonidentity rotation of `ℝ³` are a pair `{v, -v}`**, the two
endpoints of its axis on the unit sphere. -/
theorem exists_setOf_mulVec_eq_self_eq_pair {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g ∈ specialOrthogonalGroup (Fin 3) ℝ) (hg1 : g ≠ 1) :
    ∃ v, v ⬝ᵥ v = 1 ∧ {w | w ⬝ᵥ w = 1 ∧ g *ᵥ w = w} = {v, -v} := by
  obtain ⟨v, hv1, hgv⟩ := exists_dotProduct_self_eq_one_mulVec_eq_self hg
  refine ⟨v, hv1, Set.ext fun w ↦ ⟨fun ⟨hw1, hgw⟩ ↦ eq_or_eq_neg_of_mulVec_eq_self hg hg1 hv1 hw1
    hgv hgw, ?_⟩⟩
  rintro (rfl | rfl)
  · exact ⟨hv1, hgv⟩
  · exact ⟨by rw [neg_dotProduct, dotProduct_neg, neg_neg, hv1], by rw [mulVec_neg, hgv]⟩

end Matrix
