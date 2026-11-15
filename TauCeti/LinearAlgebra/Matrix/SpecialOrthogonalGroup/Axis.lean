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

So over an integral domain in which `2 ≠ 0`, the matrix `g` fixes a nonzero vector, and over `ℝ`
a unit vector.

A nonidentity rotation of `ℝ³` fixes exactly two unit vectors, the two endpoints `±v` of its axis
on the unit sphere. The reason is that a rotation `g` of `R³` fixing two vectors `u` and `w` also
fixes their cross product, since rotations preserve the cross product, so `g` fixes the frame matrix
`ofFrame u w` with columns `u`, `w` and `u ⨯₃ w`. The determinant of that frame is
`(u ⨯₃ w) ⬝ᵥ (u ⨯₃ w)`; when it is regular, so is the frame, and cancelling it from
`g * ofFrame u w = ofFrame u w` forces `g = 1`. Over an ordered commutative ring, two vectors of
equal squared length with `(u ⨯₃ w) ⬝ᵥ (u ⨯₃ w) = 0` are equal or opposite
(`TauCeti.eq_or_eq_neg_of_cross_dotProduct_eq_zero`).

These are the facts about single rotations that the pole-counting argument for finite rotation
groups rests on; see `TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Pole.lean`.

## Main results

* `Matrix.det_sub_one_eq_zero_of_mem_specialOrthogonalGroup`: in odd dimension, `det (g - 1) = 0`
  for a rotation `g`, over any commutative ring in which `2` is regular.
* `Matrix.exists_ne_zero_mulVec_eq_self_of_mem_specialOrthogonalGroup`: in odd dimension, a
  rotation over an integral domain in which `2 ≠ 0` fixes a nonzero vector.
* `Matrix.eq_one_of_mem_specialOrthogonalGroup_of_mulVec_eq_self_of_isRegular_cross_dotProduct`: a
  rotation of `R³` fixing `u` and `w` with `(u ⨯₃ w) ⬝ᵥ (u ⨯₃ w)` regular is the identity.
* `Matrix.eq_or_eq_neg_of_mem_specialOrthogonalGroup_of_mulVec_eq_self`: a nonidentity rotation of
  `R³`, over an ordered commutative ring `R`, fixing two vectors of equal squared length fixes
  them as two points of one axis: they are equal or opposite.
* `Matrix.setOf_mulVec_eq_self_eq_pair_of_mem_specialOrthogonalGroup`: over an ordered
  commutative ring `R`, the vectors fixed by a nonidentity rotation of `R³` with the squared length
  of a fixed vector `v` are exactly `v` and `-v`.
* `Matrix.exists_dotProduct_self_eq_one_mulVec_eq_self_of_mem_specialOrthogonalGroup`:
  **Euler's rotation theorem**, in odd dimension every rotation over `ℝ` fixes a unit vector.
* `Matrix.exists_setOf_mulVec_eq_self_eq_pair_of_mem_specialOrthogonalGroup`: the unit vectors
  fixed by a nonidentity rotation of `ℝ³` are exactly a pair `{v, -v}`.

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
two vectors has regular square. Over `ℝ` the hypothesis says that the vectors are linearly
independent. -/
theorem eq_one_of_mem_specialOrthogonalGroup_of_mulVec_eq_self_of_isRegular_cross_dotProduct
    {g : Matrix (Fin 3) (Fin 3) R} (hg : g ∈ specialOrthogonalGroup (Fin 3) R) {u w : Fin 3 → R}
    (hu : g *ᵥ u = u) (hw : g *ᵥ w = w) (huw : IsRegular ((u ⨯₃ w) ⬝ᵥ (u ⨯₃ w))) : g = 1 := by
  -- The frame `ofFrame u w` has regular determinant, so it can be cancelled from `g F = 1 F`.
  have hF : IsRegular (ofFrame u w) :=
    isRegular_of_isLeftRegular_det ((det_ofFrame u w).symm ▸ huw.left)
  exact hF.right (show g * ofFrame u w = 1 * ofFrame u w by
    rw [← ofFrame_mulVec_mulVec hg, hu, hw, one_mul])

/-- In odd dimension, **a rotation over an integral domain in which `2 ≠ 0` fixes a nonzero
vector**. -/
theorem exists_ne_zero_mulVec_eq_self_of_mem_specialOrthogonalGroup [IsDomain R] [NeZero (2 : R)]
    (hn : Odd (Fintype.card n)) {g : Matrix n n R} (hg : g ∈ specialOrthogonalGroup n R) :
    ∃ v ≠ 0, g *ᵥ v = v := by
  obtain ⟨v, hv, h⟩ := exists_mulVec_eq_zero_iff.mpr
    (det_sub_one_eq_zero_of_mem_specialOrthogonalGroup (IsRegular.of_ne_zero two_ne_zero) hn hg)
  exact ⟨v, hv, by rwa [sub_mulVec, one_mulVec, sub_eq_zero] at h⟩

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- **A nonidentity rotation of `R³` fixing two vectors of equal squared length fixes them as
points of one axis at the same distance from the origin**: they are equal or opposite. Here `R`
is an ordered commutative ring, such as `ℝ`. -/
theorem eq_or_eq_neg_of_mem_specialOrthogonalGroup_of_mulVec_eq_self
    {g : Matrix (Fin 3) (Fin 3) R} (hg : g ∈ specialOrthogonalGroup (Fin 3) R) (hg1 : g ≠ 1)
    {u w : Fin 3 → R} (huw : u ⬝ᵥ u = w ⬝ᵥ w) (hu : g *ᵥ u = u) (hw : g *ᵥ w = w) :
    w = u ∨ w = -u := by
  refine TauCeti.eq_or_eq_neg_of_cross_dotProduct_eq_zero huw (by_contra fun h ↦ hg1 ?_)
  exact eq_one_of_mem_specialOrthogonalGroup_of_mulVec_eq_self_of_isRegular_cross_dotProduct hg
    hu hw (IsRegular.of_ne_zero h)

/-- **The vectors fixed by a nonidentity rotation `g` of `R³` with the squared length of a fixed
vector `v` are exactly `v` and `-v`**, over an ordered commutative ring `R`. -/
theorem setOf_mulVec_eq_self_eq_pair_of_mem_specialOrthogonalGroup
    {g : Matrix (Fin 3) (Fin 3) R} (hg : g ∈ specialOrthogonalGroup (Fin 3) R) (hg1 : g ≠ 1)
    {v : Fin 3 → R} (hgv : g *ᵥ v = v) : {w | w ⬝ᵥ w = v ⬝ᵥ v ∧ g *ᵥ w = w} = {v, -v} := by
  refine Set.ext fun w ↦ ⟨fun ⟨hw, hgw⟩ ↦
    eq_or_eq_neg_of_mem_specialOrthogonalGroup_of_mulVec_eq_self hg hg1 hw.symm hgv hgw, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨rfl, hgv⟩
  · exact ⟨by rw [neg_dotProduct, dotProduct_neg, neg_neg], by rw [mulVec_neg, hgv]⟩

end Ordered

end CommRing

/-- **Euler's rotation theorem**: in odd dimension, and in particular in `ℝ³`, every rotation
over `ℝ` fixes a unit vector. -/
theorem exists_dotProduct_self_eq_one_mulVec_eq_self_of_mem_specialOrthogonalGroup {n : Type*}
    [Fintype n] [DecidableEq n] (hn : Odd (Fintype.card n)) {g : Matrix n n ℝ}
    (hg : g ∈ specialOrthogonalGroup n ℝ) : ∃ v, v ⬝ᵥ v = 1 ∧ g *ᵥ v = v := by
  obtain ⟨v, hv, hgv⟩ := exists_ne_zero_mulVec_eq_self_of_mem_specialOrthogonalGroup hn hg
  have hpos : 0 < v ⬝ᵥ v :=
    (Fintype.sum_nonneg fun i ↦ mul_self_nonneg (v i)).lt_of_ne
      (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹ • v, ?_, by rw [mulVec_smul, hgv]⟩
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  exact (Real.sq_sqrt hpos.le).symm

/-- **The unit vectors fixed by a nonidentity rotation of `ℝ³` are a pair `{v, -v}`**, the two
endpoints of its axis on the unit sphere. -/
theorem exists_setOf_mulVec_eq_self_eq_pair_of_mem_specialOrthogonalGroup
    {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g ∈ specialOrthogonalGroup (Fin 3) ℝ) (hg1 : g ≠ 1) :
    ∃ v, v ⬝ᵥ v = 1 ∧ {w | w ⬝ᵥ w = 1 ∧ g *ᵥ w = w} = {v, -v} := by
  obtain ⟨v, hv1, hgv⟩ :=
    exists_dotProduct_self_eq_one_mulVec_eq_self_of_mem_specialOrthogonalGroup (by decide) hg
  exact ⟨v, hv1, hv1 ▸ setOf_mulVec_eq_self_eq_pair_of_mem_specialOrthogonalGroup hg hg1 hgv⟩

end Matrix
