/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import TauCeti.AlgebraicGeometry.WeilDivisor

/-!
# Positive and negative parts of Weil divisors

This file adds the standard Jordan decomposition for formal Weil divisors. A divisor `D`
splits as `D⁺ - D⁻`, where both parts are effective and have disjoint support. This is a
purely combinatorial prerequisite for the Jacobian roadmap's Layer A: later geometric
principal divisors, degree-zero divisor classes, and Picard-group quotients need to separate
zeros and poles without rebuilding finite-support bookkeeping.

The implementation reuses Mathlib's `Finsupp.filter`: the positive part is the restriction
of `D` to points with positive coefficient, and the negative part is the positive part of
`-D`.

This advances the Tau Ceti Jacobian roadmap, Layer A, "Divisors on a curve: Weil divisors
`⊕_x ℤ`", "principal divisors", and "Degree", by supplying the formal positive/pole and
negative/zero decomposition used before the scheme-theoretic divisor map is introduced.
-/

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X : Type*}

noncomputable section

/-- The positive part of a Weil divisor, retaining exactly the positive coefficients. -/
def positivePart (D : WeilDivisor X) : WeilDivisor X :=
  D.filter fun x => 0 < coeff D x

/-- The negative part of a Weil divisor, with positive coefficients recording the negative
coefficients of the original divisor. -/
def negativePart (D : WeilDivisor X) : WeilDivisor X :=
  positivePart (-D)

@[simp]
lemma coeff_positivePart (D : WeilDivisor X) (x : X) :
    coeff (positivePart D) x = if 0 < coeff D x then coeff D x else 0 :=
  rfl

@[simp]
lemma coeff_negativePart (D : WeilDivisor X) (x : X) :
    coeff (negativePart D) x = if coeff D x < 0 then -coeff D x else 0 := by
  rw [negativePart, coeff_positivePart]
  simp only [coeff_neg, neg_pos]

/-- The support of the positive part is the positive-coefficient locus inside the support. -/
lemma support_positivePart (D : WeilDivisor X) :
    (positivePart D).support = D.support.filter fun x => 0 < coeff D x :=
  rfl

/-- The support of the negative part is the negative-coefficient locus inside the support. -/
lemma support_negativePart (D : WeilDivisor X) :
    (negativePart D).support = D.support.filter fun x => coeff D x < 0 := by
  rw [negativePart, support_positivePart]
  classical
  ext x
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, coeff_neg, neg_pos]
  constructor
  · rintro ⟨hx, hDx⟩
    exact ⟨fun hzero => hx (by simp [hzero]), hDx⟩
  · rintro ⟨hx, hDx⟩
    exact ⟨by simpa using hx, hDx⟩

/-- The positive part has support contained in the original support. -/
lemma support_positivePart_subset (D : WeilDivisor X) :
    (positivePart D).support ⊆ D.support := by
  rw [support_positivePart]
  exact Finset.filter_subset _ _

/-- The negative part has support contained in the original support. -/
lemma support_negativePart_subset (D : WeilDivisor X) :
    (negativePart D).support ⊆ D.support := by
  rw [support_negativePart]
  exact Finset.filter_subset _ _

/-- The positive part of a divisor is effective. -/
@[simp]
lemma isEffective_positivePart (D : WeilDivisor X) : IsEffective (positivePart D) := by
  intro x
  by_cases hx : 0 < coeff D x
  · simp [hx, hx.le]
  · simp [hx]

/-- The negative part of a divisor is effective. -/
@[simp]
lemma isEffective_negativePart (D : WeilDivisor X) : IsEffective (negativePart D) := by
  intro x
  by_cases hx : coeff D x < 0
  · simpa [hx] using neg_nonneg.mpr hx.le
  · simp [hx]

@[simp]
lemma positivePart_zero : positivePart (0 : WeilDivisor X) = 0 := by
  ext x
  simp

@[simp]
lemma negativePart_zero : negativePart (0 : WeilDivisor X) = 0 := by
  ext x
  simp [negativePart]

/-- An effective divisor is equal to its positive part. -/
lemma positivePart_eq_self_of_isEffective {D : WeilDivisor X} (hD : IsEffective D) :
    positivePart D = D := by
  ext x
  by_cases hx : 0 < coeff D x
  · simp [hx]
  · have hzero : coeff D x = 0 := le_antisymm (not_lt.mp hx) (hD x)
    simp [hzero]

/-- An effective divisor has no negative part. -/
lemma negativePart_eq_zero_of_isEffective {D : WeilDivisor X} (hD : IsEffective D) :
    negativePart D = 0 := by
  ext x
  have hx : ¬ coeff D x < 0 := not_lt.mpr (hD x)
  simp [hx]

@[simp]
lemma positivePart_ofPoint (x : X) : positivePart (ofPoint x) = ofPoint x :=
  positivePart_eq_self_of_isEffective (isEffective_ofPoint x)

@[simp]
lemma negativePart_ofPoint (x : X) : negativePart (ofPoint x) = 0 :=
  negativePart_eq_zero_of_isEffective (isEffective_ofPoint x)

/-- Positive and negative parts are pointwise disjoint. -/
lemma positivePart_coeff_ne_zero_imp_negativePart_coeff_eq_zero
    {D : WeilDivisor X} {x : X} (hx : coeff (positivePart D) x ≠ 0) :
    coeff (negativePart D) x = 0 := by
  rw [coeff_positivePart] at hx
  split_ifs at hx with hpos
  · have hnot : ¬ coeff D x < 0 := not_lt.mpr hpos.le
    simp [hnot]
  · exact (hx rfl).elim

/-- Positive and negative parts have disjoint supports. -/
lemma disjoint_support_positivePart_negativePart (D : WeilDivisor X) :
    Disjoint (positivePart D).support (negativePart D).support := by
  rw [Finset.disjoint_left]
  intro x hxpos hxneg
  exact Finsupp.mem_support_iff.mp hxneg
    (positivePart_coeff_ne_zero_imp_negativePart_coeff_eq_zero
      (Finsupp.mem_support_iff.mp hxpos))

/-- Coefficientwise form of `D = D⁺ - D⁻`. -/
lemma coeff_positivePart_sub_negativePart (D : WeilDivisor X) (x : X) :
    coeff (positivePart D - negativePart D) x = coeff D x := by
  by_cases hpos : 0 < coeff D x
  · have hnot : ¬ coeff D x < 0 := not_lt.mpr hpos.le
    simp [hpos, hnot]
  · by_cases hneg : coeff D x < 0
    · simp [hpos, hneg]
    · have hzero : coeff D x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp [hzero]

/-- Every Weil divisor is the difference of its positive and negative parts. -/
@[simp]
lemma positivePart_sub_negativePart (D : WeilDivisor X) :
    positivePart D - negativePart D = D := by
  ext x
  exact coeff_positivePart_sub_negativePart D x

/-- Equivalently, the positive part is the divisor plus the negative part. -/
lemma positivePart_eq_self_add_negativePart (D : WeilDivisor X) :
    positivePart D = D + negativePart D := by
  ext x
  by_cases hpos : 0 < coeff D x
  · have hnot : ¬ coeff D x < 0 := not_lt.mpr hpos.le
    simp [hpos, hnot]
  · by_cases hneg : coeff D x < 0
    · simp [hpos, hneg]
    · have hzero : coeff D x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp [hzero]

/-- Equivalently, the original divisor plus its negative part is effective. -/
lemma isEffective_self_add_negativePart (D : WeilDivisor X) :
    IsEffective (D + negativePart D) := by
  rw [← positivePart_eq_self_add_negativePart]
  exact isEffective_positivePart D

/-- The negative part of `-D` is the positive part of `D`. -/
@[simp]
lemma negativePart_neg (D : WeilDivisor X) : negativePart (-D) = positivePart D := by
  rw [negativePart]
  ext x
  by_cases hpos : 0 < coeff D x
  · simp [hpos]
  · by_cases hneg : coeff D x < 0
    · simp [hpos]
    · have hzero : coeff D x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp [hzero]

/-- The positive part of `-D` is the negative part of `D`. -/
@[simp]
lemma positivePart_neg (D : WeilDivisor X) : positivePart (-D) = negativePart D :=
  rfl

/-- Taking positive and negative parts characterizes effective divisors. -/
lemma isEffective_iff_negativePart_eq_zero (D : WeilDivisor X) :
    IsEffective D ↔ negativePart D = 0 := by
  constructor
  · exact negativePart_eq_zero_of_isEffective
  · intro h x
    by_contra hx
    have hneg : coeff D x < 0 := lt_of_not_ge hx
    have hcoeff : coeff (negativePart D) x = -coeff D x := by simp [hneg]
    rw [h] at hcoeff
    exact (ne_of_gt (neg_pos.mpr hneg)) hcoeff.symm

/-- The positive part of a point difference is the left point when the points are distinct. -/
@[simp]
lemma positivePart_pointDifference_of_ne {x y : X} (hxy : x ≠ y) :
    positivePart (pointDifference x y) = ofPoint x := by
  classical
  ext z
  by_cases hx : z = x
  · subst hx
    simp [hxy]
  · by_cases hy : z = y
    · subst hy
      simp [hxy.symm]
    · simp [hx, hy]

/-- The negative part of a point difference is the right point when the points are distinct. -/
@[simp]
lemma negativePart_pointDifference_of_ne {x y : X} (hxy : x ≠ y) :
    negativePart (pointDifference x y) = ofPoint y := by
  rw [negativePart]
  have h : -(pointDifference x y) = pointDifference y x := by
    rw [pointDifference, pointDifference]
    abel
  rw [h, positivePart_pointDifference_of_ne hxy.symm]

/-- The degree of the positive part minus the degree of the negative part is the degree of
the original divisor. -/
lemma degree_positivePart_sub_degree_negativePart (D : WeilDivisor X) :
    degree (positivePart D) - degree (negativePart D) = degree D := by
  rw [← degree_sub, positivePart_sub_negativePart]

/-- A divisor of degree zero has positive and negative parts of the same degree. -/
lemma degree_positivePart_eq_degree_negativePart_of_degree_eq_zero {D : WeilDivisor X}
    (hD : degree D = 0) : degree (positivePart D) = degree (negativePart D) := by
  have h := degree_positivePart_sub_degree_negativePart D
  omega

/-- Degree-zero divisors have positive and negative parts of equal degree. -/
lemma degree_positivePart_eq_degree_negativePart_of_mem_degreeZeroSubgroup
    (D : degreeZeroSubgroup X) :
    degree (positivePart (D : WeilDivisor X)) = degree (negativePart (D : WeilDivisor X)) :=
  degree_positivePart_eq_degree_negativePart_of_degree_eq_zero D.property

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti
