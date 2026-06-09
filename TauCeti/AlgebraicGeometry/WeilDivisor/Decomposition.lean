/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Tactic.Abel
import Mathlib.Tactic.SplitIfs
import TauCeti.AlgebraicGeometry.WeilDivisor

/-!
# Positive and negative parts of Weil divisors

This file adds the standard Jordan decomposition for formal Weil divisors. A divisor `D`
splits as `D⁺ - D⁻`, where both parts are effective and have disjoint support. This is a
purely combinatorial prerequisite for the Jacobian roadmap's Layer A: later geometric
principal divisors, degree-zero divisor classes, and Picard-group quotients need to separate
zeros and poles without rebuilding finite-support bookkeeping.

The implementation uses Mathlib's ordered-group positive and negative parts `D⁺` and `D⁻`;
the support lemmas identify their supports with the corresponding filtered supports of `D`.

This advances the Tau Ceti Jacobian roadmap, Layer A, "Divisors on a curve: Weil divisors
`⊕_x ℤ`", "principal divisors", and "Degree", by supplying the formal positive/zero and
negative/pole decomposition used before the scheme-theoretic divisor map is introduced.
-/

namespace TauCeti

namespace Finsupp

variable {ι α : Type*} [AddCommGroup α] [LinearOrder α]

/-- Positive parts of finitely supported functions are computed pointwise. -/
@[simp]
lemma posPart_apply (f : ι →₀ α) (i : ι) : f⁺ i = (f i)⁺ := by
  rw [posPart_def]
  simp [posPart_def]

/-- Negative parts of finitely supported functions are computed pointwise. -/
@[simp]
lemma negPart_apply (f : ι →₀ α) (i : ι) : f⁻ i = (f i)⁻ := by
  rw [negPart_def]
  simp [negPart_def]

/-- The support of the positive part is the positive-coefficient locus inside the support. -/
@[simp]
lemma support_posPart (f : ι →₀ α) :
    f⁺.support = f.support.filter fun i => 0 < f i := by
  ext i
  by_cases hi : 0 < f i
  · simp [Finsupp.mem_support_iff, hi, ne_of_gt hi]
  · have hnonpos : f i ≤ 0 := not_lt.mp hi
    simp [Finsupp.mem_support_iff, hi, posPart_eq_zero.2 hnonpos]

variable [AddLeftMono α]

/-- The support of the negative part is the negative-coefficient locus inside the support. -/
@[simp]
lemma support_negPart (f : ι →₀ α) :
    f⁻.support = f.support.filter fun i => f i < 0 := by
  ext i
  by_cases hi : f i < 0
  · simp [Finsupp.mem_support_iff, hi, ne_of_lt hi]
  · have hnonneg : 0 ≤ f i := not_lt.mp hi
    simp [Finsupp.mem_support_iff, hi, negPart_eq_zero.2 hnonneg]

/-- Positive and negative parts of a finitely supported function have disjoint supports. -/
lemma disjoint_support_posPart_negPart (f : ι →₀ α) :
    Disjoint f⁺.support f⁻.support := by
  rw [support_posPart, support_negPart, Finset.disjoint_left]
  intro i hi h'i
  exact (not_lt.mpr (Finset.mem_filter.mp hi).2.le) (Finset.mem_filter.mp h'i).2

end Finsupp

namespace AddMonoidHom

/-- Additive homomorphisms send the positive-minus-negative decomposition to the same
subtraction identity in the codomain. -/
lemma map_posPart_sub_map_negPart {α β : Type*}
    [AddGroup α] [Lattice α] [AddLeftMono α] [AddGroup β]
    (φ : α →+ β) (a : α) :
    φ a⁺ - φ a⁻ = φ a := by
  simpa only [map_sub] using congrArg φ (_root_.posPart_sub_negPart a)

end AddMonoidHom

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X : Type*}

noncomputable section

/-- The coefficient of `D⁺`: positive coefficients of `D` are retained, and all other
coefficients become zero. -/
@[simp]
lemma coeff_posPart (D : WeilDivisor X) (x : X) :
    coeff D⁺ x = if 0 < coeff D x then coeff D x else 0 := by
  by_cases hx : 0 < coeff D x
  · have hx' : 0 < D x := by simpa [coeff] using hx
    rw [if_pos hx]
    simpa [coeff] using
      (TauCeti.Finsupp.posPart_apply D x).trans (posPart_eq_self.2 hx'.le)
  · have hx' : ¬ 0 < D x := by simpa [coeff] using hx
    rw [if_neg hx]
    simpa [coeff] using
      (TauCeti.Finsupp.posPart_apply D x).trans (posPart_eq_zero.2 (not_lt.mp hx'))

/-- The coefficient of `D⁻`: negative coefficients of `D` are recorded by their absolute
value, and all other coefficients become zero. -/
@[simp]
lemma coeff_negPart (D : WeilDivisor X) (x : X) :
    coeff D⁻ x = if coeff D x < 0 then -coeff D x else 0 := by
  by_cases hx : coeff D x < 0
  · have hx' : D x < 0 := by simpa [coeff] using hx
    rw [if_pos hx]
    simpa [coeff] using
      (TauCeti.Finsupp.negPart_apply D x).trans (negPart_eq_neg.2 hx'.le)
  · have hx' : ¬ D x < 0 := by simpa [coeff] using hx
    rw [if_neg hx]
    simpa [coeff] using
      (TauCeti.Finsupp.negPart_apply D x).trans (negPart_eq_zero.2 (not_lt.mp hx'))

/-- The support of the positive part is the positive-coefficient locus inside the support. -/
@[simp]
lemma support_posPart (D : WeilDivisor X) :
    D⁺.support = D.support.filter fun x => 0 < coeff D x := by
  simp [coeff]

/-- The support of the negative part is the negative-coefficient locus inside the support. -/
@[simp]
lemma support_negPart (D : WeilDivisor X) :
    D⁻.support = D.support.filter fun x => coeff D x < 0 := by
  simp [coeff]

/-- The positive part has support contained in the original support. -/
lemma support_posPart_subset (D : WeilDivisor X) :
    D⁺.support ⊆ D.support := by
  rw [support_posPart]
  exact Finset.filter_subset _ _

/-- The negative part has support contained in the original support. -/
lemma support_negPart_subset (D : WeilDivisor X) :
    D⁻.support ⊆ D.support := by
  rw [support_negPart]
  exact Finset.filter_subset _ _

@[simp]
lemma posPart_ofPoint (x : X) : (ofPoint x)⁺ = ofPoint x :=
  posPart_eq_self.2 (isEffective_ofPoint x)

@[simp]
lemma negPart_ofPoint (x : X) : (ofPoint x)⁻ = 0 :=
  negPart_eq_zero.2 (isEffective_ofPoint x)

/-- Positive and negative parts are pointwise disjoint. -/
lemma posPart_coeff_ne_zero_imp_negPart_coeff_eq_zero
    {D : WeilDivisor X} {x : X} (hx : coeff D⁺ x ≠ 0) :
    coeff D⁻ x = 0 := by
  rw [coeff_posPart] at hx
  split_ifs at hx with hpos
  · have hnot : ¬ coeff D x < 0 := not_lt.mpr hpos.le
    simp [hnot]
  · exact (hx rfl).elim

/-- Positive and negative parts have disjoint supports. -/
lemma disjoint_support_posPart_negPart (D : WeilDivisor X) :
    Disjoint D⁺.support D⁻.support :=
  TauCeti.Finsupp.disjoint_support_posPart_negPart D

/-- Equivalently, the original divisor plus its negative part is effective. -/
lemma isEffective_self_add_negPart (D : WeilDivisor X) :
    IsEffective (D + D⁻) := by
  have h : D⁺ = D + D⁻ := sub_eq_iff_eq_add.mp (_root_.posPart_sub_negPart D)
  rw [← h]
  exact posPart_nonneg D

/-- The positive part of a point difference is the left point when the points are distinct. -/
@[simp]
lemma posPart_pointDifference_of_ne {x y : X} (hxy : x ≠ y) :
    (pointDifference x y)⁺ = ofPoint x := by
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
lemma negPart_pointDifference_of_ne {x y : X} (hxy : x ≠ y) :
    (pointDifference x y)⁻ = ofPoint y := by
  rw [← _root_.posPart_neg]
  have h : -(pointDifference x y) = pointDifference y x := by
    rw [pointDifference, pointDifference]
    abel
  rw [h, posPart_pointDifference_of_ne hxy.symm]

/-- The weighted degree of the positive part minus the weighted degree of the negative part
is the weighted degree of the original divisor. -/
lemma weightedDegree_posPart_sub_weightedDegree_negPart (w : X → ℤ) (D : WeilDivisor X) :
    weightedDegree w D⁺ - weightedDegree w D⁻ = weightedDegree w D := by
  rw [← weightedDegree_sub, _root_.posPart_sub_negPart]

/-- A divisor of weighted degree zero has positive and negative parts of the same weighted
degree. -/
lemma weightedDegree_posPart_eq_weightedDegree_negPart_of_weightedDegree_eq_zero
    {w : X → ℤ} {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    weightedDegree w D⁺ = weightedDegree w D⁻ := by
  have h := weightedDegree_posPart_sub_weightedDegree_negPart w D
  rw [hD] at h
  exact sub_eq_zero.mp h

/-- Weighted-degree-zero divisors have positive and negative parts of equal weighted degree. -/
lemma weightedDegree_posPart_eq_weightedDegree_negPart_of_mem_weightedDegreeZeroSubgroup
    (w : X → ℤ) (D : weightedDegreeZeroSubgroup w) :
    weightedDegree w (D : WeilDivisor X)⁺ =
      weightedDegree w (D : WeilDivisor X)⁻ :=
  weightedDegree_posPart_eq_weightedDegree_negPart_of_weightedDegree_eq_zero
    (weightedDegree_coe_weightedDegreeZeroSubgroup w D)

/-- The degree of the positive part minus the degree of the negative part is the degree of
the original divisor. -/
lemma degree_posPart_sub_degree_negPart (D : WeilDivisor X) :
    degree D⁺ - degree D⁻ = degree D := by
  simpa [weightedDegree_one_eq_degree] using
    weightedDegree_posPart_sub_weightedDegree_negPart (fun _ : X => (1 : ℤ)) D

/-- A divisor of degree zero has positive and negative parts of the same degree. -/
lemma degree_posPart_eq_degree_negPart_of_degree_eq_zero {D : WeilDivisor X}
    (hD : degree D = 0) : degree D⁺ = degree D⁻ := by
  simpa [weightedDegree_one_eq_degree] using
    weightedDegree_posPart_eq_weightedDegree_negPart_of_weightedDegree_eq_zero
      (w := fun _ : X => (1 : ℤ)) (D := D) (by simpa [weightedDegree_one_eq_degree] using hD)

/-- Degree-zero divisors have positive and negative parts of equal degree. -/
lemma degree_posPart_eq_degree_negPart_of_mem_degreeZeroSubgroup
    (D : degreeZeroSubgroup X) :
    degree (D : WeilDivisor X)⁺ = degree (D : WeilDivisor X)⁻ :=
  degree_posPart_eq_degree_negPart_of_degree_eq_zero D.property

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti
