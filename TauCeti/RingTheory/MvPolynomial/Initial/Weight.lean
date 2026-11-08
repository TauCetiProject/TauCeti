/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Maximal-weight initial forms

For nonnegative integral variable weights, `MvPolynomial.weightInitialForm` retains all terms
of maximal weight. Ties are retained, so an initial form need not be a monomial. Zero weights,
constant polynomials, and the zero polynomial are allowed.

Initial forms are weighted homogeneous and idempotent. Over a semiring without zero divisors
they preserve multiplication. These are the polynomial operations used to form weight-initial
ideals and special fibres of weight degenerations.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, AMS, 1996, Chapter 1.
-/

public section

namespace MvPolynomial

open Finsupp

variable {σ R S : Type*} [CommSemiring R] (w : σ → ℕ)

/-- The maximal-weight part of a polynomial, retaining every term tied for maximal weight. -/
noncomputable def weightInitialForm (p : MvPolynomial σ R) : MvPolynomial σ R :=
  weightedHomogeneousComponent w (p.weightedTotalDegree w) p

/-- The initial form is the top weighted homogeneous component. -/
theorem weightInitialForm_def (p : MvPolynomial σ R) :
    weightInitialForm w p = weightedHomogeneousComponent w (p.weightedTotalDegree w) p := (rfl)

theorem coeff_weightInitialForm (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (weightInitialForm w p).coeff d =
      if weight w d = p.weightedTotalDegree w then p.coeff d else 0 :=
  coeff_weightedHomogeneousComponent _ _ _

theorem support_weightInitialForm (p : MvPolynomial σ R) :
    (weightInitialForm w p).support =
      {d ∈ p.support | weight w d = p.weightedTotalDegree w} :=
  support_weightedHomogeneousComponent _ _

theorem support_weightInitialForm_subset (p : MvPolynomial σ R) :
    (weightInitialForm w p).support ⊆ p.support := by
  rw [support_weightInitialForm]
  exact Finset.filter_subset _ _

@[simp]
theorem weightInitialForm_zero : weightInitialForm w (0 : MvPolynomial σ R) = 0 :=
  map_zero _

/-- A polynomial and its initial form vanish simultaneously. -/
@[simp]
theorem weightInitialForm_eq_zero_iff (p : MvPolynomial σ R) :
    weightInitialForm w p = 0 ↔ p = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra hp
  obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp) (weight w)
  have hdw : weight w d = p.weightedTotalDegree w := he.symm
  have hc := congrArg (fun q : MvPolynomial σ R ↦ q.coeff d) h
  rw [coeff_weightInitialForm, ite_eq_left hdw] at hc
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact mem_support_iff.mp hd hc

theorem isWeightedHomogeneous_weightInitialForm (p : MvPolynomial σ R) :
    (weightInitialForm w p).IsWeightedHomogeneous w (p.weightedTotalDegree w) :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- A weighted homogeneous polynomial is its own initial form, including when it is zero. -/
theorem IsWeightedHomogeneous.weightInitialForm {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) : weightInitialForm w p = p := by
  by_cases h : p = 0
  · simp [h]
  have hn : p.weightedTotalDegree w = n :=
    WithBot.coe_injective ((weightedTotalDegree_coe w p h).symm.trans (hp.weighted_total_degree h))
  rw [weightInitialForm_def, hn, weightedHomogeneousComponent_eq_self hp]

@[simp]
theorem weightInitialForm_weightInitialForm (p : MvPolynomial σ R) :
    weightInitialForm w (weightInitialForm w p) = weightInitialForm w p :=
  (isWeightedHomogeneous_weightInitialForm w p).weightInitialForm w

@[simp]
theorem weightInitialForm_monomial (d : σ →₀ ℕ) (r : R) :
    weightInitialForm w (monomial d r) = monomial d r :=
  (isWeightedHomogeneous_monomial w d r rfl).weightInitialForm w

@[simp]
theorem weightInitialForm_C (r : R) : weightInitialForm w (C r : MvPolynomial σ R) = C r :=
  (isWeightedHomogeneous_C w r).weightInitialForm w

@[simp]
theorem weightInitialForm_one : weightInitialForm w (1 : MvPolynomial σ R) = 1 :=
  (isWeightedHomogeneous_one R w).weightInitialForm w

@[simp]
theorem weightInitialForm_X (i : σ) : weightInitialForm w (X i : MvPolynomial σ R) = X i :=
  (isWeightedHomogeneous_X R w i).weightInitialForm w

/-- When every variable has weight zero, every term is retained. -/
@[simp]
theorem weightInitialForm_zero_weight (p : MvPolynomial σ R) :
    weightInitialForm (0 : σ → ℕ) p = p := by
  have hp : p.IsWeightedHomogeneous (0 : σ → ℕ) 0 := by
    intro d _
    simp [Finsupp.weight_apply, Finsupp.sum]
  exact hp.weightInitialForm _

/-- Taking an initial form preserves the maximal weight, with both degrees totalized to zero
for the zero polynomial. -/
@[simp]
theorem weightedTotalDegree_weightInitialForm (p : MvPolynomial σ R) :
    (weightInitialForm w p).weightedTotalDegree w = p.weightedTotalDegree w := by
  by_cases hp : p = 0
  · simp [hp]
  have hi : weightInitialForm w p ≠ 0 := (weightInitialForm_eq_zero_iff w p).not.mpr hp
  exact WithBot.coe_injective ((weightedTotalDegree_coe _ _ hi).symm.trans
    ((isWeightedHomogeneous_weightInitialForm w p).weighted_total_degree hi))

/-- If the maximal weight in `q` is strictly larger, it alone supplies the initial form of
`p + q`. -/
theorem weightInitialForm_add_of_lt {p q : MvPolynomial σ R}
    (h : p.weightedTotalDegree w < q.weightedTotalDegree w) :
    weightInitialForm w (p + q) = weightInitialForm w q := by
  have hq : q ≠ 0 := by
    intro hq
    simp [hq, weightedTotalDegree_zero] at h
  have hc : weightedHomogeneousComponent w (q.weightedTotalDegree w) (p + q) =
      weightInitialForm w q := by
    rw [map_add, weightedHomogeneousComponent_eq_zero _ _ h, zero_add, weightInitialForm_def]
  have hdeg : (p + q).weightedTotalDegree w = q.weightedTotalDegree w := by
    apply le_antisymm ((weightedTotalDegree_add_le w p q).trans (max_le h.le le_rfl))
    by_contra! hlt
    exact (weightInitialForm_eq_zero_iff w q).not.mpr hq
      (hc.symm.trans (weightedHomogeneousComponent_eq_zero _ _ hlt))
  rw [weightInitialForm_def, hdeg, hc]

/-- The symmetric form of `weightInitialForm_add_of_lt`. -/
theorem weightInitialForm_add_of_gt {p q : MvPolynomial σ R}
    (h : q.weightedTotalDegree w < p.weightedTotalDegree w) :
    weightInitialForm w (p + q) = weightInitialForm w p := by
  rw [add_comm]
  exact weightInitialForm_add_of_lt w h

/-- If two polynomials have the same maximal weight and their initial forms do not cancel,
the initial form of their sum is the sum of their initial forms. -/
theorem weightInitialForm_add_of_eq {p q : MvPolynomial σ R}
    (h : p.weightedTotalDegree w = q.weightedTotalDegree w)
    (hne : weightInitialForm w p + weightInitialForm w q ≠ 0) :
    weightInitialForm w (p + q) = weightInitialForm w p + weightInitialForm w q := by
  have hc : weightedHomogeneousComponent w (p.weightedTotalDegree w) (p + q) =
      weightInitialForm w p + weightInitialForm w q := by
    simp only [map_add, weightInitialForm_def, h]
  have hdeg : (p + q).weightedTotalDegree w = p.weightedTotalDegree w := by
    apply le_antisymm ((weightedTotalDegree_add_le w p q).trans (by simp [h]))
    by_contra! hlt
    exact hne (hc.symm.trans (weightedHomogeneousComponent_eq_zero _ _ hlt))
  rw [weightInitialForm_def, hdeg, hc]

/-- Over a semiring without zero divisors, initial forms preserve multiplication. -/
@[simp]
theorem weightInitialForm_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) :
    weightInitialForm w (p * q) = weightInitialForm w p * weightInitialForm w q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  have hi : weightedHomogeneousComponent w
      (p.weightedTotalDegree w + q.weightedTotalDegree w) (p * q) ≠ 0 := by
    rw [weightedHomogeneousComponent_weightedTotalDegree_add]
    exact mul_ne_zero ((weightInitialForm_eq_zero_iff w p).not.mpr hp)
      ((weightInitialForm_eq_zero_iff w q).not.mpr hq)
  have hdeg : (p * q).weightedTotalDegree w =
      p.weightedTotalDegree w + q.weightedTotalDegree w := by
    apply le_antisymm (weightedTotalDegree_mul_le w p q)
    by_contra! hlt
    exact hi (weightedHomogeneousComponent_eq_zero _ _ hlt)
  rw [weightInitialForm_def, hdeg, weightedHomogeneousComponent_weightedTotalDegree_add]
  rfl

section Map

variable [CommSemiring S] (φ : R →+* S)

/-- Injective coefficient maps commute with taking initial forms. -/
theorem weightInitialForm_map_of_injective (hφ : Function.Injective φ) (p : MvPolynomial σ R) :
    weightInitialForm w (map φ p) = map φ (weightInitialForm w p) := by
  ext d
  simp only [coeff_weightInitialForm, weightedTotalDegree_map_of_injective w φ hφ,
    coeff_map]
  split_ifs <;> simp

end Map

section CommRing

variable {A : Type*} [CommRing A]

@[simp]
theorem weightInitialForm_neg (p : MvPolynomial σ A) :
    weightInitialForm w (-p) = -weightInitialForm w p := by
  have hdeg : (-p).weightedTotalDegree w = p.weightedTotalDegree w := by
    simp only [weightedTotalDegree, MvPolynomial.support_neg]
  rw [weightInitialForm_def, hdeg, map_neg, weightInitialForm_def]

/-- Subtracting the initial form leaves only strictly lower-weight terms. This support statement
also covers the case where the difference is zero, even in weight zero. -/
theorem weight_lt_of_mem_support_sub_weightInitialForm (p : MvPolynomial σ A)
    {d : σ →₀ ℕ} (hd : d ∈ (p - weightInitialForm w p).support) :
    weight w d < p.weightedTotalDegree w := by
  rw [mem_support_iff, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    coeff_weightInitialForm] at hd
  have hp : p.coeff d ≠ 0 := by
    intro hp
    simp [hp] at hd
  have hn : weight w d ≠ p.weightedTotalDegree w := by
    intro hn
    simp [hn] at hd
  exact lt_of_le_of_ne (le_weightedTotalDegree w (mem_support_iff.mpr hp)) hn

end CommRing

end MvPolynomial

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- If every other term has strictly smaller weight than the leading exponent, the weight
initial is exactly the monomial-order leading term. No positivity of the weights is required. -/
theorem weightInitialForm_eq_leadingTerm (m : MonomialOrder σ) (w : σ → ℕ)
    (f : MvPolynomial σ R)
    (h : ∀ a ∈ f.support, a ≠ m.degree f →
      Finsupp.weight w a < Finsupp.weight w (m.degree f)) :
    weightInitialForm w f = m.leadingTerm f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hdeg : f.weightedTotalDegree w = Finsupp.weight w (m.degree f) := by
    apply le_antisymm (Finset.sup_le fun a ha ↦ ?_)
      (le_weightedTotalDegree w (m.degree_mem_support hf))
    by_cases heq : a = m.degree f
    · simp [heq]
    · exact (h a ha heq).le
  ext a
  rw [coeff_weightInitialForm, hdeg, leadingTerm, coeff_monomial]
  by_cases ha : a = m.degree f
  · subst a
    simp [leadingCoeff]
  · have hzero : Finsupp.weight w a = Finsupp.weight w (m.degree f) → f.coeff a = 0 := by
      intro heq
      by_contra hn
      exact (ne_of_lt (h a (mem_support_iff.2 hn) ha)) heq
    simp only [Ne.symm ha, ↓reduceIte]
    split_ifs with heq
    · exact hzero heq
    · rfl

end MonomialOrder
