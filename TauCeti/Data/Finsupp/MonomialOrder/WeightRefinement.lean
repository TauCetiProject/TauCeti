/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.Weight

/-!
# Refining a weight order by a monomial order

Let `m` be a monomial order on `σ →₀ ℕ` and let `w : σ → ℕ` be a weight vector. The weight
`Finsupp.weight w` only preorders the monomials, since distinct monomials may have the same
weight. Breaking its ties with `m` gives a monomial order `m.weightRefinement w`, often written
`≺_w`: the monomial `a` precedes `b` when `weight w a < weight w b`, or when the two weights are
equal and `a ≺[m] b`.

This is the monomial order through which weight initial forms are compared with leading terms:
the leading term of a polynomial for `m.weightRefinement w` is the leading term for `m` of its
initial form for `w`.

## Main declarations

* `MonomialOrder.weightRefinement m w`: the monomial order `m` refined by the weight `w`.
* `MonomialOrder.weightRefinement_le_iff`, `MonomialOrder.weightRefinement_lt_iff`: the
  comparisons of `m.weightRefinement w`.

## Implementation notes

The well-ordered additive monoid underlying `m.weightRefinement w` is the image of the injective
additive map `a ↦ (weight w a, m.toSyn a)` into the lexicographic product `ℕ ×ₗ m.syn`.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 1.
-/

public section

open Finsupp

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ) (w : σ → ℕ)

/-- The additive map `a ↦ (weight w a, m.toSyn a)` into the lexicographic product `ℕ ×ₗ m.syn`. -/
private noncomputable def weightRefinementHom : (σ →₀ ℕ) →+ ℕ ×ₗ m.syn where
  toFun a := toLex (weight w a, m.toSyn a)
  map_zero' := by simp [← toLex_zero]
  map_add' a b := by simp [← toLex_add]

private theorem weightRefinementHom_apply (a : σ →₀ ℕ) :
    m.weightRefinementHom w a = toLex (weight w a, m.toSyn a) :=
  rfl

private theorem leftInverse_weightRefinementHom :
    Function.LeftInverse (fun x : ℕ ×ₗ m.syn ↦ m.toSyn.symm (ofLex x).2)
      (m.weightRefinementHom w) := fun a ↦ by
  simp [weightRefinementHom_apply]

/-- The monomial order `m` refined by the weight vector `w`, often written `≺_w`: monomials are
compared first by their weight `weight w`, and monomials of equal weight are compared by `m`. -/
noncomputable def weightRefinement : MonomialOrder σ where
  syn := AddMonoidHom.mrange (m.weightRefinementHom w)
  toSyn := AddEquiv.ofLeftInverse' _ (m.leftInverse_weightRefinementHom w)
  toSyn_monotone a b hab := by
    -- The order on `syn` is the order of the images in `ℕ ×ₗ m.syn`.
    refine Prod.Lex.toLex_le_toLex.2 ?_
    obtain ⟨c, rfl⟩ := exists_add_of_le hab
    rcases (Nat.le_add_right (weight w a) (weight w c)).lt_or_eq with h | h
    · exact .inl (by simpa using h)
    · exact .inr ⟨by simpa using h.symm, m.toSyn_monotone hab⟩

variable {m w} {a b : σ →₀ ℕ}

/-- The comparisons of `m.weightRefinement w`: monomials are compared by weight, and monomials
of equal weight by `m`. -/
theorem weightRefinement_le_iff :
    a ≼[m.weightRefinement w] b ↔ weight w a < weight w b ∨ weight w a = weight w b ∧ a ≼[m] b :=
  Prod.Lex.toLex_le_toLex

/-- The strict comparisons of `m.weightRefinement w`: monomials are compared by weight, and
monomials of equal weight by `m`. -/
theorem weightRefinement_lt_iff :
    a ≺[m.weightRefinement w] b ↔ weight w a < weight w b ∨ weight w a = weight w b ∧ a ≺[m] b :=
  Prod.Lex.toLex_lt_toLex

/-- Comparisons of `m.weightRefinement w` are compatible with the weight. -/
theorem weight_le_weight_of_weightRefinement_le (h : a ≼[m.weightRefinement w] b) :
    weight w a ≤ weight w b :=
  (weightRefinement_le_iff.1 h).elim le_of_lt fun h ↦ h.1.le

/-- Monomials of equal weight are compared by `m.weightRefinement w` as by `m`. -/
theorem weightRefinement_le_iff_of_weight_eq (h : weight w a = weight w b) :
    a ≼[m.weightRefinement w] b ↔ a ≼[m] b := by
  simp [weightRefinement_le_iff, h]

/-- Refining by the zero weight does not change the comparisons of `m`. -/
@[simp]
theorem weightRefinement_zero_le_iff : a ≼[m.weightRefinement 0] b ↔ a ≼[m] b :=
  weightRefinement_le_iff_of_weight_eq (by simp [weight_apply])

end MonomialOrder
