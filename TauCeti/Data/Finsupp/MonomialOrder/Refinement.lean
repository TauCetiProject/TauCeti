/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Order.Group.Equiv

/-!
# Weight refinements of monomial orders

A nonnegative integral weight compares exponents only partially: distinct monomials can
have the same weight. `MonomialOrder.weightRefinement` breaks these ties with a given
monomial order. The resulting order is again a native `MonomialOrder`, even with zero
weights and infinitely many variables. It can therefore be used with polynomial division
and Gröbner bases, while retaining the maximal-weight convention for initial forms.

The construction embeds exponents into the lexicographic product of their weight and their
original ordered exponent. Both factors are well ordered.

## References

* Sturmfels, *Gröbner Bases and Convex Polytopes*, Chapter 1.
-/

public section

open Finsupp
open scoped MonomialOrder

namespace MonomialOrder

variable {σ : Type*}

/-- Compare nonnegative integral weights first, breaking ties using `m`. -/
noncomputable def weightRefinement (m : MonomialOrder σ) (w : σ → ℕ) : MonomialOrder σ := by
  let f : (σ →₀ ℕ) →+ (ℕ ×ₗ m.syn) :=
    (toLexAddEquiv (ℕ × m.syn)).toAddMonoidHom.comp
      ((weight w).prod m.toSyn.toAddMonoidHom)
  exact
    { syn := AddMonoidHom.mrange f
      isOrderedAddMonoid_syn :=
        { add_le_add_left := fun a b h c ↦
            add_le_add_left (α := ℕ ×ₗ m.syn) h c.val }
      toSyn := AddEquiv.ofLeftInverse' f (g := fun x ↦ m.toSyn.symm (ofLex x).2)
        (fun a ↦ m.toSyn.symm_apply_apply a)
      toSyn_monotone := by
        intro a b hab
        apply Prod.Lex.le_iff.2
        have hw : weight w a ≤ weight w b := by
          obtain ⟨c, rfl⟩ := exists_add_of_le hab
          simp
        rcases lt_or_eq_of_le hw with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, m.toSyn_monotone hab⟩ }

/-- The weak comparison in a weight refinement. -/
theorem weightRefinement_le_iff (m : MonomialOrder σ) (w : σ → ℕ) {a b : σ →₀ ℕ} :
    a ≼[m.weightRefinement w] b ↔
      weight w a < weight w b ∨ weight w a = weight w b ∧ a ≼[m] b :=
  Prod.Lex.le_iff

/-- The strict comparison in a weight refinement. -/
theorem weightRefinement_lt_iff (m : MonomialOrder σ) (w : σ → ℕ) {a b : σ →₀ ℕ} :
    a ≺[m.weightRefinement w] b ↔
      weight w a < weight w b ∨ weight w a = weight w b ∧ a ≺[m] b :=
  Prod.Lex.lt_iff

/-- A comparison in the refined order never decreases weight. -/
theorem weight_le_of_weightRefinement_le (m : MonomialOrder σ) (w : σ → ℕ)
    {a b : σ →₀ ℕ} (h : a ≼[m.weightRefinement w] b) : weight w a ≤ weight w b := by
  rcases (m.weightRefinement_le_iff w).1 h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-- A strict weight comparison is a strict comparison in the refined order. -/
theorem weightRefinement_lt_of_weight_lt (m : MonomialOrder σ) (w : σ → ℕ)
    {a b : σ →₀ ℕ} (h : weight w a < weight w b) : a ≺[m.weightRefinement w] b :=
  (m.weightRefinement_lt_iff w).2 (Or.inl h)

/-- Equal-weight monomials are compared by the original order. -/
theorem weightRefinement_le_iff_of_weight_eq (m : MonomialOrder σ) (w : σ → ℕ)
    {a b : σ →₀ ℕ} (h : weight w a = weight w b) :
    a ≼[m.weightRefinement w] b ↔ a ≼[m] b := by
  simp [weightRefinement_le_iff, h]

/-- Equal-weight monomials are strictly compared by the original order. -/
theorem weightRefinement_lt_iff_of_weight_eq (m : MonomialOrder σ) (w : σ → ℕ)
    {a b : σ →₀ ℕ} (h : weight w a = weight w b) :
    a ≺[m.weightRefinement w] b ↔ a ≺[m] b := by
  simp [weightRefinement_lt_iff, h]

/-- Zero weight leaves all weak comparisons unchanged. -/
@[simp]
theorem weightRefinement_zero_le_iff (m : MonomialOrder σ) {a b : σ →₀ ℕ} :
    a ≼[m.weightRefinement 0] b ↔ a ≼[m] b := by
  simp [weightRefinement_le_iff, weight_apply]

/-- Zero weight leaves all strict comparisons unchanged. -/
@[simp]
theorem weightRefinement_zero_lt_iff (m : MonomialOrder σ) {a b : σ →₀ ℕ} :
    a ≺[m.weightRefinement 0] b ↔ a ≺[m] b := by
  simp [weightRefinement_lt_iff, weight_apply]

/-- The refined order compares variables by weight, retaining `m` to break ties. -/
theorem weightRefinement_single_le_iff (m : MonomialOrder σ) (w : σ → ℕ) {i j : σ} :
    single i 1 ≼[m.weightRefinement w] single j 1 ↔
      w i < w j ∨ w i = w j ∧ single i 1 ≼[m] single j 1 := by
  simp [weightRefinement_le_iff, weight_single]

end MonomialOrder
