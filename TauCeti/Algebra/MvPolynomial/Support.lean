/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Support bounds for sums of monomials and linear forms

A finite sum `∑ j ∈ s, monomial (a j) (w j)` of monomials in a multivariate polynomial ring has
support contained in `s.image a`, so its support has cardinality at most `#s`. Specializing to
degree-one monomials `C (w j) * X (g j) = monomial (Finsupp.single (g j) 1) (w j)` yields the
corresponding support inclusion and cardinality bound for finite linear combinations of variables.

## Main results

* `MvPolynomial.support_sum_monomial_subset`:
  `(∑ j ∈ s, monomial (a j) (w j)).support ⊆ s.image a`.
* `MvPolynomial.card_support_sum_monomial_le`:
  `#(∑ j ∈ s, monomial (a j) (w j)).support ≤ #s`.
* `MvPolynomial.support_sum_C_mul_X_subset`:
  `(∑ j ∈ s, C (w j) * X (g j)).support ⊆ s.image fun j ↦ Finsupp.single (g j) 1`.
* `MvPolynomial.card_support_sum_C_mul_X_le`:
  `#(∑ j ∈ s, C (w j) * X (g j)).support ≤ #s`.
-/

public section

open Finset

namespace MvPolynomial

variable {ι σ R : Type*} [CommSemiring R]

/-- The support of a finite sum of monomials `∑ j ∈ s, monomial (a j) (w j)` is contained in the
image of `s` under `a`. -/
theorem support_sum_monomial_subset [DecidableEq σ] (s : Finset ι) (a : ι → σ →₀ ℕ) (w : ι → R) :
    (∑ j ∈ s, monomial (a j) (w j)).support ⊆ s.image a :=
  support_sum.trans (biUnion_subset.2 fun _ hj ↦
    support_monomial_subset.trans (singleton_subset_iff.2 (mem_image_of_mem _ hj)))

/-- A finite sum of monomials `∑ j ∈ s, monomial (a j) (w j)` has at most `#s` monomials in its
support. -/
theorem card_support_sum_monomial_le (s : Finset ι) (a : ι → σ →₀ ℕ) (w : ι → R) :
    #(∑ j ∈ s, monomial (a j) (w j)).support ≤ #s := by
  classical
  exact (card_le_card (support_sum_monomial_subset s a w)).trans card_image_le

/-- The support of a finite linear combination `∑ j ∈ s, C (w j) * X (g j)` is contained in the
image of `s` under `j ↦ Finsupp.single (g j) 1`. -/
theorem support_sum_C_mul_X_subset [DecidableEq σ] (s : Finset ι) (w : ι → R) (g : ι → σ) :
    (∑ j ∈ s, C (w j) * X (g j) : MvPolynomial σ R).support ⊆
      s.image fun j ↦ Finsupp.single (g j) 1 := by
  simp_rw [C_mul_X_eq_monomial]
  exact support_sum_monomial_subset s (fun j ↦ Finsupp.single (g j) 1) w

/-- A finite linear combination `∑ j ∈ s, C (w j) * X (g j)` has at most `#s` monomials in its
support. -/
theorem card_support_sum_C_mul_X_le (s : Finset ι) (w : ι → R) (g : ι → σ) :
    #(∑ j ∈ s, C (w j) * X (g j) : MvPolynomial σ R).support ≤ #s := by
  simp_rw [C_mul_X_eq_monomial]
  exact card_support_sum_monomial_le s (fun j ↦ Finsupp.single (g j) 1) w

end MvPolynomial
