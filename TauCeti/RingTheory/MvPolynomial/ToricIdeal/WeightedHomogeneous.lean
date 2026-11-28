/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.MvPolynomial.ToricIdeal.Basic
import TauCeti.Data.Finsupp.Weight

/-!
# Weighted homogeneity of toric ideals

Every binomial `X^u - X^v` in the toric ideal `TauCeti.toricIdeal R a` has `∑ i, u i • a i =
∑ i, v i • a i`, so for any additive degree homomorphism `deg : M →+ D`, it is weighted homogeneous
with respect to the pulled-back weights `deg ∘ a`.

## Main declarations

* `TauCeti.isWeightedHomogeneous_monomial_sub_monomial_of_mem_toricIdeal`: a binomial in the toric
  ideal of `a` is weighted homogeneous for pulled-back weights `deg ∘ a`.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 4.
-/

public section

open MvPolynomial

namespace TauCeti

variable {ι M D R : Type*} [AddCommMonoid M] [AddCommMonoid D] [CommRing R]

/-- A binomial in the toric ideal of `a` is weighted homogeneous for the pulled-back weights
`deg ∘ a`. -/
theorem isWeightedHomogeneous_monomial_sub_monomial_of_mem_toricIdeal
    {a : ι → M} {deg : M →+ D} {u v : ι →₀ ℕ}
    (h : monomial u (1 : R) - monomial v 1 ∈ toricIdeal R a) :
    (monomial u (1 : R) - monomial v 1).IsWeightedHomogeneous (deg ∘ a)
      (Finsupp.weight (deg ∘ a) u) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (monomial u (1 : R) - monomial v 1) 0]
    exact isWeightedHomogeneous_zero R _ _
  have huv : Finsupp.linearCombination ℕ a u = Finsupp.linearCombination ℕ a v :=
    monomial_sub_monomial_mem_toricIdeal_iff.1 h
  have hw (x : ι →₀ ℕ) : Finsupp.weight (deg ∘ a) x = deg (Finsupp.linearCombination ℕ a x) :=
    Finsupp.weight_comp_eq_apply_linearCombination deg a x
  exact (isWeightedHomogeneous_monomial _ _ _ rfl).sub
    (isWeightedHomogeneous_monomial _ _ _ (by rw [hw, hw, huv]))

end TauCeti
