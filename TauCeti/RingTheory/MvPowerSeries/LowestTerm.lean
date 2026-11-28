/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic.Linarith

/-!
# Weighted lowest terms of multivariate power series

For a weight function w : X → ℕ, a monomial c • z ^ m is the *lowest term* of a multivariate
power series  : MvPowerSeries X R (TauCeti.IsLowestTerm w f m c) if every coefficient of 
in weighted degree at most m.weight w agrees with the coefficient of monomial m c.

## Main definitions and results

* TauCeti.IsLowestTerm: c • z ^ m is the lowest term of  for the weight w.
* TauCeti.IsLowestTerm.one: 1 has lowest term 1 • z ^ 0.
* TauCeti.IsLowestTerm.mul: the lowest term of  * g is (c * d) • z ^ (D + D').
* TauCeti.IsLowestTerm.prod: the lowest term of ∏ i ∈ s, f i is (∏ i ∈ s, c i) • z ^ ∑ α i.
* TauCeti.IsLowestTerm.pow: the lowest term of  ^ k is c ^ k • z ^ (k • α).

## Provenance

Adapted from New.IsLowestTerm, New.IsLowestTerm.mul, New.IsLowestTerm.prod, and
New.IsLowestTerm.pow in src/New/Derivatives/Sharpness/LeastValuation.lean of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
72fead102f663d5c7a407964a13dc0cf9d977207 (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Finset MvPowerSeries

section CommSemiring

variable {X R : Type*} [CommSemiring R]

/-- c • z ^ m is the lowest term of  for the weight w: in weighted degree at most that of
m, every coefficient of  agrees with the coefficient of monomial m c. -/
def IsLowestTerm (w : X → ℕ) (f : MvPowerSeries X R) (m : X →₀ ℕ) (c : R) : Prop :=
  ∀ d : X →₀ ℕ, d.weight w ≤ m.weight w → coeff d f = coeff d (monomial m c)

/-- The constant series 1 has lowest term 1 • z ^ 0 for any weight w. -/
theorem IsLowestTerm.one (w : X → ℕ) : IsLowestTerm w (1 : MvPowerSeries X R) 0 1 := by
  intro d _
  simp [monomial_zero_one]

/-- The lowest term of a product is the product of the lowest terms: if  has lowest term
c • z ^ D and g has lowest term d • z ^ D' for the weight w, then  * g has lowest term
(c * d) • z ^ (D + D'). -/
theorem IsLowestTerm.mul {w : X → ℕ} {f g : MvPowerSeries X R} {D D' : X →₀ ℕ} {c d : R}
    (hf : IsLowestTerm w f D c) (hg : IsLowestTerm w g D' d) :
    IsLowestTerm w (f * g) (D + D') (c * d) := by
  classical
  intro e he
  rw [← monomial_mul_monomial, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun ⟨x, y⟩ hxy ↦ ?_
  obtain rfl : x + y = e := mem_antidiagonal.1 hxy
  rw [map_add, map_add] at he
  by_cases hx : x.weight w ≤ D.weight w
  · by_cases hy : y.weight w ≤ D'.weight w
    · rw [hf x hx, hg y hy]
    · rw [hf x hx, coeff_monomial_ne (fun h ↦ by subst h; linarith), zero_mul, zero_mul]
  · rw [hg y (by linarith), coeff_monomial_ne (fun h ↦ by subst h; linarith), mul_zero, mul_zero]

/-- If each factor  i has lowest term c i • z ^ α i for the weight w, then the finite
product ∏ i ∈ s, f i has lowest term (∏ i ∈ s, c i) • z ^ (∑ i ∈ s, α i). -/
theorem IsLowestTerm.prod {ι : Type*} {w : X → ℕ} {s : Finset ι} {f : ι → MvPowerSeries X R}
    {α : ι → X →₀ ℕ} {c : ι → R} (hf : ∀ i ∈ s, IsLowestTerm w (f i) (α i) (c i)) :
    IsLowestTerm w (∏ i ∈ s, f i) (∑ i ∈ s, α i) (∏ i ∈ s, c i) := by
  induction s using cons_induction with
  | empty => simpa using IsLowestTerm.one w
  | cons i s hi ih =>
    simp only [prod_cons, sum_cons]
    exact (hf i (mem_cons_self i s)).mul (ih fun j hj ↦ hf j (mem_cons_of_mem hj))

/-- If  has lowest term c • z ^ α for the weight w, then  ^ k has lowest term
c ^ k • z ^ (k • α). -/
theorem IsLowestTerm.pow {w : X → ℕ} {f : MvPowerSeries X R} {α : X →₀ ℕ} {c : R}
    (hf : IsLowestTerm w f α c) (k : ℕ) :
    IsLowestTerm w (f ^ k) (k • α) (c ^ k) := by
  simpa using IsLowestTerm.prod (s := range k) fun _ _ ↦ hf

end CommSemiring

end TauCeti
