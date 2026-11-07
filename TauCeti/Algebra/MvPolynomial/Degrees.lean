/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Partial and block degrees of multivariate polynomials

A ring homomorphism `f : R →+* S` applied to the coefficients of a multivariate polynomial `P`
can only remove monomials, so it does not raise any partial degree. This is the partial-degree
form of Mathlib's `MvPolynomial.degrees_map_le`.

When variables `j : S` are grouped into blocks by `b : S → B` with degree bounds `d : B → ℕ`, the
block degree of an exponent `e : S →₀ ℕ` in block `h` is `e.mapDomain b h`. Such support bounds
hold for constants and bounded powers of variables and are preserved under addition, negation, and
subtraction.

## Main results

* `MvPolynomial.degreeOf_map_le`: `degreeOf i (P.map f) ≤ degreeOf i P`.
* `MvPolynomial.mapDomain_le_of_mem_support_C`, `MvPolynomial.mapDomain_le_of_mem_support_one`,
  `MvPolynomial.mapDomain_le_of_mem_support_X_pow`, `MvPolynomial.mapDomain_le_of_mem_support_X`,
  `MvPolynomial.mapDomain_le_of_mem_support_add`, `MvPolynomial.mapDomain_le_of_mem_support_neg`,
  `MvPolynomial.mapDomain_le_of_mem_support_sub`: closure of block degree bounds on polynomial
  supports.
-/

public section

namespace MvPolynomial

/-- Mapping the coefficients of `P` does not raise its degree in `Xᵢ`. -/
theorem degreeOf_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (P : MvPolynomial σ R) (i : σ) : (P.map f).degreeOf i ≤ P.degreeOf i :=
  degreeOf_le_iff.2 fun _ hs ↦ monomial_le_degreeOf i (support_map_subset f P hs)

section BlockDegree

open Finsupp

section CommSemiring

variable {R B S : Type*} [CommSemiring R] (b : S → B) (d : B → ℕ)

/-- Any constant polynomial `C c` satisfies every block degree bound `d`. -/
theorem mapDomain_le_of_mem_support_C (c : R) ⦃e : S →₀ ℕ⦄
    (he : e ∈ (C c : MvPolynomial S R).support) (h : B) :
    e.mapDomain b h ≤ d h := by
  rw [C_apply] at he
  rw [Finset.mem_singleton.1 (support_monomial_subset he)]
  simp

/-- The constant polynomial `1` satisfies every block degree bound `d`. -/
theorem mapDomain_le_of_mem_support_one ⦃e : S →₀ ℕ⦄
    (he : e ∈ (1 : MvPolynomial S R).support) (h : B) :
    e.mapDomain b h ≤ d h := by
  rw [← C_1] at he
  exact mapDomain_le_of_mem_support_C b d 1 he h

/-- A power `X j ^ k` with `k ≤ d (b j)` satisfies the block degree bounds `d`. -/
theorem mapDomain_le_of_mem_support_X_pow {j : S} {k : ℕ} (hk : k ≤ d (b j)) ⦃e : S →₀ ℕ⦄
    (he : e ∈ (X j ^ k : MvPolynomial S R).support) (h : B) :
    e.mapDomain b h ≤ d h := by
  rw [X_pow_eq_monomial] at he
  rw [Finset.mem_singleton.1 (support_monomial_subset he), mapDomain_single]
  by_cases hbj : b j = h
  · subst hbj
    simpa using hk
  · simp [hbj]

/-- A variable `X j` with `1 ≤ d (b j)` satisfies the block degree bounds `d`. -/
theorem mapDomain_le_of_mem_support_X {j : S} (hj : 1 ≤ d (b j)) ⦃e : S →₀ ℕ⦄
    (he : e ∈ (X j : MvPolynomial S R).support) (h : B) :
    e.mapDomain b h ≤ d h := by
  rw [← pow_one (X j)] at he
  exact mapDomain_le_of_mem_support_X_pow b d hj he h

/-- Block degree bounds `d` on the supports of `f` and `g` carry over to `f + g`. -/
theorem mapDomain_le_of_mem_support_add {f g : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h)
    (hg : ∀ e ∈ g.support, ∀ h, e.mapDomain b h ≤ d h) ⦃e : S →₀ ℕ⦄
    (he : e ∈ (f + g).support) (h : B) :
    e.mapDomain b h ≤ d h := by
  classical
  rcases Finset.mem_union.1 (support_add he) with hef | heg
  · exact hf e hef h
  · exact hg e heg h

end CommSemiring

section CommRing

variable {R B S : Type*} [CommRing R] (b : S → B) (d : B → ℕ)

/-- Block degree bounds `d` on the support of `f` carry over to `-f`. -/
theorem mapDomain_le_of_mem_support_neg {f : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h) ⦃e : S →₀ ℕ⦄
    (he : e ∈ (-f).support) (h : B) :
    e.mapDomain b h ≤ d h := by
  rw [← neg_one_smul R f] at he
  exact hf e (support_smul he) h

/-- Block degree bounds `d` on the supports of `f` and `g` carry over to `f - g`. -/
theorem mapDomain_le_of_mem_support_sub {f g : MvPolynomial S R}
    (hf : ∀ e ∈ f.support, ∀ h, e.mapDomain b h ≤ d h)
    (hg : ∀ e ∈ g.support, ∀ h, e.mapDomain b h ≤ d h) ⦃e : S →₀ ℕ⦄
    (he : e ∈ (f - g).support) (h : B) :
    e.mapDomain b h ≤ d h := by
  rw [sub_eq_add_neg] at he
  exact mapDomain_le_of_mem_support_add b d hf (mapDomain_le_of_mem_support_neg b d hg) he h

end CommRing

end BlockDegree

end MvPolynomial
