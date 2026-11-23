/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.RingTheory.MvPolynomial.Box
import TauCeti.RingTheory.MvPolynomial.RestrictSupport
import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

/-!
# Examples of coefficient-supported polynomial spaces

The box of bidegrees at most `(1, 2)` and the total-degree ball of radius `2` both have rank
`6`, but have different monomials. Empty and constant supports, the zero coefficient ring, and
the equality with the univariate degree space test the boundaries of this dictionary.
-/

open MvPolynomial Finsupp

namespace TauCeti.CoefficientSupportExamples

/-- The bidegree box `(1, 2)` has six independent coefficients over a ring with strong rank
condition. -/
example (R : Type*) [CommSemiring R] [StrongRankCondition R] :
    Module.finrank R (restrictSupport R {μ : Fin 2 →₀ ℕ | ∀ j, μ j ≤ ![1, 2] j}) = 6 := by
  rw [finrank_restrictSupport, ← range_boxMonomial]
  rw [← Nat.card_congr (Equiv.ofInjective _ boxMonomial_injective)]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_pi, Fin.prod_univ_two]

/-- The total-degree ball of radius two also has rank six. -/
example (R : Type*) [CommSemiring R] [StrongRankCondition R] :
    Module.finrank R (restrictTotalDegree (Fin 2) R 2) = 6 := by
  norm_num [TauCeti.finrank_restrictTotalDegree, Nat.choose]

/-- `Z W²` belongs to the box but exceeds the total-degree bound. -/
example : X 0 * X 1 ^ 2 ∈
      restrictSupport ℤ {μ : Fin 2 →₀ ℕ | ∀ j, μ j ≤ ![1, 2] j} ∧
    X 0 * X 1 ^ 2 ∉ restrictTotalDegree (Fin 2) ℤ 2 := by
  norm_num [X, monomial_pow, monomial_mul_monomial, mem_restrictTotalDegree,
    totalDegree_monomial, Fin.forall_fin_two, Finsupp.sum_fintype, Fin.sum_univ_two]

/-- `Z²` belongs to the total-degree ball but exceeds the first coordinate of the box. -/
example : X 0 ^ 2 ∈ restrictTotalDegree (Fin 2) ℤ 2 ∧
    X 0 ^ 2 ∉ restrictSupport ℤ {μ : Fin 2 →₀ ℕ | ∀ j, μ j ≤ ![1, 2] j} := by
  norm_num [X_pow_eq_monomial, mem_restrictTotalDegree, totalDegree_monomial,
    Fin.forall_fin_two]

/-- Empty support gives the zero submodule, even over the zero ring. -/
example (R σ : Type*) [CommSemiring R] :
    restrictSupport R (∅ : Set (σ →₀ ℕ)) = ⊥ := by
  simp [restrictSupport_eq_span]

/-- The empty-support space has rank zero over any nontrivial coefficient semiring. -/
example (R σ : Type*) [CommSemiring R] [Nontrivial R] :
    Module.finrank R (restrictSupport R (∅ : Set (σ →₀ ℕ))) = 0 := by
  rw [restrictSupport_eq_span, Set.image_empty, Submodule.span_empty, finrank_bot]

/-- Support in `{0}` characterizes constant polynomials. -/
example (R σ : Type*) [CommSemiring R] (p : MvPolynomial σ R) :
    p ∈ restrictSupport R {0} ↔ ∃ r, p = C r := by
  simp [restrictSupport_eq_span, Submodule.mem_span_singleton, smul_eq_C_mul, eq_comm]

/-- In the singleton monomial basis the sole coordinate of a constant is its value. -/
example (R σ : Type*) [CommSemiring R] (r : R) :
    (basisRestrictSupport R ({0} : Set (σ →₀ ℕ))).repr
      ⟨C r, by
        simp only [C_apply, monomial_mem_restrictSupport, Set.mem_singleton_iff, true_or]⟩
      ⟨0, rfl⟩ = r := by
  simp

/-- Over the zero ring every support restriction is the zero submodule. This does not assert
a rank formula for that ring. -/
example (R σ : Type*) [CommSemiring R] [Subsingleton R] (s : Set (σ →₀ ℕ)) :
    restrictSupport R s = ⊥ := by
  exact Subsingleton.elim _ _

/-- In one variable the support box maps onto the whole degree space, with equality of
submodules. -/
example (R : Type*) [CommSemiring R] :
    (restrictSupport R {μ : Fin 1 →₀ ℕ | μ 0 < 3}).map
      (uniqueAlgEquiv R (Fin 1)).toLinearMap = Polynomial.degreeLT R 3 := by
  exact map_restrictSupport_uniqueAlgEquiv 3

/-- The strict degree cutoff accepts `X²` and excludes `X³` over any nontrivial coefficient
semiring. -/
example (R : Type*) [CommSemiring R] [Nontrivial R] :
    (Polynomial.X : Polynomial R) ^ 2 ∈ Polynomial.degreeLT R 3 ∧
      (Polynomial.X : Polynomial R) ^ 3 ∉ Polynomial.degreeLT R 3 := by
  norm_num [Polynomial.mem_degreeLT]

end TauCeti.CoefficientSupportExamples
