/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Monomial-order degree bounds and algebraic independence

The degree bounds `MonomialOrder.toWithBotSyn_withBotDegree_le_toSyn_degree` and
`MonomialOrder.withBotDegree_sub_lt` compare polynomial degrees with their `WithBot` forms.

Let `m` be a monomial order on `σ →₀ ℕ` and let `yᵢ`, `i ∈ σ`, be polynomials in the variables
`Xᵢ` over a ring without zero divisors. If the leading monomial of each `yᵢ` is the variable
`Xᵢ`, then the `yᵢ` are algebraically independent: the image of a monomial `c X^d` under
`Xᵢ ↦ yᵢ` has leading monomial `X^d`, so the images of the distinct monomials of a nonzero
polynomial have distinct leading monomials and cannot cancel.

This is the triangularity argument for a family such as `yₙ = cₙ Xₙ + qₙ(X₁, …, Xₙ₋₁)` with
`cₙ ≠ 0`, ordered lexicographically with the variables of larger index more significant, as for
the images of the generators of the Lazard ring in a polynomial ring.

## Main results

* `MonomialOrder.algebraicIndependent_of_degree_eq_single`: polynomials `yᵢ` whose leading
  monomial is `Xᵢ` are algebraically independent.
-/

public section

open MvPolynomial

namespace MonomialOrder

section DegreeBounds

variable {σ R : Type*} (m : MonomialOrder σ)

variable [CommSemiring R]

/-- The `WithBot` degree of a polynomial is at most its degree. -/
theorem toWithBotSyn_withBotDegree_le_toSyn_degree (p : MvPolynomial σ R) :
    m.toWithBotSyn (m.withBotDegree p) ≤ m.toSyn (m.degree p) := by
  classical
  rw [withBotDegree_eq]
  split_ifs <;> simp [toWithBotSyn_apply_coe]

end DegreeBounds

section SubDegree

variable {σ R : Type*} [CommRing R] (m : MonomialOrder σ)

/-- If `q` has degree at most that of `f ≠ 0` and the same coefficient of `X^(deg f)`, then
`f - q` has smaller degree than `f`. -/
theorem withBotDegree_sub_lt {f q : MvPolynomial σ R} (hf : f ≠ 0)
    (hq : m.toWithBotSyn (m.withBotDegree q) ≤ m.toWithBotSyn (m.withBotDegree f))
    (hqf : q.coeff (m.degree f) = m.leadingCoeff f) :
    m.toWithBotSyn (m.withBotDegree (f - q)) < m.toWithBotSyn (m.withBotDegree f) := by
  refine lt_of_le_of_ne ?_ fun heq ↦ ?_
  · simpa [sub_eq_add_neg] using
      (m.withBotDegree_add_le f (-q)).trans (max_le le_rfl (by rwa [withBotDegree_neg]))
  rw [EmbeddingLike.apply_eq_iff_eq, withBotDegree_eq_withBotDegree_iff] at heq
  have := m.degree_mem_support fun h0 ↦ hf (heq.2.1 h0)
  rw [heq.1, mem_support_iff, coeff_sub, hqf, leadingCoeff, sub_self] at this
  exact this rfl

end SubDegree

variable {σ R : Type*} [CommRing R] [NoZeroDivisors R] (m : MonomialOrder σ)

/-- **Algebraic independence from leading monomials.** Over a ring without zero divisors, a family
`yᵢ` of polynomials in the variables `Xᵢ` whose leading monomial for a monomial order is `Xᵢ` is
algebraically independent. -/
theorem algebraicIndependent_of_degree_eq_single {y : σ → MvPolynomial σ R}
    (hy : ∀ i, m.degree (y i) = Finsupp.single i 1) : AlgebraicIndependent R y := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact algebraicIndependent_iff_injective_aeval.2 fun _ _ _ ↦ Subsingleton.elim _ _
  have hy0 (i : σ) : y i ≠ 0 := fun h ↦ by
    simpa [h] using congrArg (fun d ↦ d i) (hy i)
  have hne (d : σ →₀ ℕ) : (d.prod fun i k ↦ y i ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hy0 i)
  -- The image `c ∏ yᵢ ^ dᵢ` of a monomial `c X^d` with `c ≠ 0` has leading monomial `X^d`.
  have hterm {c : R} (hc : c ≠ 0) (d : σ →₀ ℕ) : m.degree (aeval y (monomial d c)) = d := by
    rw [aeval_monomial, algebraMap_eq, m.degree_mul (C_ne_zero.2 hc) (hne d), m.degree_C,
      zero_add, Finsupp.prod, m.degree_prod fun i _ ↦ pow_ne_zero _ (hy0 i)]
    simp_rw [m.degree_pow, hy, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact d.sum_single
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  rw [p.as_sum, map_sum] at hp
  -- The images of the monomials of `p` have pairwise distinct leading monomials, so their sum is
  -- nonzero.
  refine AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree (D := m.toSyn)
    (support_nonempty.2 hp0) (fun d hd ↦ ?_) (fun d hd e he hde ↦ ?_) hp
  · rw [aeval_monomial, algebraMap_eq]
    exact mul_ne_zero (C_ne_zero.2 (mem_support_iff.1 hd)) (hne d)
  · have key (d : σ →₀ ℕ) (hd : d ∈ p.support) :
        AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) = m.toSyn d := by
      -- `m.degree` is defined as the supremum `AddMonoidAlgebra.supDegree m.toSyn`, read back
      -- through `m.toSyn`.
      have h : m.toSyn (m.degree (aeval y (monomial d (p.coeff d)))) =
          AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) := by
        rw [degree, AddEquiv.apply_symm_apply]
        rfl
      rw [← h, hterm (mem_support_iff.1 hd)]
    simpa [key d hd, key e he] using hde

end MonomialOrder
