/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Leading monomials for a monomial order

This file collects facts about leading monomials of multivariate polynomials for a monomial order
`m` on `σ →₀ ℕ`: the degree of a monomial multiple, the cancellation of leading terms by an
S-polynomial, and algebraic independence from leading monomials.

The product `X^a * b`, normalized to leading coefficient one when `b` has a unit leading
coefficient, differs from another such product of the same degree by a monomial multiple of
their S-polynomial. This is the cancellation of leading terms behind Buchberger's criterion.

Let `yᵢ`, `i ∈ σ`, be polynomials in the variables `Xᵢ` over a ring without zero divisors. If the
leading monomial of each `yᵢ` is the variable `Xᵢ`, then the `yᵢ` are algebraically independent:
the image of a monomial `c X^d` under `Xᵢ ↦ yᵢ` has leading monomial `X^d`, so the images of the
distinct monomials of a nonzero polynomial have distinct leading monomials and cannot cancel.

This is the triangularity argument for a family such as `yₙ = cₙ Xₙ + qₙ(X₁, …, Xₙ₋₁)` with
`cₙ ≠ 0`, ordered lexicographically with the variables of larger index more significant, as for
the images of the generators of the Lazard ring in a polynomial ring.

## Main results

* `MonomialOrder.toSyn_degree_monomial_mul_le`: `c X^a * b` has degree at most `a + deg b`.
* `MonomialOrder.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial`: if `b₀` has a unit
  leading coefficient, then `X^a * b` minus `lc b` times the product of `b₀` of the same degree
  normalized to leading coefficient one is a monomial multiple of the S-polynomial
  `m.sPolynomial b b₀`.
* `MonomialOrder.algebraicIndependent_of_degree_eq_single`: polynomials `yᵢ` whose leading
  monomial is `Xᵢ` are algebraically independent.
-/

public section

open MvPolynomial

namespace MonomialOrder

variable {σ R : Type*} (m : MonomialOrder σ)

/-- A monomial multiple `c X^a * b` has degree at most `a + deg b`. -/
theorem toSyn_degree_monomial_mul_le [CommSemiring R] (a : σ →₀ ℕ) (c : R)
    (b : MvPolynomial σ R) : m.toSyn (m.degree (monomial a c * b)) ≤ m.toSyn (a + m.degree b) := by
  rw [map_add]
  exact m.toSyn_degree_mul_le.trans (by gcongr; exact m.degree_monomial_le c)

/-- **Cancellation of leading terms by an S-polynomial.** If `b₀` has unit leading coefficient
`u₀` and `deg b₀ ≤ a + deg b`, the difference between `X^a * b` and `lc b` times the normalized
product `X^(a + deg b - deg b₀) * b₀ / lc b₀` is `X^(a + deg b - L) / lc b₀ * S(b, b₀)`, where
`L = deg b ⊔ deg b₀`. -/
theorem monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial [CommRing R] {a : σ →₀ ℕ}
    {b b₀ : MvPolynomial σ R} (hb₀ : m.degree b₀ ≤ a + m.degree b) (u₀ : Rˣ)
    (hu₀ : (u₀ : R) = m.leadingCoeff b₀) :
    monomial a 1 * b -
        m.leadingCoeff b • (monomial (a + m.degree b - m.degree b₀) ((u₀⁻¹ : Rˣ) : R) * b₀) =
      monomial (a + m.degree b - m.degree b ⊔ m.degree b₀) ((u₀⁻¹ : Rˣ) : R) *
        m.sPolynomial b b₀ := by
  have hL : m.degree b ⊔ m.degree b₀ ≤ a + m.degree b := sup_le le_add_self hb₀
  -- The exponents of the two summands of the right-hand side.
  have e₁ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b) =
      a := by
    rw [tsub_add_tsub_cancel hL le_sup_left, add_tsub_cancel_right]
  have e₂ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b₀) =
      a + m.degree b - m.degree b₀ :=
    tsub_add_tsub_cancel hL le_sup_right
  -- The coefficient of the first summand.
  have hc : ((u₀⁻¹ : Rˣ) : R) * m.leadingCoeff b₀ = 1 := by rw [← hu₀, Units.inv_mul]
  simp only [sPolynomial_def, mul_sub, ← mul_assoc, monomial_mul_monomial, smul_eq_C_mul,
    C_mul_monomial, e₁, e₂, hc, mul_comm (m.leadingCoeff b)]

variable [CommRing R] [NoZeroDivisors R]

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
