/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Partial derivatives of multivariate polynomials: chain rule, degree and coefficients

Substituting polynomials `fᵢ ∈ R[Y_τ]` for the variables `Xᵢ` of `p ∈ R[X_σ]` and differentiating
with respect to `Y_j` obeys the chain rule

`∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j`,

where the sum runs over any finite set of indices containing the variables of `p`.

Partial differentiation lowers the total degree by at least one, so the `k`-th iterated partial
derivative of a polynomial of total degree less than `k` vanishes, and it keeps the coefficients
in any additive submonoid of the coefficient ring, such as a subring. These are the facts needed
to clear the denominators of derivatives of polynomials evaluated at algebraic points.

## Main results

* `MvPolynomial.pderiv_aeval`: the chain rule, summed over all variables of a finite type.
* `MvPolynomial.pderiv_aeval_of_vars_subset`: the chain rule, summed over a finite set containing
  the variables of `p`.
* `MvPolynomial.totalDegree_iterate_pderiv_le`: the `k`-th iterated partial derivative has total
  degree at most `totalDegree p - k`.
* `MvPolynomial.iterate_pderiv_eq_zero_of_totalDegree_lt`: it vanishes when `totalDegree p < k`.
* `MvPolynomial.coeff_iterate_pderiv_mem`: iterated partial derivatives keep the coefficients in
  an additive submonoid.
* `MvPolynomial.iterate_pderiv_prod_aeval_X`: on a separated product `∏ⱼ Qⱼ(Xⱼ)` of one-variable
  polynomials, the `k`-th iterated partial derivative along `Xᵢ` is `Qᵢ⁽ᵏ⁾(Xᵢ) ∏_{j ≠ i} Qⱼ(Xⱼ)`.
-/

public section

namespace MvPolynomial

variable {R σ τ : Type*} [CommSemiring R]

/-- **The chain rule**: `∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j` for a substitution
`Xᵢ ↦ fᵢ` of polynomials in the variables `Y`. -/
theorem pderiv_aeval [Fintype σ] (f : σ → MvPolynomial τ R) (j : τ) (p : MvPolynomial σ R) :
    pderiv j (aeval f p) = ∑ i, aeval f (pderiv i p) * pderiv j (f i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, pderiv_X, map_add,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single i (fun m _ hm ↦ by simp [hm]) (by simp)]
      simp [mul_comm]
    · refine Finset.sum_congr rfl fun m _ ↦ ?_
      ring

/-- **The chain rule** over an arbitrary type of variables:
`∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j`, the sum running over any finite set `s` containing the
variables of `p`. -/
theorem pderiv_aeval_of_vars_subset (f : σ → MvPolynomial τ R) (j : τ) {p : MvPolynomial σ R}
    {s : Finset σ} (hs : p.vars ⊆ s) :
    pderiv j (aeval f p) = ∑ i ∈ s, aeval f (pderiv i p) * pderiv j (f i) := by
  -- Write `p` as a polynomial in the variables indexed by `s` and apply the finite chain rule.
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p ((↑) : s → σ) Subtype.val_injective
    (by simpa using hs)
  rw [aeval_rename, pderiv_aeval, ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pderiv_rename Subtype.val_injective, aeval_rename, Function.comp_apply]

/-- Partial differentiation lowers the total degree by at least one. -/
theorem totalDegree_pderiv_le (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  refine Finset.sup_le fun m hm ↦ ?_
  rw [mem_support_iff, coeff_pderiv] at hm
  have h := le_totalDegree (mem_support_iff.2 (left_ne_zero_of_mul hm))
  rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
    Finsupp.sum_single_index rfl] at h
  omega

/-- The `k`-th iterated partial derivative lowers the total degree by at least `k`. -/
theorem totalDegree_iterate_pderiv_le (i : σ) (k : ℕ) (p : MvPolynomial σ R) :
    ((pderiv i)^[k] p).totalDegree ≤ p.totalDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := totalDegree_pderiv_le i ((pderiv i)^[k] p)
    omega

/-- The `k`-th iterated partial derivative of a polynomial of total degree less than `k`
vanishes. -/
theorem iterate_pderiv_eq_zero_of_totalDegree_lt {i : σ} {k : ℕ} {p : MvPolynomial σ R}
    (h : p.totalDegree < k) : (pderiv i)^[k] p = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [Function.iterate_succ_apply', totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1
    ((totalDegree_iterate_pderiv_le i _ p).trans (by omega))), pderiv_C]

/-- Partial differentiation keeps the coefficients in an additive submonoid of the coefficient
ring, such as a subring. -/
theorem coeff_pderiv_mem {S : Type*} [SetLike S R] [AddSubmonoidClass S R] {s : S}
    {p : MvPolynomial σ R} (hp : ∀ m, p.coeff m ∈ s) (i : σ) (m : σ →₀ ℕ) :
    (pderiv i p).coeff m ∈ s := by
  rw [coeff_pderiv, ← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]
  exact nsmul_mem (hp _) _

/-- Iterated partial differentiation keeps the coefficients in an additive submonoid of the
coefficient ring, such as a subring. -/
theorem coeff_iterate_pderiv_mem {S : Type*} [SetLike S R] [AddSubmonoidClass S R] {s : S}
    {p : MvPolynomial σ R} (hp : ∀ m, p.coeff m ∈ s) (i : σ) (k : ℕ) (m : σ →₀ ℕ) :
    ((pderiv i)^[k] p).coeff m ∈ s := by
  induction k generalizing m with
  | zero => exact hp m
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact coeff_pderiv_mem ih i m

/-- Iterated partial differentiation along `Xᵢ` of a one-variable polynomial in `Xᵢ` is iterated
differentiation of the polynomial. -/
theorem iterate_pderiv_aeval_X_self (i : σ) (k : ℕ) (p : Polynomial R) :
    (pderiv i)^[k] (Polynomial.aeval (X i : MvPolynomial σ R) p) =
      Polynomial.aeval (X i) (Polynomial.derivative^[k] p) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

/-- **Partial derivatives of a separated product.** For one-variable polynomials `Qⱼ` and
`i ∈ s`, the `k`-th iterated partial derivative along `Xᵢ` of `∏_{j ∈ s} Qⱼ(Xⱼ)` is
`Qᵢ⁽ᵏ⁾(Xᵢ) ∏_{j ∈ s, j ≠ i} Qⱼ(Xⱼ)`: the other factors do not involve `Xᵢ`. -/
theorem iterate_pderiv_prod_aeval_X [DecidableEq σ] {s : Finset σ} {i : σ} (hi : i ∈ s)
    (Q : σ → Polynomial R) (k : ℕ) :
    (pderiv i)^[k] (∏ j ∈ s, Polynomial.aeval (X j : MvPolynomial σ R) (Q j)) =
      Polynomial.aeval (X i) (Polynomial.derivative^[k] (Q i)) *
        ∏ j ∈ s.erase i, Polynomial.aeval (X j) (Q j) := by
  set g := ∏ j ∈ s.erase i, Polynomial.aeval (X j : MvPolynomial σ R) (Q j)
  have hg : pderiv i g = 0 := by
    have key : ∀ t : Finset σ, i ∉ t →
        pderiv i (∏ j ∈ t, Polynomial.aeval (X j : MvPolynomial σ R) (Q j)) = 0 := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert j t hj ih =>
        intro hit
        rw [Finset.mem_insert, not_or] at hit
        rw [Finset.prod_insert hj, Derivation.leibniz, ih hit.2, Derivation.map_aeval,
          pderiv_X_of_ne (Ne.symm hit.1)]
        simp
    exact key _ (Finset.notMem_erase i s)
  rw [← Finset.mul_prod_erase s _ hi, ← iterate_pderiv_aeval_X_self]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, Function.iterate_succ_apply']
    simp [hg, mul_comm]

end MvPolynomial
