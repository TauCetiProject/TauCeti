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

Over a commutative ring the gradient at a point `t` linearises a polynomial up to a divisibility
error: if `d ∣ xᵢ - tᵢ`, `d ∣ e` and `e ∣ x'ᵢ - xᵢ`, then `p(x') - p(x) - ∑ⱼ ∂ⱼp(t) (x'ⱼ - xⱼ)` is
divisible by `d * e`. This is the several-variable form of
`Polynomial.mul_dvd_eval_sub_eval_sub_mul` and the estimate behind Newton's method with an
approximately invertible Jacobian.

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
* `MvPolynomial.dvd_eval_sub_eval`: values at points congruent modulo `d` are congruent modulo `d`.
* `MvPolynomial.mul_dvd_eval_sub_eval_sub_sum_pderiv`: Taylor's estimate
  `d * e ∣ p(x') - p(x) - ∑ⱼ ∂ⱼp(t) (x'ⱼ - xⱼ)`.
-/

public section

namespace MvPolynomial

section CommSemiring

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

end CommSemiring

section CommRing

variable {R σ : Type*} [CommRing R]

/-- The values of a polynomial at points that agree modulo `d` agree modulo `d`. -/
theorem dvd_eval_sub_eval (p : MvPolynomial σ R) {d : R} {x t : σ → R}
    (h : ∀ i, d ∣ x i - t i) : d ∣ eval x p - eval t p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa [add_sub_add_comm] using dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, eval_X, eval_X,
      show eval x p * x i - eval t p * t i = (eval x p - eval t p) * x i + eval t p * (x i - t i) by
        ring]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right (h i) _)

/-- **Taylor's estimate in several variables.** If `d ∣ xᵢ - tᵢ`, `d ∣ e` and `e ∣ x'ᵢ - xᵢ` for
every `i`, then the gradient at `t` linearises `p` from `x` to `x'` up to an error divisible by
`d * e`. -/
theorem mul_dvd_eval_sub_eval_sub_sum_pderiv [Fintype σ] (p : MvPolynomial σ R) {d e : R}
    {t x x' : σ → R} (hx : ∀ i, d ∣ x i - t i) (hde : d ∣ e) (hxx' : ∀ i, e ∣ x' i - x i) :
    d * e ∣ eval x' p - eval x p - ∑ j, eval t (pderiv j p) * (x' j - x j) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    convert dvd_add hp hq using 1
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X p i hp =>
    classical
    set S := ∑ j, eval t (pderiv j p) * (x' j - x j)
    have hS : e ∣ S := Finset.dvd_sum fun j _ ↦ dvd_mul_of_dvd_right (hxx' j) _
    have hx'i : d ∣ x' i - t i := by
      simpa using dvd_add (hde.trans (hxx' i)) (hx i)
    -- By the Leibniz rule, the gradient term of `p * Xᵢ` is `tᵢ S + p(t) (x'ᵢ - xᵢ)`.
    have hsum : ∑ j, eval t (pderiv j (p * X i)) * (x' j - x j) =
        t i * S + eval t p * (x' i - x i) := by
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X, add_mul,
        Finset.sum_add_distrib, S, Finset.mul_sum, Pi.single_apply]
      simp only [apply_ite (eval t), map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_assoc]
      ring
    rw [hsum, show eval x' (p * X i) - eval x (p * X i) - (t i * S + eval t p * (x' i - x i)) =
        (eval x' p - eval x p - S) * x' i + S * (x' i - t i) +
          (eval x p - eval t p) * (x' i - x i) by simp only [map_mul, eval_X]; ring]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left hp _) (mul_comm d e ▸ mul_dvd_mul hS hx'i))
      (mul_dvd_mul (dvd_eval_sub_eval p hx) (hxx' i))

end CommRing

end MvPolynomial
