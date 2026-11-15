/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Operations

import TauCeti.Algebra.MvPolynomial.Eval

/-!
# Partial derivatives of multivariate polynomials: chain rule, degree and coefficients

Substituting polynomials `fᵢ ∈ R[Y_τ]` for the variables `Xᵢ` of `p ∈ R[X_σ]` and differentiating
with respect to `Y_j` obeys the chain rule

`∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j`,

where the sum runs over any finite set of indices containing the variables of `p`.

Partial differentiation lowers the total degree, and the degree in the differentiated variable,
by at least one, so the `k`-th iterated partial derivative along `Xᵢ` of a polynomial of degree
less than `k` in `Xᵢ` vanishes; it also keeps the coefficients in any additive submonoid of the
coefficient ring, such as a subring. These are the facts needed to clear the denominators of
derivatives of polynomials evaluated at algebraic points.

Over a commutative ring the gradient at a point `t` linearises a polynomial up to a divisibility
or ideal-product error: if `xᵢ - tᵢ ∈ I`, `x'ᵢ - tᵢ ∈ I` and `x'ᵢ - xᵢ ∈ J`, then
`p(x') - p(x) - ∑ⱼ ∂ⱼp(t) (x'ⱼ - xⱼ)` lies in `I * J` (and is divisible by `d * e` when `I = (d)`,
`J = (e)` with `d ∣ e`). Specialising `x = t` and `I = J` linearises `p(x') - p(t)` modulo `I ^ 2`
over any finite set `s` containing the variables of `p` at which `x'` and `t` differ. This is the
several-variable form of `Polynomial.mul_dvd_eval_sub_eval_sub_mul` and the estimate behind
Newton's method with an approximately invertible Jacobian.

## Main results

* `MvPolynomial.pderiv_aeval`: the chain rule, summed over all variables of a finite type.
* `MvPolynomial.pderiv_aeval_of_vars_subset`: the chain rule, summed over a finite set containing
  the variables of `p`.
* `MvPolynomial.totalDegree_iterate_pderiv_le`: the `k`-th iterated partial derivative has total
  degree at most `totalDegree p - k`.
* `MvPolynomial.degreeOf_iterate_pderiv_le`: the `k`-th iterated partial derivative along `Xᵢ` has
  degree at most `degreeOf i p - k` in `Xᵢ`.
* `MvPolynomial.iterate_pderiv_eq_zero_of_degreeOf_lt`: the `k`-th iterated partial derivative
  along `Xᵢ` vanishes when `degreeOf i p < k`.
* `MvPolynomial.coeff_iterate_pderiv_mem`: iterated partial derivatives keep the coefficients in
  an additive submonoid.
* `MvPolynomial.iterate_pderiv_prod_aeval_X`: on a separated product `∏ⱼ Qⱼ(Xⱼ)` of one-variable
  polynomials, the `k`-th iterated partial derivative along `Xᵢ` is `Qᵢ⁽ᵏ⁾(Xᵢ) ∏_{j ≠ i} Qⱼ(Xⱼ)`.
* `MvPolynomial.mul_dvd_eval_sub_eval_sub_sum_pderiv`: Taylor's divisibility estimate
  `d * e ∣ p(x') - p(x) - ∑ⱼ ∂ⱼp(t) (x'ⱼ - xⱼ)`.
* `MvPolynomial.eval_sub_eval_sub_sum_pderiv_mem_mul`,
  `MvPolynomial.eval_sub_eval_sub_sum_pderiv_mem_sq`: Taylor's ideal-product estimate
  `p(x') - p(x) - ∑ⱼ ∂ⱼp(t) (x'ⱼ - xⱼ) ∈ I * J`, and its first-order specialisation modulo `I ^ 2`
  over an arbitrary variable type.
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
    simp [Derivation.leibniz, hp, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Pi.single_apply,
      apply_ite, mul_assoc]

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

/-- Partial differentiation along `Xᵢ` lowers the degree in `Xᵢ` by at least one. -/
theorem degreeOf_pderiv_le (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).degreeOf i ≤ p.degreeOf i - 1 := by
  classical
  refine degreeOf_le_iff.2 fun m hm ↦ ?_
  rw [mem_support_iff, coeff_pderiv] at hm
  have h := monomial_le_degreeOf i (mem_support_iff.2 (left_ne_zero_of_mul hm))
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at h
  omega

/-- The `k`-th iterated partial derivative along `Xᵢ` lowers the degree in `Xᵢ` by at least
`k`. -/
theorem degreeOf_iterate_pderiv_le (i : σ) (k : ℕ) (p : MvPolynomial σ R) :
    ((pderiv i)^[k] p).degreeOf i ≤ p.degreeOf i - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := degreeOf_pderiv_le i ((pderiv i)^[k] p)
    omega

/-- The `k`-th iterated partial derivative along `Xᵢ` of a polynomial of degree less than `k` in
`Xᵢ` vanishes. -/
theorem iterate_pderiv_eq_zero_of_degreeOf_lt {i : σ} {k : ℕ} {p : MvPolynomial σ R}
    (h : p.degreeOf i < k) : (pderiv i)^[k] p = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [Function.iterate_succ_apply']
  refine pderiv_eq_zero_of_notMem_vars fun hi ↦ mem_vars_iff_degreeOf_ne_zero.1 hi ?_
  have := degreeOf_iterate_pderiv_le i (p.degreeOf i + k) p
  omega

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
  -- The factors other than the `i`-th do not involve `Xᵢ`, so their product is a constant for
  -- `∂/∂Xᵢ`.
  have hg : pderiv i (∏ j ∈ s.erase i, Polynomial.aeval (X j : MvPolynomial σ R) (Q j)) = 0 :=
    Finset.prod_induction _ (fun g ↦ pderiv i g = 0)
      (fun a b ha hb ↦ by simp [Derivation.leibniz, ha, hb]) pderiv_one
      fun j hj ↦ by simp [Derivation.map_aeval, pderiv_X_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase s _ hi]
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [Function.iterate_succ_apply', ih, Derivation.leibniz, Derivation.map_aeval, hg, mul_comm]

end CommSemiring

section CommRing

variable {R σ : Type*} [CommRing R]

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
    convert dvd_add (dvd_add (dvd_mul_of_dvd_left hp (x' i)) (mul_dvd_mul hx'i hS))
      (mul_dvd_mul (dvd_eval_sub_eval p hx) (hxx' i)) using 1
    rw [hsum]
    simp only [map_mul, eval_X]
    ring

/-- **Ideal-product Taylor estimate in several variables.** If `xᵢ - tᵢ ∈ I`, `x'ᵢ - tᵢ ∈ I` and
`x'ᵢ - xᵢ ∈ J` for every `i`, then the gradient at `t` linearises `p` from `x` to `x'` up to an
error in `I * J`. -/
theorem eval_sub_eval_sub_sum_pderiv_mem_mul [Fintype σ] (p : MvPolynomial σ R) {I J : Ideal R}
    {t x x' : σ → R} (hx : ∀ i, x i - t i ∈ I) (hx' : ∀ i, x' i - t i ∈ I)
    (hxx' : ∀ i, x' i - x i ∈ J) :
    eval x' p - eval x p - ∑ j, eval t (pderiv j p) * (x' j - x j) ∈ I * J := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have hlin : eval x' (p + q) - eval x (p + q) -
          ∑ j, eval t (pderiv j (p + q)) * (x' j - x j) =
        (eval x' p - eval x p - ∑ j, eval t (pderiv j p) * (x' j - x j)) +
          (eval x' q - eval x q - ∑ j, eval t (pderiv j q) * (x' j - x j)) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [hlin]
    exact (I * J).add_mem hp hq
  | mul_X p i hp =>
    classical
    set S := ∑ j, eval t (pderiv j p) * (x' j - x j)
    have hS : S ∈ J := J.sum_mem fun j _ ↦ J.mul_mem_left _ (hxx' j)
    have hsum : ∑ j, eval t (pderiv j (p * X i)) * (x' j - x j) =
        t i * S + eval t p * (x' i - x i) := by
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X, add_mul,
        Finset.sum_add_distrib, S, Finset.mul_sum, Pi.single_apply]
      simp only [apply_ite (eval t), map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_assoc]
      ring
    have hlin : eval x' (p * X i) - eval x (p * X i) -
          ∑ j, eval t (pderiv j (p * X i)) * (x' j - x j) =
        (eval x' p - eval x p - S) * x' i + (x' i - t i) * S +
          (eval x p - eval t p) * (x' i - x i) := by
      rw [hsum]
      simp only [map_mul, eval_X]
      ring
    rw [hlin]
    exact (I * J).add_mem
      ((I * J).add_mem ((I * J).mul_mem_right _ hp) (Ideal.mul_mem_mul (hx' i) hS))
      (Ideal.mul_mem_mul (eval_sub_eval_mem p hx) (hxx' i))

/-- **First-order Taylor estimate modulo `I ^ 2` over an arbitrary variable type.** Let `s` be a
finite set of indices containing every variable of `p` at which `b` and `a` differ. If `bᵢ - aᵢ ∈ I`
for every `i ∈ s`, then `p(b) - p(a) - ∑_{j ∈ s} ∂ⱼp(a) (bⱼ - aⱼ) ∈ I ^ 2`. -/
theorem eval_sub_eval_sub_sum_pderiv_mem_sq (p : MvPolynomial σ R) {I : Ideal R}
    {a b : σ → R} {s : Finset σ} (hs : ∀ i ∈ p.vars, b i ≠ a i → i ∈ s)
    (hb : ∀ i ∈ s, b i - a i ∈ I) :
    eval b p - eval a p - ∑ j ∈ s, eval a (pderiv j p) * (b j - a j) ∈ I ^ 2 := by
  classical
  let u : Finset σ := s ∪ p.vars
  have hpv : p.vars ⊆ u := Finset.subset_union_right
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range p ((↑) : u → σ) Subtype.val_injective
    (by simpa using hpv)
  have hcoord (k : u) : (b ∘ Subtype.val) k - (a ∘ Subtype.val) k ∈ I := by
    by_cases hks : (k : σ) ∈ s
    · exact hb k hks
    · have hk : b k = a k := by
        by_contra hne
        rcases Finset.mem_union.mp k.2 with hks' | hkv
        · exact hks hks'
        · exact hks (hs k hkv hne)
      simp [hk]
  have hmem := eval_sub_eval_sub_sum_pderiv_mem_mul q (I := I) (J := I)
    (t := a ∘ Subtype.val) (x := a ∘ Subtype.val) (x' := b ∘ Subtype.val)
    (fun _ ↦ by simp) hcoord hcoord
  rw [← sq] at hmem
  have hsum : (∑ k : u, eval (a ∘ Subtype.val) (pderiv k q) * (b k - a k)) =
      ∑ j ∈ s, eval a (pderiv j p) * (b j - a j) := by
    have h1 : (∑ k : u, eval (a ∘ Subtype.val) (pderiv k q) * (b k - a k)) =
        ∑ j ∈ u, eval a (pderiv j p) * (b j - a j) := by
      rw [← Finset.sum_coe_sort u]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← hq, pderiv_rename Subtype.val_injective, eval_rename]
    rw [h1]
    refine (Finset.sum_subset Finset.subset_union_left fun j _ hjs ↦ ?_).symm
    by_cases hjv : j ∈ p.vars
    · have hjb : b j = a j := by
        by_contra hne
        exact hjs (hs j hjv hne)
      simp [hjb]
    · simp [pderiv_eq_zero_of_notMem_vars hjv]
  have heval_b : eval (b ∘ Subtype.val) q = eval b p := by
    rw [← hq, eval_rename]
  have heval_a : eval (a ∘ Subtype.val) q = eval a p := by
    rw [← hq, eval_rename]
  simpa only [Function.comp_apply, heval_b, heval_a, hsum] using hmem

end CommRing

end MvPolynomial
