/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.RingTheory.Derivation.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Chain rule for derivations on evaluated multivariate polynomials

For a `k`-derivation `D : Derivation k A A` and a finite variable type `σ` (`[Fintype σ]`), a
multivariate polynomial `F : MvPolynomial σ A` evaluated at a point `t : σ → A` satisfies the
multivariable chain rule

`D (F.eval t) = (∑ e ∈ F.support, D (F.coeff e) * ∏ j, t j ^ e j) +`
`  ∑ j, (pderiv j F).eval t * D (t j)`,

differentiating both the coefficients of `F` and the coordinate entries `t j`. When `A` is local,
`[Finite σ]`, and `t` lies in its maximal ideal `𝔪`, this computes the leading term modulo
`𝔪 ^ (n + 1)` of `D (F(t))` for a homogeneous form `F` of degree `n + 1` whenever `D` is dual
modulo `𝔪` to coordinate `i`.

## Main results

* `Derivation.apply_eval_monomial`: chain rule on an evaluated monomial over a finite variable type
  `[Fintype σ]`.
* `Derivation.apply_eval_mvPolynomial`: chain rule on an evaluated multivariate polynomial over a
  finite variable type `[Fintype σ]`.
* `Derivation.apply_eval_sub_pderiv_mul_mem_pow_succ`: leading-term congruence modulo
  `𝔪 ^ (n + 1)` for a derivation dual modulo `𝔪` to coordinate `i` acting on a degree-`(n + 1)`
  homogeneous form over a finite variable type `[Finite σ]`.
-/

public section

namespace Derivation

open IsLocalRing MvPolynomial

section ChainRule

variable {k A σ : Type*} [CommSemiring k] [CommSemiring A] [Algebra k A] [Fintype σ]

/-- Applying a `k`-derivation of `A` to a monomial evaluated at `t` differentiates the coefficient
and the variable powers via the Leibniz rule. -/
theorem apply_eval_monomial (D : Derivation k A A) (e : σ →₀ ℕ) (a : A) (t : σ → A) :
    D ((monomial e a).eval t) =
      D a * (∏ j, t j ^ e j) + ∑ j, (pderiv j (monomial e a)).eval t * D (t j) := by
  classical
  have hprod : e.prod (fun j n ↦ t j ^ n) = ∏ j, t j ^ e j :=
    Finsupp.prod_fintype e (fun j n ↦ t j ^ n) fun _ ↦ pow_zero _
  have hsum : a * ∑ j, (∏ i ∈ Finset.univ.erase j, t i ^ e i) * D (t j ^ e j) =
      ∑ j, (pderiv j (monomial e a)).eval t * D (t j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [D.leibniz_pow]
    simp only [pderiv_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      smul_eq_mul, nsmul_eq_mul]
    by_cases hj : e j = 0
    · simp only [hj, Nat.cast_zero, zero_mul, mul_zero]
    · have hsub : ∏ l, t l ^ (e - Finsupp.single j (1 : ℕ)) l =
          t j ^ (e j - 1) * ∏ l ∈ Finset.univ.erase j, t l ^ e l := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        congr 1
        · simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        · refine Finset.prod_congr rfl fun l hl ↦ ?_
          simp only [Finsupp.tsub_apply,
            Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hl), Nat.sub_zero]
      rw [hsub]
      ring
  rw [eval_monomial, hprod, D.leibniz, D.leibniz_prod]
  simp only [smul_eq_mul]
  rw [hsum]
  ring

/-- **Chain rule for a derivation on a polynomial evaluated at elements of `A`.** -/
theorem apply_eval_mvPolynomial (D : Derivation k A A) (F : MvPolynomial σ A) (t : σ → A) :
    D (F.eval t) =
      (∑ e ∈ F.support, D (F.coeff e) * ∏ j, t j ^ e j) +
        ∑ j, (pderiv j F).eval t * D (t j) := by
  classical
  conv_lhs => rw [F.as_sum]
  simp only [map_sum]
  simp_rw [apply_eval_monomial]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Finset.sum_mul]

end ChainRule

/-- A derivation `D` of a local `k`-algebra `A` that is dual modulo `𝔪` to coordinate `i` of
`t : σ → A` (up to `s : A`) acts on a degree-`(n + 1)` homogeneous form `F(t)` as
`(pderiv i F).eval t * s` modulo `𝔪 ^ (n + 1)`. -/
theorem apply_eval_sub_pderiv_mul_mem_pow_succ {k A σ : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [IsLocalRing A] [Finite σ] [DecidableEq σ]
    (D : Derivation k A A) {t : σ → A} (htmem : ∀ j, t j ∈ maximalIdeal A) {n : ℕ}
    {F : MvPolynomial σ A} (hF : F.IsHomogeneous (n + 1)) {i : σ} {s : A}
    (hDt : ∀ j : σ, residue A (D (t j)) = if j = i then residue A s else 0) :
    D (F.eval t) - (pderiv i F).eval t * s ∈ maximalIdeal A ^ (n + 1) := by
  have := Fintype.ofFinite σ
  have hcoeff_mem :
      (∑ e ∈ F.support, D (F.coeff e) * ∏ j, t j ^ e j) ∈ maximalIdeal A ^ (n + 1) :=
    Ideal.sum_mem _ fun e he ↦ Ideal.mul_mem_left _ _ (hF.prod_pow_mem_pow htmem he)
  have hderiv_mem (j : σ) : (pderiv j F).eval t ∈ maximalIdeal A ^ n :=
    hF.pderiv.eval_mem_pow htmem
  have htail_mem :
      (∑ j, (pderiv j F).eval t * D (t j)) - (pderiv i F).eval t * s ∈
        maximalIdeal A ^ (n + 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_right_comm, ← mul_sub]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun j hj ↦ ?_)
    · rw [pow_succ]
      refine Ideal.mul_mem_mul (hderiv_mem i) ((residue_eq_zero_iff _).mp ?_)
      simp [hDt i]
    · rw [pow_succ]
      refine Ideal.mul_mem_mul (hderiv_mem j) ((residue_eq_zero_iff _).mp ?_)
      simp [hDt j, Finset.ne_of_mem_erase hj]
  rw [D.apply_eval_mvPolynomial F t, add_sub_assoc]
  exact Ideal.add_mem _ hcoeff_mem htail_mem

end Derivation
