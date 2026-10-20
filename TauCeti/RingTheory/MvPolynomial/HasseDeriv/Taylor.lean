/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
public import TauCeti.RingTheory.MvPolynomial.OrderAt

/-!
# Hasse derivatives as Taylor coefficients

The Taylor coefficients of a multivariate polynomial are its Hasse derivatives: for the Taylor
shift `MvPolynomial.taylor a`, `[Y^d] P(a + Y) = (∂^d P)(a)`, so that
`P(a + y) = ∑_d (∂^d P)(a) y^d`. Comparing Taylor coefficients of a product gives the Leibniz
rule for Hasse derivatives.

## Main results

* `MvPolynomial.coeff_taylor_X_map_C`, `MvPolynomial.coeff_taylor`: the Taylor coefficients of
  `P` at the generic point and at a point `a` are the Hasse derivatives `∂^d P` and their values
  `(∂^d P)(a)`.
* `MvPolynomial.eval_add_eq_finsum_hasseDeriv`: the finite Taylor expansion
  `P(a + y) = ∑_d (∂^d P)(a) y^d`.
* `MvPolynomial.hasseDeriv_mul`: the Leibniz rule `∂^d (P Q) = ∑_{a + b = d} ∂^a P · ∂^b Q`.
* `MvPolynomial.hasseDeriv_add_single_mul_toMvPolynomial`: the Leibniz rule for a product
  `f · p(Xᵢ)` in separated variables, `∂^(d + l eᵢ) (f · p(Xᵢ)) = ∂^d f · (Dˡ p)(Xᵢ)` when
  neither `f` nor `d` involves `Xᵢ`.
* `TauCeti.eval_hasseDeriv_rename`: renaming along an injective map commutes with
  evaluating Hasse derivatives.
* `TauCeti.eval_hasseDeriv_eval_hasseDeriv_finSuccEquiv`: evaluating a Hasse derivative after
  specializing `X₀` agrees with evaluating the combined derivative at the full point.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (2022), §2.6, Lemma 2.6.1.
* Mathlib's univariate `Polynomial.taylor_coeff` (`Mathlib/Algebra/Polynomial/Taylor.lean`), the
  one-variable form of `MvPolynomial.coeff_taylor`.
-/

public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- The Taylor coefficients of `P` at the generic point are its Hasse derivatives:
`P(X + Y) = ∑_d (∂^d P)(X) Y^d`. -/
theorem coeff_taylor_X_map_C (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (taylor (X : σ → MvPolynomial σ R) (map C P)).coeff d = hasseDeriv d P := by
  classical
  induction P using MvPolynomial.induction_on generalizing d with
  | C a =>
    rw [map_C, taylor_C, coeff_C]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [ite_eq_right (Ne.symm hd), hasseDeriv_C hd]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [hasseDeriv_mul_X, mul_comm (hasseDeriv d p)]
    simp [mul_add, mul_comm _ (C _), coeff_C_mul, coeff_mul_X', hp]

/-- The Taylor coefficients of `P` at the point `a` are the values of its Hasse derivatives:
`[Y^d] P(a + Y) = (∂^d P)(a)`. -/
theorem coeff_taylor (a : σ → R) (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (taylor a P).coeff d = eval a (hasseDeriv d P) := by
  rw [← eval_coeff_taylor_map_C, coeff_taylor_X_map_C]

/-- The Leibniz rule for Hasse derivatives: `∂^d (P Q) = ∑_{a + b = d} ∂^a P · ∂^b Q`. -/
theorem hasseDeriv_mul [DecidableEq σ] (d : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasseDeriv d (P * Q) =
      ∑ x ∈ Finset.antidiagonal d, hasseDeriv x.1 P * hasseDeriv x.2 Q := by
  simp only [← coeff_taylor_X_map_C, map_mul, coeff_mul]

/-- The Leibniz rule for a product in separated variables: if `f` does not involve `Xᵢ` and `d`
does not differentiate in `Xᵢ`, then `∂^(d + l eᵢ) (f · p(Xᵢ)) = ∂^d f · (Dˡ p)(Xᵢ)`, where `Dˡ` is
the one-variable Hasse derivative. -/
theorem hasseDeriv_add_single_mul_toMvPolynomial {d : σ →₀ ℕ} {i : σ} (hd : d i = 0)
    {f : MvPolynomial σ R} (hf : i ∉ f.vars) (l : ℕ) (p : Polynomial R) :
    hasseDeriv (d + Finsupp.single i l) (f * p.toMvPolynomial i) =
      hasseDeriv d f * (Polynomial.hasseDeriv l p).toMvPolynomial i := by
  classical
  rw [hasseDeriv_mul, Finset.sum_eq_single_of_mem (d, Finsupp.single i l)
    (Finset.mem_antidiagonal.2 rfl), hasseDeriv_single_toMvPolynomial]
  rintro ⟨a, b⟩ hab hne
  rw [Finset.mem_antidiagonal] at hab
  -- A term with `aᵢ ≠ 0` differentiates `f` in `Xᵢ`, and a term with `bⱼ ≠ 0` for some `j ≠ i`
  -- differentiates `p(Xᵢ)` in `Xⱼ`; the remaining term is `(d, l eᵢ)`.
  by_cases ha : a i = 0
  · by_cases hb : ∃ j, j ≠ i ∧ b j ≠ 0
    · obtain ⟨j, hji, hbj⟩ := hb
      rw [hasseDeriv_toMvPolynomial_eq_zero (Ne.symm hji) hbj, mul_zero]
    · push Not at hb
      refine absurd (Prod.ext (Finsupp.ext fun j ↦ ?_) (Finsupp.ext fun j ↦ ?_)) hne <;>
      · have h := DFunLike.congr_fun hab j
        simp only [Finsupp.add_apply, Finsupp.single_apply] at h ⊢
        rcases eq_or_ne j i with rfl | hj
        · simp only [ite_true] at h ⊢
          omega
        · simp only [Ne.symm hj, ite_false] at h ⊢
          have := hb j hj
          omega
  · rw [mem_vars_iff_degreeOf_ne_zero, not_not] at hf
    rw [hasseDeriv_eq_zero_of_degreeOf_lt (d := a) (P := f) (i := i) (by omega), zero_mul]

/-- The finite Taylor expansion with Hasse derivatives: `P(a + y) = ∑_d (∂^d P)(a) y^d`. -/
theorem eval_add_eq_finsum_hasseDeriv (P : MvPolynomial σ R) (a y : σ → R) :
    eval (a + y) P = ∑ᶠ d : σ →₀ ℕ, eval a (hasseDeriv d P) * d.prod fun j k ↦ y j ^ k := by
  rw [add_comm, ← eval_taylor, eval_eq,
    finsum_eq_sum_of_support_subset (s := (taylor a P).support) _ fun d hd ↦ ?_]
  · simp [coeff_taylor, Finsupp.prod]
  · rw [Function.mem_support] at hd
    rw [Finset.mem_coe, mem_support_iff, coeff_taylor]
    exact left_ne_zero_of_mul hd

end MvPolynomial

namespace TauCeti

open _root_.MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- Renaming the variables along an injective map commutes with evaluating Hasse derivatives. -/
theorem eval_hasseDeriv_rename {τ : Type*} {f : σ → τ} (hf : Function.Injective f) (b : τ → R)
    (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    eval b (hasseDeriv (d.mapDomain f) (rename f P)) = eval (b ∘ f) (hasseDeriv d P) := by
  rw [← coeff_taylor, taylor_rename, coeff_rename_mapDomain f hf, coeff_taylor]

/-- Evaluating the `i`-th Hasse derivative of the specialized `k`-th Hasse derivative in `X₀` at
`a` at a point `x` in the remaining variables gives the value of `∂^(i.cons k) P` at
`Fin.cons a x`. -/
theorem eval_hasseDeriv_eval_hasseDeriv_finSuccEquiv {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R) (a : R) (x : Fin n → R) (k : ℕ) (i : Fin n →₀ ℕ) :
    eval x (hasseDeriv i ((Polynomial.hasseDeriv k (finSuccEquiv R n P)).eval (C a))) =
      eval (Fin.cons a x) (hasseDeriv (i.cons k) P) := by
  rw [← coeff_taylor (Fin.cons a x), coeff_taylor_cons, Fin.cons_zero, Fin.tail_cons,
    Polynomial.taylor_coeff, coeff_taylor]

end TauCeti
