/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Complex.Exponential

import TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial
import TauCeti.RingTheory.MvPolynomial.DirectionalOrder

/-!
# Linear independence of multivariate complex exponential polynomials

For finitely many pairwise distinct complex frequency vectors `w : ι → ℂ`, the functions
`z ↦ exp (∑ v, w v * z v)` on `ι → ℂ` are linearly independent over `MvPolynomial ι ℂ`: if
`∑ w ∈ T, MvPolynomial.eval z (P w) * exp (∑ v, w v * z v) = 0` for every `z : ι → ℂ`, then every
coefficient polynomial `P w` on `T` is zero (`TauCeti.eq_zero_of_sum_eval_mul_cexp`), and
similarly for frequencies indexed by an injective map on a finite set
(`TauCeti.eq_zero_of_sum_eval_mul_cexp_of_injOn`).

The proof reduces to the one-variable theorem
`TauCeti.eq_zero_of_sum_eval_mul_cexp_eq_zero_of_injOn` along a single complex line through the
origin chosen via `MvPolynomial.exists_injOn_sum_mul_and_aeval_C_mul_X_ne_zero`, on which all
nonzero `P k` stay nonzero as univariate polynomials and the linear forms `z ↦ ∑ v, w k v * z v`
restrict to pairwise distinct complex frequencies. Expanding each `P k` in the monomial basis via
`Finsupp.equivFunOnFinite` also yields linear independence of exponential monomials
`(∏ v, z v ^ τ m v) * exp (∑ v, w k v * z v)` over `ℂ`
(`TauCeti.eq_zero_of_sum_mul_prod_pow_mul_cexp_eq_zero`). In transcendence arguments such as the
Schneider–Lang criterion, this guarantees that an auxiliary exponential polynomial with nontrivial
coefficients and pairwise distinct frequencies is not identically zero.

## Main results

* `TauCeti.eq_zero_of_sum_eval_mul_cexp_of_injOn`: multivariate exponential polynomials with
  frequencies injective on `s` have trivial `MvPolynomial ι ℂ`-relations.
* `TauCeti.eq_zero_of_sum_eval_mul_cexp`: specialization to sums indexed directly by a finite set
  `T : Finset (ι → ℂ)` of frequencies.
* `TauCeti.sum_eval_mul_cexp_sum_eq_zero_iff_of_injOn`,
  `TauCeti.sum_eval_mul_cexp_sum_eq_zero_iff`, and `TauCeti.sum_eval_mul_cexp_sum_eq_iff`:
  characterization of vanishing and uniqueness of polynomial coefficients.
* `TauCeti.eq_zero_of_sum_mul_prod_pow_mul_cexp_eq_zero`: linear independence over `ℂ` of
  exponential monomials `(∏ v, z v ^ τ m v) * exp (∑ v, w k v * z v)` with distinct multi-indices
  and distinct frequencies.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren 326,
  Springer (2000), Chapter 4, §4.6 (compare also Exercise 2.5, p. 60).
* M. Karatarakis, formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
  commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/ExpIndep.lean`, Apache 2.0).
-/

public section

open Finset

namespace TauCeti

/-- **Linear independence of multivariate complex exponential polynomials** for a family of
frequencies injective on a finite index set `s`. If
`∑ k ∈ s, MvPolynomial.eval z (P k) * exp (∑ v, w k v * z v) = 0` for every `z : ι → ℂ`, then
`P k = 0` for all `k ∈ s`. -/
theorem eq_zero_of_sum_eval_mul_cexp_of_injOn {ι κ : Type*} [Fintype ι] {s : Finset κ}
    {w : κ → ι → ℂ} (hw : Set.InjOn w s) {P : κ → MvPolynomial ι ℂ}
    (hP : ∀ z : ι → ℂ, ∑ k ∈ s, MvPolynomial.eval z (P k) * Complex.exp (∑ v, w k v * z v) = 0) :
    ∀ k ∈ s, P k = 0 := by
  obtain ⟨u, hu_inj, hu_ne⟩ :=
    MvPolynomial.exists_injOn_sum_mul_and_aeval_C_mul_X_ne_zero hw P
  set q : κ → Polynomial ℂ := fun k ↦
    MvPolynomial.aeval (fun v ↦ Polynomial.C (u v) * Polynomial.X) (P k)
  have hline : ∀ t : ℂ, ∑ k ∈ s, (q k).eval t * Complex.exp ((∑ v, w k v * u v) * t) = 0 := by
    intro t
    rw [← hP (t • u)]
    refine sum_congr rfl fun k _ ↦ ?_
    have hk := MvPolynomial.eval_aeval_C_add_C_mul_X (P k) 0 u t
    simp only [Pi.zero_apply, map_zero, zero_add] at hk
    rw [hk, sum_mul]
    congr 2
    refine sum_congr rfl fun v _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hq : ∀ k ∈ s, q k = 0 :=
    eq_zero_of_sum_eval_mul_cexp_eq_zero_of_injOn hu_inj hline
  intro k hk
  by_contra hPk
  exact hu_ne k hk hPk (hq k hk)

/-- **Linear independence of multivariate complex exponential polynomials** indexed by a finite set
`T` of frequency vectors: if `∑ w ∈ T, MvPolynomial.eval z (P w) * exp (∑ v, w v * z v) = 0` for
every `z : ι → ℂ`, then `P w = 0` for all `w ∈ T`. -/
theorem eq_zero_of_sum_eval_mul_cexp {ι : Type*} [Fintype ι] {T : Finset (ι → ℂ)}
    {P : (ι → ℂ) → MvPolynomial ι ℂ}
    (hP : ∀ z : ι → ℂ, ∑ w ∈ T, MvPolynomial.eval z (P w) * Complex.exp (∑ v, w v * z v) = 0) :
    ∀ w ∈ T, P w = 0 :=
  eq_zero_of_sum_eval_mul_cexp_of_injOn (fun _ _ _ _ ↦ id) hP

/-- A multivariate complex exponential polynomial with pairwise distinct frequencies on `s`
vanishes everywhere if and only if all of its coefficient polynomials on `s` vanish. -/
theorem sum_eval_mul_cexp_sum_eq_zero_iff_of_injOn {ι κ : Type*} [Fintype ι] {s : Finset κ}
    {w : κ → ι → ℂ} (hw : Set.InjOn w s) {P : κ → MvPolynomial ι ℂ} :
    (∀ z : ι → ℂ, ∑ k ∈ s, MvPolynomial.eval z (P k) * Complex.exp (∑ v, w k v * z v) = 0) ↔
      ∀ k ∈ s, P k = 0 :=
  ⟨eq_zero_of_sum_eval_mul_cexp_of_injOn hw, fun h z ↦
    sum_eq_zero fun k hk ↦ by simp [h k hk]⟩

/-- A multivariate complex exponential polynomial indexed by a finite set of frequency vectors
vanishes everywhere if and only if all of its coefficient polynomials vanish. -/
theorem sum_eval_mul_cexp_sum_eq_zero_iff {ι : Type*} [Fintype ι] {T : Finset (ι → ℂ)}
    {P : (ι → ℂ) → MvPolynomial ι ℂ} :
    (∀ z : ι → ℂ, ∑ w ∈ T, MvPolynomial.eval z (P w) * Complex.exp (∑ v, w v * z v) = 0) ↔
      ∀ w ∈ T, P w = 0 :=
  sum_eval_mul_cexp_sum_eq_zero_iff_of_injOn (fun _ _ _ _ ↦ id)

/-- Uniqueness of polynomial coefficients in a multivariate complex exponential polynomial
expansion. -/
theorem sum_eval_mul_cexp_sum_eq_iff {ι : Type*} [Fintype ι] {T : Finset (ι → ℂ)}
    {P Q : (ι → ℂ) → MvPolynomial ι ℂ} :
    (∀ z : ι → ℂ, ∑ w ∈ T, MvPolynomial.eval z (P w) * Complex.exp (∑ v, w v * z v) =
      ∑ w ∈ T, MvPolynomial.eval z (Q w) * Complex.exp (∑ v, w v * z v)) ↔
        ∀ w ∈ T, P w = Q w := by
  constructor
  · intro h
    have hz : ∀ z : ι → ℂ,
        ∑ w ∈ T, MvPolynomial.eval z (P w - Q w) * Complex.exp (∑ v, w v * z v) = 0 := fun z ↦ by
      simp only [map_sub, sub_mul, sum_sub_distrib, h z, sub_self]
    exact fun w hw ↦ sub_eq_zero.1 (eq_zero_of_sum_eval_mul_cexp hz w hw)
  · exact fun h z ↦ sum_congr rfl fun w hw ↦ by rw [h w hw]

/-- **Linear independence of multivariate complex exponential monomials.** If `τ` is injective on
`s` and `w` is injective on `t`, and
`∑ m ∈ s, ∑ k ∈ t, c m k * (∏ v, z v ^ τ m v) * exp (∑ v, w k v * z v) = 0` for every `z : ι → ℂ`,
then `c m k = 0` for all `m ∈ s` and `k ∈ t`. -/
theorem eq_zero_of_sum_mul_prod_pow_mul_cexp_eq_zero {ι μ κ : Type*} [Fintype ι]
    {s : Finset μ} {t : Finset κ} {τ : μ → ι → ℕ} (hτ : Set.InjOn τ s)
    {w : κ → ι → ℂ} (hw : Set.InjOn w t) {c : μ → κ → ℂ}
    (hc : ∀ z : ι → ℂ,
      ∑ m ∈ s, ∑ k ∈ t, c m k * (∏ v, z v ^ τ m v) * Complex.exp (∑ v, w k v * z v) = 0) :
    ∀ m ∈ s, ∀ k ∈ t, c m k = 0 := by
  classical
  let P : κ → MvPolynomial ι ℂ := fun k ↦
    ∑ m ∈ s, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (τ m)) (c m k)
  have hP : ∀ z : ι → ℂ,
      ∑ k ∈ t, MvPolynomial.eval z (P k) * Complex.exp (∑ v, w k v * z v) = 0 := by
    intro z
    have heval (k : κ) :
        MvPolynomial.eval z (P k) = ∑ m ∈ s, c m k * ∏ v, z v ^ τ m v := by
      simp only [P, map_sum, MvPolynomial.eval_monomial]
      refine sum_congr rfl fun m _ ↦ congrArg (c m k * ·) ?_
      rw [Finsupp.prod_of_support_subset _ (subset_univ _) _ fun _ _ ↦ pow_zero _]
      rfl
    simpa only [heval, sum_mul] using (sum_comm.trans (hc z))
  have hP0 := eq_zero_of_sum_eval_mul_cexp_of_injOn hw hP
  intro m hm k hk
  have hcoeff := congrArg
    (fun q : MvPolynomial ι ℂ ↦ q.coeff (Finsupp.equivFunOnFinite.symm (τ m))) (hP0 k hk)
  rw [_root_.MvPolynomial.coeff_sum, sum_eq_single m] at hcoeff
  · simpa using hcoeff
  · intro m' hm' hne
    have hne' :
        Finsupp.equivFunOnFinite.symm (τ m') ≠ Finsupp.equivFunOnFinite.symm (τ m) :=
      Finsupp.equivFunOnFinite.symm.injective.ne (hτ.ne hm' hm hne)
    simp [_root_.MvPolynomial.coeff_monomial, hne']
  · exact fun h ↦ absurd hm h

end TauCeti
