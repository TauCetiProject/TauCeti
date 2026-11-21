/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

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
origin chosen via `MvPolynomial.exists_forall_trailingDegree_aeval_C_add_C_mul_X_eq` applied
simultaneously at the origin to the coefficient polynomials `P k` and the pairwise differences of
the linear forms `z ↦ ∑ v, w k v * z v`, so every nonzero `P k` stays nonzero as a univariate
polynomial and the restricted complex frequencies remain pairwise distinct. Fibering a finite
linear combination of exponential monomials by frequency and expanding in the monomial basis via
`Finsupp.equivFunOnFinite` also yields `ℂ`-linear independence of the family of exponential
monomials `(∏ v, z v ^ p.1 v) * exp (∑ v, p.2 v * z v)`
(`TauCeti.linearIndependent_prod_pow_mul_cexp`,
`TauCeti.eq_zero_of_sum_mul_prod_pow_mul_cexp_eq_zero`). In transcendence arguments such as the
Schneider–Lang criterion, this guarantees that an auxiliary exponential polynomial with nontrivial
coefficients and pairwise distinct frequencies is not identically zero.

## Main results

* `TauCeti.eq_zero_of_sum_eval_mul_cexp_of_injOn`: multivariate exponential polynomials with
  frequencies injective on `s` have trivial `MvPolynomial ι ℂ`-relations.
* `TauCeti.eq_zero_of_sum_eval_mul_cexp`: specialization to sums indexed directly by a finite set
  `T : Finset (ι → ℂ)` of frequencies.
* `TauCeti.sum_eval_mul_cexp_sum_eq_zero_iff_of_injOn`,
  `TauCeti.sum_eval_mul_cexp_sum_eq_zero_iff`,
  `TauCeti.sum_eval_mul_cexp_sum_eq_iff_of_injOn`, and
  `TauCeti.sum_eval_mul_cexp_sum_eq_iff`: characterization of vanishing and uniqueness of
  polynomial coefficients.
* `TauCeti.linearIndependent_prod_pow_mul_cexp` and
  `TauCeti.eq_zero_of_sum_mul_prod_pow_mul_cexp_eq_zero`: linear independence over `ℂ` of
  multivariate exponential monomials `(∏ v, z v ^ τ k v) * exp (∑ v, w k v * z v)` with pairwise
  distinct `(exponent, frequency)` pairs.

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
  classical
  let q : κ ⊕ (κ × κ) → MvPolynomial ι ℂ :=
    Sum.elim P fun m ↦ ∑ v, MvPolynomial.C (w m.1 v - w m.2 v) * MvPolynomial.X v
  obtain ⟨u, hu_deg⟩ := MvPolynomial.exists_forall_trailingDegree_aeval_C_add_C_mul_X_eq
    (s.disjSum (s ×ˢ s)) q 0
  have hu (i : κ ⊕ (κ × κ)) (hi : i ∈ s.disjSum (s ×ˢ s)) (hqi : q i ≠ 0) :
      MvPolynomial.aeval (fun v ↦ Polynomial.C (u v) * Polynomial.X) (q i) ≠ 0 := by
    have hdeg := hu_deg i hi
    simp only [Pi.zero_apply, map_zero, zero_add] at hdeg
    exact Polynomial.trailingDegree_eq_top.not.1
      (hdeg ▸ MvPolynomial.orderAt_eq_top_iff.not.2 hqi)
  have hu_inj : Set.InjOn (fun k ↦ ∑ v, w k v * u v) s := by
    intro k₁ hk₁ k₂ hk₂ hsum
    by_contra hne_k
    obtain ⟨v₀, hv₀⟩ := Function.ne_iff.1 (hw.ne hk₁ hk₂ hne_k)
    have hq_ne : q (Sum.inr (k₁, k₂)) ≠ 0 := fun hzero ↦
      sub_ne_zero.2 hv₀ <| by
        simpa [q, Pi.single_apply] using
          congrArg (MvPolynomial.eval (Pi.single v₀ (1 : ℂ))) hzero
    refine hu (Sum.inr (k₁, k₂))
      (Finset.mem_disjSum.2 (Or.inr ⟨(k₁, k₂), Finset.mem_product.2 ⟨hk₁, hk₂⟩, rfl⟩)) hq_ne ?_
    have hzero : ∑ v, (w k₁ v - w k₂ v) * u v = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, hsum, sub_self]
    simp only [q, Sum.elim_inr, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    simp only [← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum, hzero, map_zero, zero_mul]
  set r : κ → Polynomial ℂ := fun k ↦
    MvPolynomial.aeval (fun v ↦ Polynomial.C (u v) * Polynomial.X) (P k)
  have hline : ∀ t : ℂ, ∑ k ∈ s, (r k).eval t * Complex.exp ((∑ v, w k v * u v) * t) = 0 := by
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
  have hr : ∀ k ∈ s, r k = 0 :=
    eq_zero_of_sum_eval_mul_cexp_eq_zero_of_injOn hu_inj hline
  intro k hk
  by_contra hPk
  exact hu (Sum.inl k) (Finset.mem_disjSum.2 (Or.inl ⟨k, hk, rfl⟩)) hPk (hr k hk)

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
expansion with pairwise distinct frequencies on `s`. -/
theorem sum_eval_mul_cexp_sum_eq_iff_of_injOn {ι κ : Type*} [Fintype ι] {s : Finset κ}
    {w : κ → ι → ℂ} (hw : Set.InjOn w s) {P Q : κ → MvPolynomial ι ℂ} :
    (∀ z : ι → ℂ, ∑ k ∈ s, MvPolynomial.eval z (P k) * Complex.exp (∑ v, w k v * z v) =
      ∑ k ∈ s, MvPolynomial.eval z (Q k) * Complex.exp (∑ v, w k v * z v)) ↔
        ∀ k ∈ s, P k = Q k := by
  constructor
  · intro h
    have hz : ∀ z : ι → ℂ,
        ∑ k ∈ s, MvPolynomial.eval z (P k - Q k) * Complex.exp (∑ v, w k v * z v) = 0 :=
      fun z ↦ by
        simp only [map_sub, sub_mul, sum_sub_distrib, h z, sub_self]
    exact fun k hk ↦ sub_eq_zero.1 (eq_zero_of_sum_eval_mul_cexp_of_injOn hw hz k hk)
  · exact fun h z ↦ sum_congr rfl fun k hk ↦ by rw [h k hk]

/-- Uniqueness of polynomial coefficients in a multivariate complex exponential polynomial
expansion. -/
theorem sum_eval_mul_cexp_sum_eq_iff {ι : Type*} [Fintype ι] {T : Finset (ι → ℂ)}
    {P Q : (ι → ℂ) → MvPolynomial ι ℂ} :
    (∀ z : ι → ℂ, ∑ w ∈ T, MvPolynomial.eval z (P w) * Complex.exp (∑ v, w v * z v) =
      ∑ w ∈ T, MvPolynomial.eval z (Q w) * Complex.exp (∑ v, w v * z v)) ↔
        ∀ w ∈ T, P w = Q w :=
  sum_eval_mul_cexp_sum_eq_iff_of_injOn (fun _ _ _ _ ↦ id)

/-- **Linear independence of multivariate complex exponential monomials.** As functions
`(ι → ℂ) → ℂ`, the exponential monomials
`z ↦ (∏ v, z v ^ p.1 v) * exp (∑ v, p.2 v * z v)` indexed by `(ι → ℕ) × (ι → ℂ)` are linearly
independent over `ℂ`. -/
theorem linearIndependent_prod_pow_mul_cexp {ι : Type*} [Fintype ι] :
    LinearIndependent ℂ
      (fun p : (ι → ℕ) × (ι → ℂ) ↦ fun z : ι → ℂ ↦
        (∏ v, z v ^ p.1 v) * Complex.exp (∑ v, p.2 v * z v)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc
  let P : (ι → ℂ) → MvPolynomial ι ℂ := fun w ↦
    ∑ p ∈ s.filter (fun p ↦ p.2 = w),
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm p.1) (c p)
  have hP : ∀ z : ι → ℂ,
      ∑ w ∈ s.image Prod.snd, MvPolynomial.eval z (P w) * Complex.exp (∑ v, w v * z v) = 0 := by
    intro z
    have heval (w : ι → ℂ) :
        MvPolynomial.eval z (P w) =
          ∑ p ∈ s.filter (fun p ↦ p.2 = w), c p * ∏ v, z v ^ p.1 v := by
      simp only [P, map_sum, MvPolynomial.eval_monomial]
      refine sum_congr rfl fun p _ ↦ congrArg (c p * ·) ?_
      rw [Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, Finsupp.coe_equivFunOnFinite_symm]
    have hsum :
        ∑ w ∈ s.image Prod.snd,
            (∑ p ∈ s.filter (fun p ↦ p.2 = w), c p * ∏ v, z v ^ p.1 v) *
              Complex.exp (∑ v, w v * z v) =
          ∑ p ∈ s, c p * ((∏ v, z v ^ p.1 v) * Complex.exp (∑ v, p.2 v * z v)) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.snd) (fun _ hp ↦ mem_image_of_mem _ hp)]
      refine sum_congr rfl fun w _ ↦ ?_
      rw [sum_mul]
      refine sum_congr rfl fun p hp ↦ ?_
      rw [(mem_filter.1 hp).2, mul_assoc]
    simpa only [heval, hsum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrFun hc z
  have hP0 := eq_zero_of_sum_eval_mul_cexp hP
  intro p hp
  have hcoeff := congrArg
    (fun q : MvPolynomial ι ℂ ↦ q.coeff (Finsupp.equivFunOnFinite.symm p.1))
    (hP0 p.2 (mem_image_of_mem _ hp))
  rw [MvPolynomial.coeff_sum, sum_eq_single p] at hcoeff
  · simpa using hcoeff
  · intro p' hp' hne
    have hne1 : p'.1 ≠ p.1 := fun h1 ↦ hne (Prod.ext h1 (mem_filter.1 hp').2)
    have hne' :
        Finsupp.equivFunOnFinite.symm p'.1 ≠ Finsupp.equivFunOnFinite.symm p.1 :=
      Finsupp.equivFunOnFinite.symm.injective.ne hne1
    simp [MvPolynomial.coeff_monomial, hne']
  · exact fun h ↦ (h (mem_filter.2 ⟨hp, rfl⟩)).elim

/-- **Linear independence of multivariate complex exponential monomials** for a finite family whose
`(exponent, frequency)` pairs `k ↦ (τ k, w k)` are pairwise distinct on `s`: if
`∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * exp (∑ v, w k v * z v)) = 0` for every `z : ι → ℂ`, then
`c k = 0` for all `k ∈ s`. -/
theorem eq_zero_of_sum_mul_prod_pow_mul_cexp_eq_zero {ι κ : Type*} [Fintype ι] {s : Finset κ}
    {τ : κ → ι → ℕ} {w : κ → ι → ℂ} (h : Set.InjOn (fun k ↦ (τ k, w k)) s) {c : κ → ℂ}
    (hc : ∀ z : ι → ℂ,
      ∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v)) = 0) :
    ∀ k ∈ s, c k = 0 := by
  have hli : LinearIndepOn ℂ
      (fun k : κ ↦ fun z : ι → ℂ ↦ (∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v)) s :=
    (linearIndependent_prod_pow_mul_cexp (ι := ι)).comp
      (Set.domRestrict (s : Set κ) fun k ↦ (τ k, w k)) (Set.injOn_iff_injective.1 h)
  refine (linearIndepOn_finset_iff.1 hli) c ?_
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  exact hc z

end TauCeti
