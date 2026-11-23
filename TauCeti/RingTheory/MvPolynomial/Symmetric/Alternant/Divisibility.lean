/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import TauCeti.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Divisibility by the Vandermonde alternant

Over any integral domain `R`, the linear factors `X j - X i` (`i < j`) of the Vandermonde
alternant `TauCeti.alternant (Fin m) R (fun j => (j : ℕ))` are pairwise non-associated primes in
`MvPolynomial (Fin m) R`. Consequently:

* If a polynomial `p` whose variable permutations remain associated to `p` (in particular, any
  symmetric or antisymmetric polynomial) is divisible by one root difference `X i₀ - X j₀`
  (`i₀ ≠ j₀`), then it is divisible by the entire Vandermonde alternant
  (`TauCeti.alternant_fin_val_dvd_of_associated_rename`,
  `TauCeti.alternant_fin_val_dvd_of_isSymmetric`).
* Every symmetric divisor of the squared Vandermonde alternant is either a unit or divisible by
  the Vandermonde alternant (`TauCeti.isUnit_or_alternant_fin_val_dvd_of_isSymmetric_of_dvd_sq`),
  with no unique factorization assumption on `R`.

## Main results

* `TauCeti.alternant_fin_val_dvd_of_associated_rename`,
  `TauCeti.alternant_fin_val_dvd_of_isSymmetric`: divisibility by the Vandermonde alternant from
  a single root-difference divisor.
* `TauCeti.isUnit_or_alternant_fin_val_dvd_of_isSymmetric_of_dvd_sq`: symmetric divisors of the
  squared Vandermonde alternant.
-/

public section

namespace TauCeti

open MvPolynomial Equiv Finset

private theorem prod_dvd_of_forall_prime {A ι : Type*} [CommRing A] [IsDomain A]
    {s : Finset ι} {q : ι → A} {p : A}
    (hq : ∀ x ∈ s, Prime (q x))
    (hnodup : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ Associated (q x) (q y))
    (hdvd : ∀ x ∈ s, q x ∣ p) :
    ∏ x ∈ s, q x ∣ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
    rw [Finset.prod_insert hxs]
    have hx_mem : x ∈ insert x s := mem_insert_self x s
    have hprime : Prime (q x) := hq x hx_mem
    obtain ⟨r, hr⟩ := ih (fun y hy => hq y (mem_insert_of_mem hy))
      (fun y hy z hz hyz => hnodup y (mem_insert_of_mem hy) z (mem_insert_of_mem hz) hyz)
      (fun y hy => hdvd y (mem_insert_of_mem hy))
    have hqxp : q x ∣ (∏ y ∈ s, q y) * r := hr ▸ hdvd x hx_mem
    rcases hprime.dvd_or_dvd hqxp with hprod | hqr
    · obtain ⟨y, hys, hxy⟩ := hprime.exists_mem_finset_dvd hprod
      have hy_mem : y ∈ insert x s := mem_insert_of_mem hys
      have hy_irr : Irreducible (q y) := (hq y hy_mem).irreducible
      have hass : Associated (q x) (q y) := hprime.irreducible.associated_of_dvd hy_irr hxy
      exact absurd hass (hnodup x hx_mem y hy_mem (fun h => hxs (h ▸ hys)))
    · obtain ⟨r', rfl⟩ := hqr
      exact ⟨r', by rw [hr]; ring⟩

private theorem exists_submultiset_associated_of_dvd_prod_prime {A : Type*} [CommRing A]
    [IsDomain A] {m : Multiset A} (hm : ∀ q ∈ m, Prime q) {p : A} (hdvd : p ∣ m.prod) :
    ∃ m' ≤ m, Associated p m'.prod := by
  induction m using Multiset.induction_on generalizing p with
  | empty =>
    rw [Multiset.prod_zero] at hdvd
    exact ⟨0, le_rfl, associated_one_iff_isUnit.mpr (isUnit_of_dvd_one hdvd)⟩
  | @cons q m ih =>
    rw [Multiset.prod_cons] at hdvd
    have hq : Prime q := hm q (Multiset.mem_cons_self q m)
    have hm' : ∀ r ∈ m, Prime r := fun r hr => hm r (Multiset.mem_cons_of_mem hr)
    obtain ⟨r, hr⟩ := hdvd
    rcases hq.dvd_or_dvd ⟨m.prod, hr.symm⟩ with hqp | hqr
    · obtain ⟨p', rfl⟩ := hqp
      have hp'd : p' ∣ m.prod := ⟨r, mul_left_cancel₀ hq.ne_zero (by rw [hr]; ring)⟩
      obtain ⟨m', hm'le, hass⟩ := ih hm' hp'd
      refine ⟨q ::ₘ m', Multiset.cons_le_cons q hm'le, ?_⟩
      rw [Multiset.prod_cons]
      exact hass.mul_left q
    · obtain ⟨r', rfl⟩ := hqr
      have hpd : p ∣ m.prod := ⟨r', mul_left_cancel₀ hq.ne_zero (by rw [hr]; ring)⟩
      obtain ⟨m', hm'le, hass⟩ := ih hm' hpd
      exact ⟨m', hm'le.trans (Multiset.le_cons_self m q), hass⟩

variable {R : Type*} [CommRing R]

/-- Over an integral domain `R`, if `p : MvPolynomial (Fin m) R` satisfies
`Associated (rename e p) p` for every permutation `e` (in particular, if `p` is symmetric or
antisymmetric) and is divisible by one root difference `X i₀ - X j₀` (`i₀ ≠ j₀`), then it is
divisible by the Vandermonde alternant `alternant (Fin m) R (fun j => (j : ℕ))`. -/
theorem alternant_fin_val_dvd_of_associated_rename [IsDomain R] {m : ℕ}
    {p : MvPolynomial (Fin m) R} (hp : ∀ e : Equiv.Perm (Fin m), Associated (rename e p) p)
    {i₀ j₀ : Fin m} (h₀ : i₀ ≠ j₀) (hdvd₀ : X i₀ - X j₀ ∣ p) :
    alternant (Fin m) R (fun j => (j : ℕ)) ∣ p := by
  rw [alternant_fin_val_eq_vandermonde]
  let S : Finset (Σ _ : Fin m, Fin m) := univ.sigma fun i : Fin m => Ioi i
  have hvand : ∏ i : Fin m, ∏ j ∈ Ioi i, (X j - X i : MvPolynomial (Fin m) R) =
      ∏ x ∈ S, (X x.2 - X x.1) := (Finset.prod_sigma (univ : Finset (Fin m))
    (fun i : Fin m => Ioi i) fun x : Σ _ : Fin m, Fin m =>
      (X x.2 - X x.1 : MvPolynomial (Fin m) R)).symm
  rw [hvand]
  refine prod_dvd_of_forall_prime (fun x hx => ?_) (fun x hx y hy hxy hass => ?_) (fun x hx => ?_)
  · have hx' : x.1 < x.2 := mem_Ioi.mp (mem_sigma.mp hx).2
    exact prime_X_sub_X hx'.ne'
  · have hx' : x.1 < x.2 := mem_Ioi.mp (mem_sigma.mp hx).2
    have hy' : y.1 < y.2 := mem_Ioi.mp (mem_sigma.mp hy).2
    obtain ⟨u, hu⟩ := hass
    have hass' : Associated (X x.1 - X x.2 : MvPolynomial (Fin m) R) (X y.1 - X y.2) :=
      ⟨u, by linear_combination -hu⟩
    obtain ⟨h1, h2⟩ := eq_of_associated_X_sub_X hx' hy' hass'
    exact hxy (Sigma.ext h1 (heq_of_eq h2))
  · have hx' : x.1 < x.2 := mem_Ioi.mp (mem_sigma.mp hx).2
    obtain ⟨e, he1, he2⟩ := MulAction.is_two_pretransitive_iff.mp
      (Equiv.Perm.isMultiplyPretransitive (Fin m) 2) h₀ hx'.ne'
    simp only [Equiv.Perm.smul_def] at he1 he2
    have hmap : X x.2 - X x.1 ∣ rename (R := R) e p := by
      have hd := _root_.map_dvd (rename (R := R) e) hdvd₀
      simpa [he1, he2] using hd
    exact hmap.trans (hp e).dvd

/-- Over an integral domain `R`, if a symmetric polynomial in `Fin m` is divisible by one root
difference `X i₀ - X j₀` (`i₀ ≠ j₀`), then it is divisible by the Vandermonde alternant
`alternant (Fin m) R (fun j => (j : ℕ))`. -/
theorem alternant_fin_val_dvd_of_isSymmetric [IsDomain R] {m : ℕ}
    {p : MvPolynomial (Fin m) R} (hp : p.IsSymmetric) {i₀ j₀ : Fin m}
    (h₀ : i₀ ≠ j₀) (hdvd₀ : X i₀ - X j₀ ∣ p) :
    alternant (Fin m) R (fun j => (j : ℕ)) ∣ p :=
  alternant_fin_val_dvd_of_associated_rename (fun e => by rw [hp e]) h₀ hdvd₀

/-- Over an integral domain `R`, any symmetric divisor of
`alternant (Fin m) R (fun j => (j : ℕ)) ^ 2` is either a unit or divisible by
`alternant (Fin m) R (fun j => (j : ℕ))`. -/
theorem isUnit_or_alternant_fin_val_dvd_of_isSymmetric_of_dvd_sq [IsDomain R] {m : ℕ}
    {p : MvPolynomial (Fin m) R} (hp : p.IsSymmetric)
    (hdvd : p ∣ alternant (Fin m) R (fun j => (j : ℕ)) ^ 2) :
    IsUnit p ∨ alternant (Fin m) R (fun j => (j : ℕ)) ∣ p := by
  let S : Finset (Σ _ : Fin m, Fin m) := univ.sigma fun i : Fin m => Ioi i
  let M : Multiset (MvPolynomial (Fin m) R) := S.val.map fun x => X x.2 - X x.1
  have hvand : alternant (Fin m) R (fun j => (j : ℕ)) = M.prod := by
    rw [alternant_fin_val_eq_vandermonde, ← Finset.prod_sigma (univ : Finset (Fin m))
      (fun i : Fin m => Ioi i) fun x : Σ _ : Fin m, Fin m =>
        (X x.2 - X x.1 : MvPolynomial (Fin m) R)]
    simp [M, S, Finset.prod_map_val]
  have hM : ∀ q ∈ M + M, Prime q := by
    intro q hq
    rcases Multiset.mem_add.mp hq with hqM | hqM <;>
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hqM
      have hx' : x.1 < x.2 := mem_Ioi.mp (mem_sigma.mp hx).2
      exact prime_X_sub_X hx'.ne'
  rw [hvand, sq, ← Multiset.prod_add] at hdvd
  obtain ⟨m', hm'le, hass⟩ := exists_submultiset_associated_of_dvd_prod_prime hM hdvd
  by_cases hm'0 : m' = 0
  · subst hm'0
    rw [Multiset.prod_zero] at hass
    exact Or.inl (isUnit_of_dvd_one hass.dvd)
  · right
    obtain ⟨q, hqm'⟩ := Multiset.exists_mem_of_ne_zero hm'0
    have hqM : q ∈ M + M := Multiset.subset_of_le hm'le hqm'
    have hq_pair : ∃ x ∈ S, q = X x.2 - X x.1 := by
      rcases Multiset.mem_add.mp hqM with hq' | hq' <;>
      · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hq'
        exact ⟨x, hx, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hq_pair
    have hx' : x.1 < x.2 := mem_Ioi.mp (mem_sigma.mp hx).2
    have hqp : X x.2 - X x.1 ∣ p := (Multiset.dvd_prod hqm').trans hass.symm.dvd
    exact alternant_fin_val_dvd_of_isSymmetric hp hx'.ne' hqp

end TauCeti
