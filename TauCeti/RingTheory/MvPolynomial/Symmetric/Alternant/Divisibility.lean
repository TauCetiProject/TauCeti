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
import TauCeti.RingTheory.MvPolynomial.Prime

/-!
# Divisibility by the Vandermonde alternant

Over any integral domain `R`, the linear factors `X j - X i` (`i < j`) of the Vandermonde
alternant `TauCeti.alternant (Fin m) R (fun j => (j : ℕ))` are pairwise non-associated primes in
`MvPolynomial (Fin m) R`. Consequently:

* If a polynomial `p` whose variable permutations remain associated to `p` (in particular, any
  symmetric or antisymmetric polynomial) is divisible by one root difference `X i₀ - X j₀`
  (`i₀ ≠ j₀`), then it is divisible by the entire Vandermonde alternant
  (`TauCeti.alternant_fin_val_dvd_of_associated_rename`,
  `TauCeti.alternant_fin_val_dvd_of_isSymmetric`), with no unique factorization assumption on `R`.

## Main results

* `TauCeti.alternant_fin_val_dvd_of_associated_rename`,
  `TauCeti.alternant_fin_val_dvd_of_isSymmetric`: divisibility by the Vandermonde alternant from
  a single root-difference divisor.
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

end TauCeti
