/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Polynomial.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Divisors of split polynomials after extending scalars

A divisor of a product of monic linear factors over a domain is a unit constant times
an indexed subproduct. Consequently a divisor of a split polynomial from a ground field
is a unit constant times the image of a divisor over that field.
-/

public section

open Polynomial

variable {k : Type*} [Field k]

/-- Over a domain `A`, a divisor of a product of linear polynomials `X - C (v i)` is a unit
constant times a sub-product. -/
theorem TauCeti.exists_eq_C_mul_prod_X_sub_C_of_dvd
    {A ι : Type*} [CommRing A] [IsDomain A] (v : ι → A)
    (s : Multiset ι) (p : A[X]) (hp : p ∣ (s.map fun i ↦ X - C (v i)).prod) :
    ∃ u : Aˣ, ∃ t ≤ s, p = C (u : A) * (t.map fun i ↦ X - C (v i)).prod := by
  induction s using Multiset.induction_on generalizing p with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero] at hp
    obtain ⟨u, ha, rfl⟩ := Polynomial.isUnit_iff.mp (isUnit_of_dvd_one hp)
    exact ⟨ha.unit, 0, le_rfl, by simp⟩
  | cons i s ih =>
    obtain ⟨q, hq⟩ := hp
    rw [Multiset.map_cons, Multiset.prod_cons] at hq
    have hdvd : X - C (v i) ∣ p * q := Dvd.intro _ hq
    rcases (prime_X_sub_C (v i)).dvd_or_dvd hdvd with ⟨p', rfl⟩ | ⟨q', rfl⟩
    · obtain ⟨u, t, ht, rfl⟩ := ih p' ⟨q, mul_left_cancel₀ (X_sub_C_ne_zero (v i))
        (by linear_combination hq)⟩
      refine ⟨u, i ::ₘ t, Multiset.cons_le_cons i ht, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons]
      ring
    · obtain ⟨u, t, ht, rfl⟩ := ih p ⟨q', mul_left_cancel₀ (X_sub_C_ne_zero (v i))
        (by linear_combination hq)⟩
      exact ⟨u, t, ht.trans (Multiset.le_cons_self s i), rfl⟩

/-- Let `f` split over a field `k` and let `A` be a domain over `k`. A divisor in `A[X]`
of the image of a nonzero `f ∈ k[X]` is `C a * g` for a unit `a` of `A` and a divisor `g` of `f`
in `k[X]`. -/
theorem Polynomial.Splits.exists_eq_C_mul_map_of_dvd_map {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] {f : k[X]} (hf : f ≠ 0) (hsplit : f.Splits) {p : A[X]}
    (hp : p ∣ f.map (algebraMap k A)) :
    ∃ u : Aˣ, ∃ factor : k[X], factor ∣ f ∧ p = C (u : A) * factor.map (algebraMap k A) := by
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (hsplit.natDegree_eq_card_roots.symm)
  rw [← hfac, Polynomial.map_mul, map_C, Polynomial.map_multiset_prod, Multiset.map_map] at hp
  have hu : IsUnit (C (algebraMap k A f.leadingCoeff)) :=
    (((leadingCoeff_ne_zero.mpr hf).isUnit).map (algebraMap k A)).map C
  rw [hu.dvd_mul_left] at hp
  obtain ⟨u, t, ht, rfl⟩ := TauCeti.exists_eq_C_mul_prod_X_sub_C_of_dvd (algebraMap k A) f.roots p
    (by simpa [Function.comp_def] using hp)
  refine ⟨u, (t.map fun a ↦ X - C a).prod, ?_, ?_⟩
  · rw [← hfac]
    exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map ht)).mul_left _
  · simp [Polynomial.map_multiset_prod, Multiset.map_map]
