/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import TauCeti.FieldTheory.Finite.Irreducible

import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Squarefree polynomials with prescribed factorization patterns over finite fields

This file constructs two squarefree factorization patterns over finite fields that are used to
exhibit a large symmetric Galois group by reduction modulo primes:

* degrees `(1, n - 1)`, whose Frobenius cycle type is an `(n - 1)`-cycle with one fixed point,
  which makes a transitive group doubly transitive;
* exactly one factor of degree `2` and all other factor degrees odd, whose Frobenius cycle type
  has an odd power that is a transposition.

These patterns are inputs to the three-prime realization of the full symmetric group `Sₙ` as a
Galois group over `ℚ`.

## Main results

* `TauCeti.exists_monic_squarefree_map_natDegree_normalizedFactors_eq_pair_one_sub_one`: for
  `2 ≤ n`, a monic squarefree polynomial of degree `n` whose factor degrees are `{1, n - 1}`.
* `TauCeti.exists_monic_squarefree_count_two_map_natDegree_normalizedFactors_eq_one_and_odd`:
  for `2 ≤ n`, a monic squarefree polynomial of degree `n` with exactly one quadratic irreducible
  factor and all other irreducible factors of odd degree.

## References

* B. L. van der Waerden, *Algebra* I, §61, for the three-prime realization of `Sₙ` over `ℚ` that
  these patterns feed.
-/

public section

noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace TauCeti

variable (k : Type*) [Field k] [Finite k]

/-- For `2 ≤ n`, a finite field has a monic squarefree polynomial of degree `n` whose irreducible
factors have degrees `1` and `n - 1`. -/
theorem exists_monic_squarefree_map_natDegree_normalizedFactors_eq_pair_one_sub_one
    [DecidableEq k] (n : ℕ) (hn : 2 ≤ n) :
    ∃ g : k[X], g.Monic ∧ g.natDegree = n ∧ Squarefree g ∧
      (normalizedFactors g).map natDegree = {1, n - 1} := by
  obtain ⟨h, hmonic, hirr, hdeg, hX⟩ :=
    exists_monic_irreducible_natDegree_eq_ne_X k (n - 1) (by omega)
  let s : Multiset k[X] := {X, h}
  have smonic : ∀ p ∈ s, p.Monic := by simp [s, monic_X, hmonic]
  have sirr : ∀ p ∈ s, Irreducible p := by simp [s, irreducible_X, hirr]
  have hfac : normalizedFactors s.prod = s := by
    rw [normalizedFactors_prod_eq s sirr]
    exact (Multiset.map_congr rfl fun p hp ↦ (smonic p hp).normalize_eq_self).trans s.map_id'
  have gsq : Squarefree s.prod := by
    rw [squarefree_iff_nodup_normalizedFactors
        (Multiset.prod_ne_zero fun hp ↦ (sirr 0 hp).ne_zero rfl), hfac]
    simp [s, Ne.symm hX]
  have gfac : (normalizedFactors s.prod).map natDegree = s.map natDegree := by rw [hfac]
  refine ⟨s.prod, by simpa using monic_multiset_prod_of_monic s id smonic, ?_, gsq,
    by simpa [s, hdeg] using gfac⟩
  rw [natDegree_multiset_prod_of_monic s smonic]
  simp only [s, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, natDegree_X, hdeg]
  omega

/-- For `2 ≤ n`, a finite field has a monic squarefree polynomial of degree `n` with exactly one
irreducible factor of degree `2`, all of whose other irreducible factors have odd degree.

For `n = 2` the polynomial is irreducible quadratic; for odd `n` the factors have degrees `2` and
`n - 2`; for even `n ≥ 4` they have degrees `2`, `1` and `n - 3`. -/
theorem exists_monic_squarefree_count_two_map_natDegree_normalizedFactors_eq_one_and_odd
    [DecidableEq k] (n : ℕ) (hn : 2 ≤ n) :
    ∃ g : k[X], g.Monic ∧ g.natDegree = n ∧ Squarefree g ∧
      ((normalizedFactors g).map natDegree).count 2 = 1 ∧
      ∀ d ∈ (normalizedFactors g).map natDegree, d ≠ 2 → Odd d := by
  obtain ⟨q, qmonic, qirr, qdeg⟩ := exists_monic_irreducible_natDegree_eq k 2 two_pos
  obtain rfl | hn := hn.eq_or_lt
  · refine ⟨q, qmonic, qdeg, qirr.squarefree, ?_, ?_⟩ <;>
      simp [normalizedFactors_irreducible qirr, qmonic.normalize_eq_self, qdeg]
  have qX : q ≠ X := fun h ↦ by simp [h] at qdeg
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- even degree: factors of degrees `2`, `1` and `n - 3`
    obtain ⟨h, hmonic, hirr, hdeg, hX⟩ :=
      exists_monic_irreducible_natDegree_eq_ne_X k (m + m - 3) (by omega)
    have hq : h ≠ q := fun h' ↦ by rw [h'] at hdeg; omega
    let s : Multiset k[X] := {q, X, h}
    have smonic : ∀ p ∈ s, p.Monic := by simp [s, monic_X, qmonic, hmonic]
    have sirr : ∀ p ∈ s, Irreducible p := by simp [s, irreducible_X, qirr, hirr]
    have hfac : normalizedFactors s.prod = s := by
      rw [normalizedFactors_prod_eq s sirr]
      exact (Multiset.map_congr rfl fun p hp ↦ (smonic p hp).normalize_eq_self).trans s.map_id'
    have gsq : Squarefree s.prod := by
      rw [squarefree_iff_nodup_normalizedFactors
          (Multiset.prod_ne_zero fun hp ↦ (sirr 0 hp).ne_zero rfl), hfac]
      simp [s, qX, Ne.symm hq, Ne.symm hX]
    have gfac : (normalizedFactors s.prod).map natDegree = s.map natDegree := by rw [hfac]
    refine ⟨s.prod, by simpa using monic_multiset_prod_of_monic s id smonic, ?_, gsq, ?_, ?_⟩
    · rw [natDegree_multiset_prod_of_monic s smonic]
      simp only [s, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton, natDegree_X, qdeg, hdeg]
      omega
    · rw [gfac]
      simp [s, qdeg, hdeg]
      omega
    · rw [gfac]
      simp only [s, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.mem_cons, Multiset.mem_singleton, natDegree_X, qdeg, hdeg]
      rintro d (rfl | rfl | rfl) hd
      · exact absurd rfl hd
      · exact odd_one
      · exact ⟨m - 2, by omega⟩
  · -- odd degree: factors of degrees `2` and `n - 2`
    obtain ⟨h, hmonic, hirr, hdeg⟩ :=
      exists_monic_irreducible_natDegree_eq k (2 * m + 1 - 2) (by omega)
    have hq : h ≠ q := fun h' ↦ by rw [h'] at hdeg; omega
    let s : Multiset k[X] := {q, h}
    have smonic : ∀ p ∈ s, p.Monic := by simp [s, qmonic, hmonic]
    have sirr : ∀ p ∈ s, Irreducible p := by simp [s, qirr, hirr]
    have hfac : normalizedFactors s.prod = s := by
      rw [normalizedFactors_prod_eq s sirr]
      exact (Multiset.map_congr rfl fun p hp ↦ (smonic p hp).normalize_eq_self).trans s.map_id'
    have gsq : Squarefree s.prod := by
      rw [squarefree_iff_nodup_normalizedFactors
          (Multiset.prod_ne_zero fun hp ↦ (sirr 0 hp).ne_zero rfl), hfac]
      simp [s, Ne.symm hq]
    have gfac : (normalizedFactors s.prod).map natDegree = s.map natDegree := by rw [hfac]
    refine ⟨s.prod, by simpa using monic_multiset_prod_of_monic s id smonic, ?_, gsq, ?_, ?_⟩
    · rw [natDegree_multiset_prod_of_monic s smonic]
      simp only [s, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton, qdeg, hdeg]
      omega
    · rw [gfac]
      simp [s, qdeg, hdeg]
      omega
    · rw [gfac]
      simp only [s, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.mem_cons, Multiset.mem_singleton, qdeg, hdeg]
      rintro d (rfl | rfl) hd
      · exact absurd rfl hd
      · exact ⟨m - 1, by omega⟩

end TauCeti
