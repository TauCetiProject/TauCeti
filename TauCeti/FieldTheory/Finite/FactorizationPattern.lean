/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.Irreducible
public import TauCeti.RingTheory.Polynomial.Factors

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
  for `3 ≤ n`, a monic squarefree polynomial of degree `n` with exactly one quadratic irreducible
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

/-- A product of distinct monic irreducible polynomials is monic and squarefree, its factor
degrees are the degrees of the given polynomials, and its degree is their sum. -/
private theorem exists_monic_squarefree_of_nodup (K : Type*) [Field K] [DecidableEq K]
    {s : Multiset K[X]}
    (hmonic : ∀ p ∈ s, p.Monic) (hirr : ∀ p ∈ s, Irreducible p) (hs : s.Nodup) :
    ∃ g : K[X], g.Monic ∧ g.natDegree = (s.map natDegree).sum ∧ Squarefree g ∧
      (normalizedFactors g).map natDegree = s.map natDegree := by
  have hfac : normalizedFactors s.prod = s := by
    rw [normalizedFactors_prod_eq s hirr]
    exact (Multiset.map_congr rfl fun p hp ↦ (hmonic p hp).normalize_eq_self).trans s.map_id'
  have hsq : Squarefree s.prod := by
    rw [squarefree_iff_nodup_normalizedFactors
        (Multiset.prod_ne_zero fun h ↦ (hirr 0 h).ne_zero rfl), hfac]
    exact hs
  refine ⟨s.prod, by simpa using monic_multiset_prod_of_monic s id hmonic, ?_, hsq, by rw [hfac]⟩
  rw [← sum_natDegree_normalizedFactors, hfac]

/-- For `2 ≤ n`, a finite field has a monic squarefree polynomial of degree `n` whose irreducible
factors have degrees `1` and `n - 1`. -/
theorem exists_monic_squarefree_map_natDegree_normalizedFactors_eq_pair_one_sub_one
    [DecidableEq k] (n : ℕ) (hn : 2 ≤ n) :
    ∃ g : k[X], g.Monic ∧ g.natDegree = n ∧ Squarefree g ∧
      (normalizedFactors g).map natDegree = {1, n - 1} := by
  obtain ⟨h, hmonic, hirr, hdeg, hX⟩ :=
    exists_monic_irreducible_natDegree_eq_ne_X k (n - 1) (by omega)
  obtain ⟨g, gmonic, gdeg, gsq, gfac⟩ := exists_monic_squarefree_of_nodup k (s := {X, h})
    (by simp [monic_X, hmonic]) (by simp [irreducible_X, hirr]) (by simp [Ne.symm hX])
  refine ⟨g, gmonic, ?_, gsq, by simp [gfac, hdeg]⟩
  simp only [gdeg, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, natDegree_X, hdeg]
  omega

/-- For `3 ≤ n`, a finite field has a monic squarefree polynomial of degree `n` with exactly one
irreducible factor of degree `2`, all of whose other irreducible factors have odd degree.

For odd `n` the factors have degrees `2` and `n - 2`; for even `n` they have degrees `2`, `1`
and `n - 3`. -/
theorem exists_monic_squarefree_count_two_map_natDegree_normalizedFactors_eq_one_and_odd
    [DecidableEq k] (n : ℕ) (hn : 3 ≤ n) :
    ∃ g : k[X], g.Monic ∧ g.natDegree = n ∧ Squarefree g ∧
      ((normalizedFactors g).map natDegree).count 2 = 1 ∧
      ∀ d ∈ (normalizedFactors g).map natDegree, d ≠ 2 → Odd d := by
  obtain ⟨q, qmonic, qirr, qdeg⟩ := exists_monic_irreducible_natDegree_eq k 2 two_pos
  have qX : q ≠ X := fun h ↦ by simp [h] at qdeg
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- even degree: factors of degrees `2`, `1` and `n - 3`
    obtain ⟨h, hmonic, hirr, hdeg, hX⟩ :=
      exists_monic_irreducible_natDegree_eq_ne_X k (m + m - 3) (by omega)
    have hq : h ≠ q := fun h' ↦ by rw [h'] at hdeg; omega
    obtain ⟨g, gmonic, gdeg, gsq, gfac⟩ := exists_monic_squarefree_of_nodup k (s := {q, X, h})
      (by simp [monic_X, qmonic, hmonic]) (by simp [irreducible_X, qirr, hirr])
      (by simp [qX, Ne.symm hq, Ne.symm hX])
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, natDegree_X, qdeg, hdeg] at gdeg gfac
    refine ⟨g, gmonic, by omega, gsq, ?_, ?_⟩
    · simp [gfac]
      omega
    · simp only [gfac, Multiset.mem_cons, Multiset.mem_singleton]
      rintro d (rfl | rfl | rfl) hd
      · exact absurd rfl hd
      · exact odd_one
      · exact ⟨m - 2, by omega⟩
  · -- odd degree: factors of degrees `2` and `n - 2`
    obtain ⟨h, hmonic, hirr, hdeg⟩ :=
      exists_monic_irreducible_natDegree_eq k (2 * m + 1 - 2) (by omega)
    have hq : h ≠ q := fun h' ↦ by rw [h'] at hdeg; omega
    obtain ⟨g, gmonic, gdeg, gsq, gfac⟩ := exists_monic_squarefree_of_nodup k (s := {q, h})
      (by simp [qmonic, hmonic]) (by simp [qirr, hirr]) (by simp [Ne.symm hq])
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, qdeg, hdeg] at gdeg gfac
    refine ⟨g, gmonic, by omega, gsq, ?_, ?_⟩
    · simp [gfac]
      omega
    · simp only [gfac, Multiset.mem_cons, Multiset.mem_singleton]
      rintro d (rfl | rfl) hd
      · exact absurd rfl hd
      · exact ⟨m - 1, by omega⟩

end TauCeti
