/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Basic
import TauCeti.Data.List.Finite

/-!
# Bounded words of positive degree changes

A word of allowed nonzero increments has length at most the degree of its sum.
`PositiveDegrees.wordCutoff` gives a finite index type of all such words at a fixed
cutoff, using the weighted-list theorem built on Mathlib's `List.finite_length_le`.
Filtering zero increments from an allowed word preserves the sum and puts the
result in the same word cutoff. The increments retain their actual degrees,
including nonzero degrees in the kernel of a geometric projection.

Adapted from `Mei/Algebra/PositiveDegrees/Word.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e`, released under Apache 2.0.
-/

public section

namespace TauCeti.PositiveDegrees

variable {N : Type*} [AddCommMonoid N] (d : PositiveDegrees N)

/-- All words of nonzero allowed increments with total degree at most `k`. -/
def wordCutoff (k : ℕ) : Set (List N) :=
  {l | (∀ n ∈ l, n ∈ d.monoid ∧ n ≠ 0) ∧ d.degree l.sum ≤ k}

/-- Membership in the finite word cutoff. -/
@[simp]
theorem mem_wordCutoff {k : ℕ} {l : List N} :
    l ∈ d.wordCutoff k ↔ (∀ n ∈ l, n ∈ d.monoid ∧ n ≠ 0) ∧ d.degree l.sum ≤ k :=
  Iff.rfl

/-- The number of nonzero allowed increments is bounded by their total degree. -/
theorem length_le_degree_sum (l : List N) (hP : ∀ n ∈ l, n ∈ d.monoid)
    (hne : ∀ n ∈ l, n ≠ 0) : (l.length : ℤ) ≤ d.degree l.sum := by
  have h := List.length_nsmul_le_sum (l.map d.degree) (1 : ℤ) (by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
    have := d.degree_pos (hP n hn) (hne n hn)
    omega)
  simpa only [List.length_map, nsmul_eq_mul, mul_one, ← map_list_sum] using h

/-- Every cutoff of words of nonzero allowed increments is finite. -/
theorem finite_wordCutoff (k : ℕ) : (d.wordCutoff k).Finite := by
  have hcut : {n : N | (n ∈ d.monoid ∧ n ≠ 0) ∧ d.degree n ≤ k}.Finite :=
    (d.finite_cutoff k).subset fun _ hn => d.mem_cutoff.mpr ⟨hn.1.1, hn.2⟩
  simpa only [wordCutoff, Set.mem_ofPred_eq, ← map_list_sum] using
    List.finite_setOf_sum_map_le (s := {n : N | n ∈ d.monoid ∧ n ≠ 0}) d.degree k
      (fun _ hn => d.degree_pos hn.1 hn.2) hcut

/-- Word cutoffs can index finite families of degree changes. -/
instance (k : ℕ) : Finite (d.wordCutoff k) := (d.finite_wordCutoff k).to_subtype

variable [DecidableEq N]

/-- Removing zeros sends allowed words of total degree at most `k` into the word cutoff. -/
theorem filter_bne_zero_image_subset_wordCutoff (k : ℕ) :
    (fun l : List N => l.filter (· != 0)) ''
      {l | (∀ n ∈ l, n ∈ d.monoid) ∧ d.degree l.sum ≤ k} ⊆ d.wordCutoff k := by
  rintro _ ⟨l, hl, rfl⟩
  refine ⟨?_, ?_⟩
  · intro n hn
    exact ⟨hl.1 n (List.mem_filter.mp hn).1, by simpa using (List.mem_filter.mp hn).2⟩
  · simpa only [List.sum_filter_bne_zero] using hl.2

/-- A word of allowed increments and total degree at most `k` has at most `k`
nonzero increments. -/
theorem length_filter_bne_zero_le (l : List N) (hP : ∀ n ∈ l, n ∈ d.monoid)
    (k : ℕ) (hk : d.degree l.sum ≤ k) : (l.filter (· != 0)).length ≤ k := by
  have hred := d.filter_bne_zero_image_subset_wordCutoff k ⟨l, ⟨hP, hk⟩, rfl⟩
  have hmem := (d.mem_wordCutoff.mp hred).1
  have h := d.length_le_degree_sum _ (fun n hn => (hmem n hn).1)
    (fun n hn => (hmem n hn).2)
  exact_mod_cast h.trans (d.mem_wordCutoff.mp hred).2

/-- Zero-filtered words of allowed increments with total degree at most `k` form a finite set. -/
theorem finite_reduced_degree_words_cutoff (k : ℕ) :
    Set.Finite ((fun l : List N => l.filter (· != 0)) ''
      {l | (∀ n ∈ l, n ∈ d.monoid) ∧ d.degree l.sum ≤ k}) :=
  (d.finite_wordCutoff k).subset (d.filter_bne_zero_image_subset_wordCutoff k)

end TauCeti.PositiveDegrees
