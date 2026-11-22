/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Map
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.List

/-!
# Bounded words of positive degree changes

A word of allowed nonzero increments has length at most the degree of its sum.
At a fixed degree cutoff there are finitely many such words: every increment
lies in the finite cutoff, and the word length is bounded. For words permitting
zero increments, filtering out zero preserves the sum and leaves at most the
cutoff number of entries. A positive degree map transports the bound through
its cutoff modulus. Thus arbitrary insertions of zero increments do not
enlarge the finite set of reduced degree itineraries. Finite encounter labels
also give finitely many records when each constant-degree block meets each label
at most once: a record has one such block before the first change and after each
change. Encounters acting by the identity on the decoration are retained in these
blocks without being counted as degree changes.

These are the degree-only bounds used for successive homogeneous component
changes. Geometric itineraries additionally carry encounter and chart data.
The increments retain their actual degrees, including nonzero degrees in the
kernel of a geometric projection. No finite generation, saturation, cancellation,
or group hypothesis is needed.
-/

public section

namespace TauCeti.PositiveDegrees

variable {N : Type*} [AddCommMonoid N] (d : PositiveDegrees N)

/-- The number of nonzero allowed increments is bounded by their total degree. -/
theorem length_le_degree_sum (l : List N) (hP : ∀ n ∈ l, n ∈ d.monoid)
    (hne : ∀ n ∈ l, n ≠ 0) : (l.length : ℤ) ≤ d.degree l.sum := by
  have h := List.length_nsmul_le_sum (l.map d.degree) (1 : ℤ) (by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
    have := d.degree_pos (hP n hn) (hne n hn)
    omega)
  simpa only [List.length_map, nsmul_eq_mul, mul_one, ← map_list_sum] using h

/-- Every increment in an allowed word has degree at most the total degree. -/
theorem degree_le_degree_sum (l : List N) (hP : ∀ n ∈ l, n ∈ d.monoid)
    {n : N} (hn : n ∈ l) : d.degree n ≤ d.degree l.sum := by
  have h := List.single_le_sum (l := l.map d.degree) (by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
    exact d.degree_nonneg (hP n hn)) (d.degree n) (List.mem_map.mpr ⟨n, hn, rfl⟩)
  simpa only [← map_list_sum] using h

/-- There are finitely many words of nonzero allowed increments whose total degree
is at most a fixed cutoff. -/
theorem finite_degree_words (k : ℕ) :
    Set.Finite {l : List N | (∀ n ∈ l, n ∈ d.monoid ∧ n ≠ 0) ∧ d.degree l.sum ≤ k} := by
  apply ((List.finite_length_le (d.cutoff k) k).image
    (fun l => l.map (fun n : d.cutoff k => (n : N)))).subset
  intro l hl
  let lifted : List (d.cutoff k) := l.attach.map fun (n : {n // n ∈ l}) =>
    ⟨n.val, d.mem_cutoff.mpr ⟨(hl.1 n.val n.property).1,
      (d.degree_le_degree_sum l (fun n hn => (hl.1 n hn).1) n.property).trans hl.2⟩⟩
  refine ⟨lifted, ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, lifted, List.length_map, List.length_attach]
    exact_mod_cast (d.length_le_degree_sum l (fun n hn => (hl.1 n hn).1)
      (fun n hn => (hl.1 n hn).2)).trans hl.2
  · simp only [lifted, List.map_map, Function.comp_def]
    exact List.attach_map_subtype_val l

/-- Finite encounter labels and a positive-degree cutoff give finitely many records
of nonzero degree changes and duplicate-free encounter lists between successive changes.
There is one encounter block before the first change and after each change. -/
theorem finite_degree_encounter_words {ι : Type*} [Finite ι] (k : ℕ) :
    Set.Finite {p : List N × List (List ι) |
      ((∀ n ∈ p.1, n ∈ d.monoid ∧ n ≠ 0) ∧ d.degree p.1.sum ≤ k) ∧
        p.2.length = p.1.length + 1 ∧ ∀ b ∈ p.2, b.Nodup} := by
  classical
  let := Fintype.ofFinite ι
  let Block := {b : List ι // b.Nodup}
  apply ((d.finite_degree_words k).biUnion (fun l _ =>
    Set.finite_range (fun f : Fin (l.length + 1) → Block =>
      (l, List.ofFn fun j => (f j).val)))).subset
  rintro ⟨l, blocks⟩ ⟨hl, hlen, hb⟩
  refine Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨hl, ?_⟩⟩
  rw [← hlen]
  refine ⟨fun j => ⟨blocks.get j, hb _ (List.get_mem blocks j)⟩, ?_⟩
  exact Prod.ext rfl (List.ofFn_get blocks)

variable [DecidableEq N]

/-- A word with allowed increments and total degree at most `k` has at most `k`
nonzero changes, irrespective of the number of inserted zero increments. -/
theorem length_filter_bne_zero_le (l : List N) (hP : ∀ n ∈ l, n ∈ d.monoid)
    (k : ℕ) (hk : d.degree l.sum ≤ k) : (l.filter (· != 0)).length ≤ k := by
  have h := d.length_le_degree_sum (l.filter (· != 0))
    (fun n hn => hP n (List.mem_filter.mp hn).1)
    (fun n hn => by simpa using (List.mem_filter.mp hn).2)
  rw [List.sum_filter_bne_zero] at h
  exact_mod_cast h.trans hk

/-- Reduced degree itineraries form a finite set even when zero increments may
be inserted arbitrarily before reduction. -/
theorem finite_reduced_degree_words (k : ℕ) :
    Set.Finite ((fun l : List N => l.filter (· != 0)) ''
      {l | (∀ n ∈ l, n ∈ d.monoid) ∧ d.degree l.sum ≤ k}) := by
  apply (d.finite_degree_words k).subset
  rintro _ ⟨l, hl, rfl⟩
  refine ⟨?_, ?_⟩
  · intro n hn
    exact ⟨hl.1 n (List.mem_filter.mp hn).1, by simpa using (List.mem_filter.mp hn).2⟩
  · simpa only [List.sum_filter_bne_zero] using hl.2

end TauCeti.PositiveDegrees

namespace TauCeti.PositiveDegreeMap

variable {N M : Type*} [AddCommMonoid N] [AddCommMonoid M]
  {d : PositiveDegrees N} {e : PositiveDegrees M} (T : PositiveDegreeMap d e)

/-- A target cutoff bounds the source words through the specified cutoff modulus,
even when the positive degree map identifies different allowed increments. -/
theorem finite_preimage_degree_words (k : ℕ) :
    Set.Finite {l : List N | (∀ n ∈ l, n ∈ d.monoid ∧ n ≠ 0) ∧
      e.degree (T l.sum) ≤ k} := by
  apply (d.finite_degree_words (T.modulus k)).subset
  intro l hl
  exact ⟨hl.1, T.degree_le k (d.monoid.list_sum_mem (fun n hn => (hl.1 n hn).1)) hl.2⟩

end TauCeti.PositiveDegreeMap
