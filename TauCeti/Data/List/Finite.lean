/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.List

/-!
# Finite lists over finite types

A positive integer weight bounds a word's length by its total weight. If the
letters of weight at most the cutoff are finite, the words are finite as well.
This file also shows that any duplicate-free list over a finite type can be extended
to a duplicate-free list covering every element.

## Main results

* `TauCeti.finite_setOf_sum_map_le`: a finite cutoff alphabet gives finitely many words
  below the same positive integer-weight cutoff.
* `TauCeti.finite_setOf_sum_map_le_nat`: the finite-cutoff theorem for positive natural weights.
* `List.finite_setOf_sum_map_snd_add_one_le`: words in pairs of a finite label and a
  natural number have finite cutoffs when each weight is the second entry plus one.
* `List.Nodup.exists_append_forall_mem`: completes a duplicate-free list over a finite type to a
  duplicate-free list containing every element.
* `Set.Finite.nodup_blocks`: a finite set of lists admits finitely many records
  formed by placing one duplicate-free label block in each gap.
-/

public section

namespace List

/-- The length of a list is at most the sum of its strictly positive integer weights. -/
theorem length_le_sum_map_of_pos {α : Type*} (l : List α) (w : α → ℤ)
    (h : ∀ a ∈ l, 0 < w a) : (l.length : ℤ) ≤ (l.map w).sum := by
  have hweight (b : ℤ) (hb : b ∈ l.map w) : 1 ≤ b := by
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
    have := h a ha
    omega
  simpa only [length_map, nsmul_eq_mul, mul_one] using
    (length_nsmul_le_sum (l.map w) (1 : ℤ) hweight)

end List

namespace TauCeti

/-- Over an alphabet of positive integer weights, a fixed weight cutoff permits
only finitely many words whenever it permits only finitely many letters. -/
theorem finite_setOf_sum_map_le {α : Type*} {s : Set α} (w : α → ℤ) (k : ℕ)
    (hpos : ∀ a ∈ s, 0 < w a) (hcut : {a ∈ s | w a ≤ k}.Finite) :
    {l : List α | (∀ a ∈ l, a ∈ s) ∧ (l.map w).sum ≤ k}.Finite := by
  let : Finite {a ∈ s | w a ≤ k} := hcut.to_subtype
  apply ((List.finite_length_le {a ∈ s | w a ≤ k} k).image (List.map Subtype.val)).subset
  rintro l ⟨hs, hsum⟩
  have hentry (a : α) (ha : a ∈ l) : a ∈ {a ∈ s | w a ≤ k} :=
    ⟨hs a ha, (List.single_le_sum (by simpa using fun b hb => (hpos b (hs b hb)).le)
      _ (List.mem_map_of_mem ha)).trans hsum⟩
  have hlen := l.length_le_sum_map_of_pos w (fun a ha => hpos a (hs a ha))
  refine ⟨l.attachWith _ hentry, ?_, List.attachWith_map_subtype_val hentry⟩
  rw [Set.mem_ofPred_eq, List.length_attachWith]
  exact_mod_cast hlen.trans hsum

/-- Positive natural weights with a finite letter cutoff give finitely many words
below the same weight cutoff. -/
theorem finite_setOf_sum_map_le_nat {α : Type*} {s : Set α} (w : α → ℕ) (k : ℕ)
    (hpos : ∀ a ∈ s, 0 < w a) (hcut : {a ∈ s | w a ≤ k}.Finite) :
    {l : List α | (∀ a ∈ l, a ∈ s) ∧ (l.map w).sum ≤ k}.Finite := by
  apply (finite_setOf_sum_map_le (fun a => (w a : ℤ)) k
    (fun a ha => by exact_mod_cast hpos a ha) (by simpa only [Nat.cast_le] using hcut)).subset
  rintro l ⟨hs, hl⟩
  have hcast : ((l.map w).sum : ℤ) ≤ k := by exact_mod_cast hl
  rw [Nat.cast_list_sum, List.map_map] at hcast
  exact ⟨hs, hcast⟩

end TauCeti

namespace List

/-- Over a finite alphabet `α`, there are finitely many words `l : List (α × ℕ)` whose total
degree `(l.map fun p => p.2 + 1).sum` is at most `K`. -/
theorem finite_setOf_sum_map_snd_add_one_le (α : Type*) [Finite α] (K : ℕ) :
    {l : List (α × ℕ) | (l.map fun p => p.2 + 1).sum ≤ K}.Finite := by
  let w (p : α × ℕ) := p.2 + 1
  have hcut : {p ∈ (Set.univ : Set (α × ℕ)) | w p ≤ K}.Finite := by
    refine (Set.finite_range (fun p : α × Fin (K + 1) => (p.1, (p.2 : ℕ)))).subset ?_
    rintro ⟨a, n⟩ ⟨_, hn⟩
    dsimp only [w] at hn
    exact ⟨(a, ⟨n, by omega⟩), rfl⟩
  exact (TauCeti.finite_setOf_sum_map_le_nat w K
    (fun p _ => Nat.succ_pos p.2) hcut).subset fun _ hl => ⟨fun _ _ => Set.mem_univ _, hl⟩

/-- Completes a duplicate-free list over a finite type to a duplicate-free list covering every
element. -/
theorem Nodup.exists_append_forall_mem {ι : Type*} [Finite ι] {l : List ι} (hl : l.Nodup) :
    ∃ l' : List ι, (l ++ l').Nodup ∧ ∀ i : ι, i ∈ l ++ l' := by
  classical
  obtain ⟨all, hall, hmem⟩ := Finite.exists_univ_list ι
  have hperm : List.Perm (l ++ all.diff l) all :=
    List.subperm_append_diff_self_of_count_le (List.subperm_ext_iff.mp
      (hl.subperm fun i _ ↦ hmem i))
  exact ⟨all.diff l, hperm.nodup_iff.2 hall, fun i ↦ hperm.mem_iff.2 (hmem i)⟩

end List

/-- A finite set of lists admits finitely many records with one duplicate-free block
of labels before, between, and after its entries, over a finite label type.

Adapted from `Mei/Algebra/PositiveDegrees/Word.lean` at commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0, Mei contributors, author Codex). -/
theorem Set.Finite.nodup_blocks {α ι : Type*} [Finite ι] {S : Set (List α)}
    (hS : S.Finite) :
    {p : List α × List (List ι) |
      p.1 ∈ S ∧ p.2.length = p.1.length + 1 ∧ ∀ b ∈ p.2, b.Nodup}.Finite := by
  classical
  let := Fintype.ofFinite ι
  let Block := {b : List ι // b.Nodup}
  apply (hS.biUnion (fun l _ =>
    (List.finite_length_eq Block (l.length + 1)).image
      (fun bs => (l, bs.map Subtype.val)))).subset
  rintro ⟨l, blocks⟩ ⟨hl, hlen, hb⟩
  refine Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨hl, ?_⟩⟩
  refine ⟨blocks.attachWith List.Nodup hb, ?_, ?_⟩
  · rw [Set.mem_ofPred_eq, List.length_attachWith]
    exact hlen
  · exact Prod.ext rfl (List.attachWith_map_subtype_val hb)
