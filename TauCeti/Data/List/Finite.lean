/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.List

/-!
# Finitely many words of bounded degree

A positive integer weight bounds a word's length by its total weight. If the
letters of weight at most the cutoff are finite, the words are finite as well.

## Main results

* `TauCeti.finite_setOf_sum_map_le`: a finite cutoff alphabet gives finitely many words
  below the same positive integer-weight cutoff.
* `List.finite_setOf_sum_map_snd_add_one_le`: words in pairs of a finite label and a
  natural number have finite cutoffs when each weight is the second entry plus one.
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
  change (l.attachWith (· ∈ {a ∈ s | w a ≤ k}) hentry).length ≤ k
  rw [List.length_attachWith]
  exact_mod_cast hlen.trans hsum

end TauCeti

namespace List

/-- Over a finite alphabet `α`, there are finitely many words `l : List (α × ℕ)` whose total
degree `(l.map fun p => p.2 + 1).sum` is at most `K`. -/
theorem finite_setOf_sum_map_snd_add_one_le (α : Type*) [Finite α] (K : ℕ) :
    {l : List (α × ℕ) | (l.map fun p => p.2 + 1).sum ≤ K}.Finite := by
  let w (p : α × ℕ) : ℤ := (p.2 + 1 : ℕ)
  have hcut : {p ∈ (Set.univ : Set (α × ℕ)) | w p ≤ K}.Finite := by
    refine (Set.finite_range (fun p : α × Fin (K + 1) => (p.1, (p.2 : ℕ)))).subset ?_
    rintro ⟨a, n⟩ ⟨_, hn⟩
    change ((n + 1 : ℕ) : ℤ) ≤ K at hn
    exact ⟨(a, ⟨n, by omega⟩), rfl⟩
  have hpos (p : α × ℕ) : 0 < w p := by
    dsimp [w]
    omega
  refine (TauCeti.finite_setOf_sum_map_le w K (fun p _ => hpos p) hcut).subset ?_
  intro l hl
  refine ⟨fun _ _ => Set.mem_univ _, ?_⟩
  change (l.map fun p => p.2 + 1).sum ≤ K at hl
  change (l.map (Nat.castAddMonoidHom ℤ ∘ fun p => p.2 + 1)).sum ≤ K
  rw [← List.map_map, ← map_list_sum]
  exact Int.ofNat_le.mpr hl

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
  · change (blocks.attachWith List.Nodup hb).length = l.length + 1
    rw [List.length_attachWith]
    exact hlen
  · exact Prod.ext rfl (List.attachWith_map_subtype_val hb)
