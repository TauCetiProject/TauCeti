/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.PerfectMatching
public import TauCeti.Data.Finset.Sort

/-!
# Pair-weighted sums over noncrossing pairings

Let `K : α → α → M` be a kernel on a linear order `α`, assigning the weight `K a b` to each
ordered pair `(a, b)` with `a < b`. Extending `K` to finite subsets `B : Finset α` by
`pairWeight K {a, b} = K a b` for `a < b` and `pairWeight K B = 0` when `#B ≠ 2` turns sums over
all noncrossing partitions of `s` into sums over the noncrossing pairings of `s`:

`∑ P ∈ NC(s), ∏ B ∈ P, pairWeight K B = ∑ P ∈ NC₂(s), ∏ B ∈ P, pairWeight K B`.

These sums are the combinatorial right-hand side of the free Wick formula for semicircular
systems, where `K i j = C i j` is the covariance (for instance `⟪h i, h j⟫_𝕜` on a full Fock
space, which is Hermitian rather than symmetric over `ℂ`, so the ordered-pair convention `a < b` is
essential).

Splitting a noncrossing pairing of a nonempty set `s` at the partner `x > m` of the first position
`m = s.min' hs` gives the weighted partner recurrence
(`TauCeti.NoncrossingPartition.sum_isPairing_prod_pairWeight_eq_sum`): the total pair weight on `s`
is the sum over `x ∈ s` with `m < x` of `K m x` times the total pair weight on `{y ∈ s | m < y < x}`
times the total pair weight on `{y ∈ s | x < y}`.

## Main definitions

* `TauCeti.NoncrossingPartition.pairWeight K B` — `K a b` when `B = {a, b}` with `a < b`, and `0`
  when `#B ≠ 2`.

## Main results

* `TauCeti.NoncrossingPartition.sum_prod_pairWeight_eq_sum_isPairing` — only noncrossing pairings
  contribute to `∑ P : NoncrossingPartition s, ∏ B ∈ P.1.parts, pairWeight K B`.
* `TauCeti.NoncrossingPartition.sum_prod_pairWeight_eq_sum`,
  `TauCeti.NoncrossingPartition.sum_isPairing_prod_pairWeight_eq_sum` — the weighted recurrence by
  the partner of the first position `s.min' hs`.
* `TauCeti.PerfectMatching.prod_pairWeight_toFinpartition`,
  `TauCeti.PerfectMatching.sum_isNoncrossingMatching_prod_eq_sum_isPairing` — reformulation in
  terms of noncrossing perfect matchings via `noncrossingPairingEquiv`, without assuming symmetry
  of `K`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 8
  (Wick formula for semicircular families) and Lecture 9.
-/

public section

open Finset

namespace TauCeti.NoncrossingPartition

section PairWeight

variable {α β M : Type*} [LinearOrder α] [LinearOrder β]

/-- The weight of a finite set `B` under an ordered-pair kernel `K`: for a two-element set `{a, b}`
with `a < b` it is `K a b`, and for a set of any other size it is `0`. -/
def pairWeight [Zero M] (K : α → α → M) (B : Finset α) : M :=
  match B.sort with
  | [a, b] => K a b
  | _ => 0

theorem pairWeight_def [Zero M] (K : α → α → M) (B : Finset α) :
    pairWeight K B = match B.sort with | [a, b] => K a b | _ => 0 :=
  (rfl)

@[simp]
theorem pairWeight_pair [Zero M] (K : α → α → M) {a b : α} (hab : a < b) :
    pairWeight K {a, b} = K a b := by
  rw [pairWeight, sort_pair _ hab.le hab.ne]

@[simp]
theorem pairWeight_pair_of_gt [Zero M] (K : α → α → M) {a b : α} (hba : b < a) :
    pairWeight K {a, b} = K b a := by
  rw [pair_comm, pairWeight_pair K hba]

theorem pairWeight_eq_zero_of_card_ne_two [Zero M] (K : α → α → M) {B : Finset α}
    (hB : #B ≠ 2) : pairWeight K B = 0 := by
  rw [pairWeight]
  split
  · rename_i a b h
    have hlen := congrArg List.length h
    rw [length_sort] at hlen
    exact absurd hlen hB
  · rfl

@[simp]
theorem pairWeight_empty [Zero M] (K : α → α → M) : pairWeight K (∅ : Finset α) = 0 := by
  simp [pairWeight]

@[simp]
theorem pairWeight_singleton [Zero M] (K : α → α → M) (a : α) : pairWeight K {a} = 0 := by
  simp [pairWeight]

@[simp]
theorem pairWeight_zero [Zero M] (B : Finset α) : pairWeight (0 : α → α → M) B = 0 := by
  rw [pairWeight_def]
  split <;> rfl

@[simp]
theorem pairWeight_const_zero [Zero M] (B : Finset α) :
    pairWeight (fun _ _ : α => (0 : M)) B = 0 :=
  pairWeight_zero B

/-- Applying a zero-preserving map commutes with `pairWeight`. -/
theorem apply_pairWeight {N : Type*} [Zero M] [Zero N] {f : M → N} (hf : f 0 = 0)
    (K : α → α → M) (B : Finset α) :
    f (pairWeight K B) = pairWeight (fun a b => f (K a b)) B := by
  rw [pairWeight_def, pairWeight_def]
  generalize B.sort = l
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp [hf]

@[simp]
theorem map_pairWeight {F N : Type*} [Zero M] [Zero N] [FunLike F M N] [ZeroHomClass F M N]
    (f : F) (K : α → α → M) (B : Finset α) :
    f (pairWeight K B) = pairWeight (fun a b => f (K a b)) B :=
  apply_pairWeight (map_zero f) K B

/-- On a two-element set `B`, `pairWeight K B` evaluates `K` at `(B.min', B.max')`. -/
theorem pairWeight_eq_min'_max' [Zero M] (K : α → α → M) {B : Finset α} (hB : #B = 2) :
    pairWeight K B = K (B.min' (card_pos.1 (by omega))) (B.max' (card_pos.1 (by omega))) := by
  obtain ⟨a, b, hne, rfl⟩ := card_eq_two.1 hB
  rcases lt_or_gt_of_ne hne with hab | hba
  · rw [pairWeight_pair K hab, min'_pair, max'_pair, min_eq_left hab.le, max_eq_right hab.le]
  · rw [pairWeight_pair_of_gt K hba, min'_pair, max'_pair, min_eq_right hba.le, max_eq_left hba.le]

/-- `pairWeight` commutes with strictly monotone embeddings of the index order. -/
@[simp]
theorem pairWeight_map_orderEmbedding [Zero M] (e : α ↪o β) (K : β → β → M) (B : Finset α) :
    pairWeight K (B.map e.toEmbedding) = pairWeight (fun x y => K (e x) (e y)) B := by
  have hsort : (B.map e.toEmbedding).sort = B.sort.map e := by
    simpa using (e.strictMono.strictMonoOn B).map_finsetSort.symm
  rw [pairWeight_def, pairWeight_def, hsort]
  generalize B.sort = l
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> rfl

/-- Constant pair weight `v` recovers the indicator `if #B = 2 then v else 0`. -/
theorem pairWeight_const [Zero M] (v : M) (B : Finset α) :
    pairWeight (fun _ _ : α => v) B = if #B = 2 then v else 0 := by
  split_ifs with hB
  · exact pairWeight_eq_min'_max' _ hB
  · exact pairWeight_eq_zero_of_card_ne_two _ hB

/-- The product of `pairWeight K` over the parts of a partition that is not a pairing vanishes. -/
theorem prod_pairWeight_eq_zero_of_not_isPairing [CommMonoidWithZero M] {s : Finset α}
    {P : Finpartition s} (hP : ¬P.IsPairing) (K : α → α → M) :
    ∏ B ∈ P.parts, pairWeight K B = 0 := by
  rw [Finpartition.isPairing_iff] at hP
  push Not at hP
  obtain ⟨B, hB, hcard⟩ := hP
  exact prod_eq_zero hB (pairWeight_eq_zero_of_card_ne_two K hcard)

end PairWeight

section Sum

variable {α M : Type*} [LinearOrder α] [CommSemiring M] {s : Finset α}

/-- Only the noncrossing pairings contribute to the sum of `∏ B ∈ P.1.parts, pairWeight K B` over
all noncrossing partitions of `s`. -/
theorem sum_prod_pairWeight_eq_sum_isPairing (s : Finset α) (K : α → α → M) :
    (∑ P : NoncrossingPartition s, ∏ B ∈ P.1.parts, pairWeight K B) =
      ∑ P : {P : NoncrossingPartition s // P.1.IsPairing}, ∏ B ∈ P.1.1.parts, pairWeight K B := by
  rw [← sum_subtype (univ.filter fun P : NoncrossingPartition s => P.1.IsPairing)
    (p := fun P => P.1.IsPairing) (fun _ => by simp) (fun P => ∏ B ∈ P.1.parts, pairWeight K B),
    sum_filter]
  refine sum_congr rfl fun P _ => ?_
  split_ifs with hP
  · rfl
  · exact prod_pairWeight_eq_zero_of_not_isPairing hP K

theorem sum_empty_prod_pairWeight (K : α → α → M) :
    (∑ P : NoncrossingPartition (∅ : Finset α), ∏ B ∈ P.1.parts, pairWeight K B) = 1 := by
  rw [Fintype.sum_unique]
  simp [Unique.default_eq ⊥]

@[simp]
theorem sum_isPairing_empty_prod_pairWeight (K : α → α → M) :
    (∑ P : {P : NoncrossingPartition (∅ : Finset α) // P.1.IsPairing},
      ∏ B ∈ P.1.1.parts, pairWeight K B) = 1 := by
  rw [← sum_prod_pairWeight_eq_sum_isPairing, sum_empty_prod_pairWeight]

/-- On a set of odd cardinality, the pair-weighted sum over noncrossing pairings vanishes. -/
theorem sum_isPairing_prod_pairWeight_eq_zero (hs : Odd #s) (K : α → α → M) :
    (∑ P : {P : NoncrossingPartition s // P.1.IsPairing},
      ∏ B ∈ P.1.1.parts, pairWeight K B) = 0 := by
  have : IsEmpty {P : NoncrossingPartition s // P.1.IsPairing} :=
    ⟨fun P => Nat.not_even_iff_odd.2 hs P.2.even_card⟩
  simp

theorem sum_prod_pairWeight_eq_zero (hs : Odd #s) (K : α → α → M) :
    (∑ P : NoncrossingPartition s, ∏ B ∈ P.1.parts, pairWeight K B) = 0 := by
  rw [sum_prod_pairWeight_eq_sum_isPairing, sum_isPairing_prod_pairWeight_eq_zero hs]

private theorem sum_before_pairWeight_insert_eq (hs : s.Nonempty) (K : α → α → M) (x : α) :
    (∑ L : NoncrossingPartition {y ∈ s | y < x},
        pairWeight K (insert x (L.1.part (s.min' hs))) *
          ∏ B ∈ L.1.parts with s.min' hs ∉ B, pairWeight K B) =
      if s.min' hs < x then
        K (s.min' hs) x *
          ∑ M : NoncrossingPartition {y ∈ s | s.min' hs < y ∧ y < x},
            ∏ B ∈ M.1.parts, pairWeight K B
      else 0 := by
  set m := s.min' hs
  split_ifs with hmx
  · have hmt : m ∈ {y ∈ s | y < x} := mem_filter.2 ⟨s.min'_mem hs, hmx⟩
    -- Only partitions `L` in which `{m}` is a singleton part make `insert x (L.1.part m)` a pair.
    have hterm (L : NoncrossingPartition {y ∈ s | y < x}) :
        pairWeight K (insert x (L.1.part m)) *
            (∏ B ∈ L.1.parts with m ∉ B, pairWeight K B) =
          if {m} ∈ L.1.parts then
            K m x * ∏ B ∈ L.1.parts.erase {m}, pairWeight K B
          else 0 := by
      split_ifs with hmL
      · have hpart : L.1.part m = {m} := L.1.part_eq_of_mem hmL (mem_singleton_self m)
        have herase_parts : {B ∈ L.1.parts | m ∉ B} = L.1.parts.erase {m} := by
          ext B
          rw [mem_filter, mem_erase]
          exact ⟨fun ⟨hB, hmB⟩ => ⟨fun h => hmB (h ▸ mem_singleton_self m), hB⟩,
            fun ⟨hBne, hB⟩ => ⟨hB, fun hmB => hBne ((L.1.part_eq_of_mem hB hmB).symm.trans hpart)⟩⟩
        rw [herase_parts, hpart, pair_comm x m, pairWeight_pair K hmx]
      · have hxL : x ∉ L.1.part m := fun h =>
          (mem_filter.1 (L.1.part_subset m h)).2.false
        have hcard1 : #(L.1.part m) ≠ 1 := fun hc1 => by
          obtain ⟨z, hz⟩ := card_eq_one.1 hc1
          have hmz : m = z := mem_singleton.1 (hz ▸ L.1.mem_part_self.2 hmt)
          exact hmL (hmz ▸ hz ▸ L.1.part_mem.2 hmt)
        have hcard2 : #(insert x (L.1.part m)) ≠ 2 := by
          rw [card_insert_of_notMem hxL]
          omega
        rw [pairWeight_eq_zero_of_card_ne_two K hcard2, zero_mul]
    have herase : ({y ∈ s | y < x}).erase m = {y ∈ s | m < y ∧ y < x} := by
      ext y
      simp only [mem_erase, mem_filter]
      exact ⟨fun ⟨hym, hys, hyx⟩ => ⟨hys, (s.min'_le y hys).lt_of_ne hym.symm, hyx⟩,
        fun ⟨hys, hmy, hyx⟩ => ⟨hmy.ne', hys, hyx⟩⟩
    rw [← herase, sum_congr rfl fun L _ => hterm L, ← sum_filter,
      sum_subtype (p := fun L : NoncrossingPartition {y ∈ s | y < x} => {m} ∈ L.1.parts) _
        (fun _ => by simp),
      mul_sum]
    refine Fintype.sum_equiv (singletonPartEquiv hmt) _ _ fun L => ?_
    simp
  · refine sum_eq_zero fun L _ => ?_
    have hempty : L.1.part m = ∅ :=
      L.1.part_eq_empty.2 fun h =>
        hmx ((s.min'_le _ (mem_filter.1 h).1).trans_lt (mem_filter.1 h).2)
    rw [hempty, insert_empty_eq, pairWeight_singleton, zero_mul]

/-- **Weighted partner recurrence for noncrossing partitions.** Weighting two-element parts by
`pairWeight K` and all other parts by `0`, the sum over `NC(s)` for nonempty `s` splits by the
partner `x > s.min' hs` of the first position `s.min' hs`. -/
theorem sum_prod_pairWeight_eq_sum (hs : s.Nonempty) (K : α → α → M) :
    (∑ P : NoncrossingPartition s, ∏ B ∈ P.1.parts, pairWeight K B) =
      ∑ x ∈ s with s.min' hs < x, K (s.min' hs) x *
        (∑ M : NoncrossingPartition {y ∈ s | s.min' hs < y ∧ y < x},
          ∏ B ∈ M.1.parts, pairWeight K B) *
        ∑ R : NoncrossingPartition {y ∈ s | x < y}, ∏ B ∈ R.1.parts, pairWeight K B := by
  rw [sum_congr rfl fun P _ => P.1.prod_parts_eq_mul_prod_filter_notMem (s.min'_mem hs) _,
    sum_mul_prod_eq_sum_mul_sum hs, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_before_pairWeight_insert_eq hs K x]
  split_ifs <;> simp

/-- **Weighted partner recurrence for noncrossing pairings.** For nonempty `s`, the sum over
noncrossing pairings `NC₂(s)` splits by the partner `x > s.min' hs` of `s.min' hs` into a
noncrossing pairing of `{y ∈ s | s.min' hs < y ∧ y < x}` and one of `{y ∈ s | x < y}`. -/
theorem sum_isPairing_prod_pairWeight_eq_sum (hs : s.Nonempty) (K : α → α → M) :
    (∑ P : {P : NoncrossingPartition s // P.1.IsPairing},
        ∏ B ∈ P.1.1.parts, pairWeight K B) =
      ∑ x ∈ s with s.min' hs < x, K (s.min' hs) x *
        (∑ M : {M : NoncrossingPartition {y ∈ s | s.min' hs < y ∧ y < x} // M.1.IsPairing},
          ∏ B ∈ M.1.1.parts, pairWeight K B) *
        ∑ R : {R : NoncrossingPartition {y ∈ s | x < y} // R.1.IsPairing},
          ∏ B ∈ R.1.1.parts, pairWeight K B := by
  simp_rw [← sum_prod_pairWeight_eq_sum_isPairing]
  exact sum_prod_pairWeight_eq_sum hs K

end Sum

end TauCeti.NoncrossingPartition

namespace TauCeti.PerfectMatching

section PairWeight

variable {α M : Type*} [Fintype α] [LinearOrder α]

/-- For a perfect matching `D` on a finite linear order, the product of `pairWeight K` over the
two-element orbits of `D` is the product of `K a (D.val a)` over the left endpoints `a < D.val a`.
No symmetry of `K` is required. -/
theorem prod_pairWeight_toFinpartition [CommMonoid M] [Zero M] (D : PerfectMatching α)
    (K : α → α → M) :
    ∏ B ∈ D.toFinpartition.parts, NoncrossingPartition.pairWeight K B =
      ∏ a ∈ univ with a < D.val a, K a (D.val a) := by
  symm
  refine prod_bij (fun a _ => D.toFinpartition.part a)
    (fun a _ => D.toFinpartition.part_mem.2 (mem_univ a)) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ hpart
    have ha₁' := (mem_filter.1 ha₁).2
    have ha₂' := (mem_filter.1 ha₂).2
    have hmem : a₂ ∈ ({a₁, D.val a₁} : Finset α) := by
      rw [← part_toFinpartition, hpart, part_toFinpartition]
      simp
    rcases mem_insert.1 hmem with rfl | h
    · rfl
    · rw [mem_singleton.1 h, D.apply_apply] at ha₂'
      exact absurd (ha₁'.trans ha₂') (lt_irrefl _)
  · intro B hB
    obtain ⟨x, hx⟩ := D.toFinpartition.nonempty_of_mem_parts hB
    have hBx : D.toFinpartition.part x = B := D.toFinpartition.part_eq_of_mem hB hx
    rcases lt_or_gt_of_ne (D.apply_ne x).symm with hlt | hgt
    · exact ⟨x, mem_filter.2 ⟨mem_univ x, hlt⟩, hBx⟩
    · refine ⟨D.val x, mem_filter.2 ⟨mem_univ _, by simpa using hgt⟩, ?_⟩
      rw [part_toFinpartition, D.apply_apply, pair_comm, ← part_toFinpartition, hBx]
  · intro a ha
    rw [part_toFinpartition, NoncrossingPartition.pairWeight_pair K (mem_filter.1 ha).2]

/-- Summing `∏_{a < D a} K a (D a)` over noncrossing perfect matchings of a finite linear order
computes the pair-weighted sum over noncrossing pairings. -/
theorem sum_isNoncrossingMatching_prod_eq_sum_isPairing [CommSemiring M] (K : α → α → M) :
    (∑ D : {D : PerfectMatching α // D.val.IsNoncrossingMatching},
        ∏ a ∈ univ with a < D.val.val a, K a (D.val.val a)) =
      ∑ P : {P : NoncrossingPartition (univ : Finset α) // P.val.IsPairing},
        ∏ B ∈ P.1.1.parts, NoncrossingPartition.pairWeight K B := by
  refine Fintype.sum_equiv noncrossingPairingEquiv _ _ fun D => ?_
  rw [noncrossingPairingEquiv_apply_coe, prod_pairWeight_toFinpartition]

end PairWeight

end TauCeti.PerfectMatching
