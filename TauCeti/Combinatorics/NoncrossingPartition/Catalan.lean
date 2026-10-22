/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Finset.Max
public import TauCeti.Combinatorics.NoncrossingPartition.Basic
public import TauCeti.Order.Partition.Pairing
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Noncrossing partitions and noncrossing pairings are counted by the Catalan numbers

Let `s` be a nonempty finite set of positions in a linear order, with first position `m`. For a
noncrossing partition `P` of `s`, let `x` be the last position of the part of `P` containing `m`.
No part of `P` then joins a position before `x` to a position after `x`, so `P` is the same as a
noncrossing partition of the positions of `s` before `x` (with `x` adjoined to the part of `m`)
together with an arbitrary noncrossing partition of the positions of `s` after `x`. This is the
recurrence of noncrossing partitions by the part containing the first position, and it is the
recurrence of the Catalan numbers; hence there are `catalan n` noncrossing partitions of `n`
ordered positions.

The same decomposition counts the noncrossing pairings, the noncrossing partitions all of whose
parts have two elements, which index the moments of semicircular variables. In a noncrossing
pairing of `s` the first position `m` is paired with some `x > m`, and the pairing is the same as
a noncrossing pairing of the positions strictly between `m` and `x` together with one of the
positions after `x`. Hence there are `catalan n` noncrossing pairings of `2 * n` ordered positions,
and none of an odd number of positions.

## Main results

* `TauCeti.NoncrossingPartition.card_eq_sum_card_mul_card` — the recurrence by the part containing
  the first position: `|NC(s)| = ∑_{x ∈ s} |NC(s_{<x})| |NC(s_{>x})|`.
* `TauCeti.NoncrossingPartition.card_eq_catalan` — `|NC(s)| = catalan |s|`.
* `TauCeti.NoncrossingPartition.card_fin_eq_catalan` — `|NC(n)| = catalan n` for the positions
  of `Fin n`.
* `TauCeti.NoncrossingPartition.card_isPairing_eq_sum` — the recurrence of noncrossing pairings by
  the partner `x` of the first position `m`:
  `|NC₂(s)| = ∑_{x ∈ s, m < x} |NC₂(s ∩ (m, x))| |NC₂(s_{>x})|`.
* `TauCeti.NoncrossingPartition.card_isPairing_eq_catalan` — `|NC₂(s)| = catalan n` when
  `|s| = 2 n`, and `card_isPairing_eq_zero` — `|NC₂(s)| = 0` when `|s|` is odd.
* `TauCeti.NoncrossingPartition.card_isPairing_fin_eq_catalan` — `|NC₂(2n)| = catalan n` for the
  positions of `Fin (2 * n)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9.
* G. Kreweras, *Sur les partitions non croisées d'un cycle*, Discrete Math. 1 (1972), 333–350.
-/

public section

open Finset

namespace TauCeti.NoncrossingPartition

variable {α : Type*} [LinearOrder α] {s : Finset α} {m x : α}

section Glue

variable {L : Finpartition {y ∈ s | y < x}} {R : Finpartition {y ∈ s | x < y}}

/-- The label of a position in the glued partition `glue s m x L R`: the parts of `L` and `R`
through it, where `x` is sent to the part of `L` through `m`. -/
private def glueKey (m x : α) (L : Finpartition {y ∈ s | y < x})
    (R : Finpartition {y ∈ s | x < y}) (y : α) : Finset α × Finset α :=
  (L.part (if y = x then m else y), R.part y)

/-- The partition of `s` that agrees with `L` before `x` and with `R` after `x`, and that adjoins
`x` to the part of `L` through `m`. -/
private noncomputable def glue (s : Finset α) (m x : α) (L : Finpartition {y ∈ s | y < x})
    (R : Finpartition {y ∈ s | x < y}) : Finpartition s :=
  open Classical in Finpartition.ofSetSetoid (Setoid.ker (glueKey m x L R)) s

private theorem mem_part_glue {a b : α} :
    b ∈ (glue s m x L R).part a ↔ a ∈ s ∧ b ∈ s ∧ glueKey m x L R a = glueKey m x L R b := by
  rw [glue, Finpartition.mem_part_ofSetSetoid_iff_rel, Setoid.ker_def]

private theorem glueKey_of_lt {y : α} (hy : y < x) :
    glueKey m x L R y = (L.part y, ∅) := by
  rw [glueKey, ite_eq_right hy.ne, R.part_eq_empty.2 fun h => (mem_filter.1 h).2.not_gt hy]

private theorem glueKey_self : glueKey m x L R x = (L.part m, ∅) := by
  rw [glueKey, ite_eq_left rfl, R.part_eq_empty.2 fun h => (mem_filter.1 h).2.false]

private theorem glueKey_of_gt {y : α} (hy : x < y) :
    glueKey m x L R y = (∅, R.part y) := by
  rw [glueKey, ite_eq_right hy.ne', L.part_eq_empty.2 fun h => (mem_filter.1 h).2.not_gt hy]

private theorem glueKey_snd (y : α) : (glueKey m x L R y).2 = R.part y :=
  rfl

/-- The glued partition is noncrossing when its two pieces are. -/
private theorem isNoncrossing_glue (hm : ∀ y ∈ s, m ≤ y) (hL : L.IsNoncrossing)
    (hR : R.IsNoncrossing) : (glue s m x L R).IsNoncrossing := by
  rw [Finpartition.isNoncrossing_iff_part]
  intro a ha b hb c hc d hd hab hbc hcd
  rw [mem_part_glue] at hc hd
  obtain ⟨-, hc, hac⟩ := hc
  obtain ⟨-, hd, hbd⟩ := hd
  refine ((Finpartition.mem_part_iff_part_eq_part _ hb ha).1 ?_).symm
  refine mem_part_glue.2 ⟨ha, hb, ?_⟩
  rcases lt_trichotomy d x with hdx | rfl | hxd
  · -- All four positions lie before `x`, where the glued partition is `L`.
    have hcx := hcd.trans hdx
    have hbx := hbc.trans hcx
    have hax := hab.trans hbx
    simp only [glueKey_of_lt hax, glueKey_of_lt hbx, glueKey_of_lt hcx, glueKey_of_lt hdx,
      Prod.mk.injEq, and_true] at hac hbd ⊢
    exact hL.part_eq_part (mem_filter.2 ⟨ha, hax⟩) (mem_filter.2 ⟨hb, hbx⟩) hac hbd hab hbc hcd
  · -- The last position is `x`, so `b` lies in the part of `m`.
    have hbx := hbc.trans hcd
    have hax := hab.trans hbx
    simp only [glueKey_of_lt hax, glueKey_of_lt hbx, glueKey_of_lt hcd, glueKey_self,
      Prod.mk.injEq, and_true] at hac hbd ⊢
    rw [hbd]
    rcases (hm a ha).eq_or_lt with rfl | hma
    · rfl
    · have hmL := L.part_nonempty.1 (hbd ▸ L.part_nonempty.2 (mem_filter.2 ⟨hb, hbx⟩))
      exact (hL.part_eq_part hmL (mem_filter.2 ⟨ha, hax⟩) hbd.symm hac hma hab hbc).symm
  · -- The last position is after `x`, which forces all four positions after `x`.
    have hgt {y : α} (hy : y ∈ s) (hne : (glueKey m x L R y).2.Nonempty) : x < y := by
      rw [glueKey_snd, R.part_nonempty] at hne
      exact (mem_filter.1 hne).2
    have hbx : x < b := hgt hb <| by
      rw [hbd, glueKey_snd, R.part_nonempty]; exact mem_filter.2 ⟨hd, hxd⟩
    have hcx := hbx.trans hbc
    have hax : x < a := hgt ha <| by
      rw [hac, glueKey_snd, R.part_nonempty]; exact mem_filter.2 ⟨hc, hcx⟩
    simp only [glueKey_of_gt hax, glueKey_of_gt hbx, glueKey_of_gt hcx, glueKey_of_gt hxd,
      Prod.mk.injEq, true_and] at hac hbd ⊢
    exact hR.part_eq_part (mem_filter.2 ⟨ha, hax⟩) (mem_filter.2 ⟨hb, hbx⟩) hac hbd hab hbc hcd

/-- In the glued partition, `x` lies in the part of `m`. -/
private theorem mem_part_glue_self (hms : m ∈ s) (hxs : x ∈ s) (hmx : m ≤ x) :
    x ∈ (glue s m x L R).part m := by
  refine mem_part_glue.2 ⟨hms, hxs, ?_⟩
  rcases hmx.eq_or_lt with rfl | hmx
  · rfl
  · rw [glueKey_self, glueKey_of_lt hmx]

/-- In the glued partition, no position after `x` lies in the part of `m`. -/
private theorem le_of_mem_part_glue (hmx : m ≤ x) {y : α} (hy : y ∈ (glue s m x L R).part m) :
    y ≤ x := by
  obtain ⟨-, hys, h⟩ := mem_part_glue.1 hy
  by_contra! hxy
  have h2 := congrArg Prod.snd h
  rw [glueKey_snd, glueKey_snd, R.part_eq_empty.2 fun h => (mem_filter.1 h).2.not_ge hmx] at h2
  exact (R.part_nonempty.2 (mem_filter.2 ⟨hys, hxy⟩)).ne_empty h2.symm

/-- Restricting the glued partition to a set `t` on which the label of each position is an
injective function `f` of its part in `Q` recovers `Q`. -/
private theorem restrict_glue_eq {t : Finset α} (hts : t ≤ s) {Q : Finpartition t}
    {f : Finset α → Finset α × Finset α} (hf : Function.Injective f)
    (hkey : ∀ y ∈ t, glueKey m x L R y = f (Q.part y)) : (glue s m x L R).restrict hts = Q := by
  refine Finpartition.ext_of_part fun a ha => ?_
  ext b
  rw [Finpartition.part_restrict _ _ ha, mem_inter, mem_part_glue, hkey a ha]
  constructor
  · rintro ⟨⟨-, -, h⟩, hb⟩
    rw [hkey b hb] at h
    rw [hf h]
    exact Q.mem_part_self.2 hb
  · intro hb
    have hb' := Q.part_subset a hb
    exact ⟨⟨hts ha, hts hb', by rw [hkey b hb', (Q.mem_part_iff_part_eq_part hb' ha).1 hb]⟩, hb'⟩

/-- Restricting the glued partition to the positions before `x` recovers `L`. -/
private theorem restrict_glue_lt : (glue s m x L R).restrict (filter_subset _ s) = L :=
  restrict_glue_eq _ (f := (·, ∅)) (fun _ _ h => congrArg Prod.fst h) fun _ hy =>
    glueKey_of_lt (mem_filter.1 hy).2

/-- Restricting the glued partition to the positions after `x` recovers `R`. -/
private theorem restrict_glue_gt : (glue s m x L R).restrict (filter_subset _ s) = R :=
  restrict_glue_eq _ (f := (∅, ·)) (fun _ _ h => congrArg Prod.snd h) fun _ hy =>
    glueKey_of_gt (mem_filter.1 hy).2

end Glue

section Split

variable {P : Finpartition s}

/-- Let `x` be the last position of the part of the first position `m` of a noncrossing partition.
Then no part joins a position at most `x` to a position after `x`. -/
private theorem notMem_part_of_le_of_lt (hP : P.IsNoncrossing) (hm : ∀ y ∈ s, m ≤ y)
    (hxm : x ∈ P.part m) (hmax : ∀ y ∈ P.part m, y ≤ x) {y z : α} (hy : y ∈ s) (hyx : y ≤ x)
    (hxz : x < z) : z ∉ P.part y := by
  intro hz
  have hms : m ∈ s := P.part_nonempty.1 ⟨x, hxm⟩
  by_cases hym : y ∈ P.part m
  · rw [(P.mem_part_iff_part_eq_part hy hms).1 hym] at hz
    exact (hmax z hz).not_gt hxz
  · have hmy : m < y := (hm y hy).lt_of_ne (by rintro rfl; exact hym (P.mem_part_self.2 hy))
    have hyx : y < x := hyx.lt_of_ne (by rintro rfl; exact hym hxm)
    exact hym <| (P.mem_part_iff_part_eq_part hy hms).2
      (Finpartition.isNoncrossing_iff_part.1 hP m hms y hy x hxm z hz hmy hyx hxz).symm

/-- Gluing the restrictions of a noncrossing partition to the positions before and after the last
position `x` of the part of the first position: each label is the pair of traces of a part. -/
private theorem glueKey_restrict (hP : P.IsNoncrossing) (hm : ∀ y ∈ s, m ≤ y)
    (hxm : x ∈ P.part m) (hmax : ∀ y ∈ P.part m, y ≤ x) {y : α} (hy : y ∈ s) :
    glueKey m x (P.restrict (filter_subset (· < x) s)) (P.restrict (filter_subset (x < ·) s)) y =
      (P.part y ∩ {z ∈ s | z < x}, P.part y ∩ {z ∈ s | x < z}) := by
  have hms : m ∈ s := P.part_nonempty.1 ⟨x, hxm⟩
  -- A part through a position at most `x` has no position after `x`.
  have hgt {w : α} (hw : w ∈ s) (hwx : w ≤ x) : P.part w ∩ {z ∈ s | x < z} = ∅ :=
    eq_empty_of_forall_notMem fun z hz => notMem_part_of_le_of_lt hP hm hxm hmax hw hwx
      (mem_filter.1 (mem_inter.1 hz).2).2 (mem_inter.1 hz).1
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · rw [glueKey_of_lt hyx, Finpartition.part_restrict _ _ (mem_filter.2 ⟨hy, hyx⟩),
      hgt hy hyx.le]
  · rw [glueKey_self, hgt hy le_rfl]
    rcases (hm y hy).eq_or_lt with rfl | hmy
    · rw [(P.restrict _).part_eq_empty.2 fun h => (mem_filter.1 h).2.false]
      refine congrArg (·, _) (eq_empty_of_forall_notMem fun z hz => ?_).symm
      obtain ⟨hzs, hzm⟩ := mem_filter.1 (mem_inter.1 hz).2
      exact (hm z hzs).not_gt hzm
    · rw [Finpartition.part_restrict _ _ (mem_filter.2 ⟨hms, hmy⟩),
        (P.mem_part_iff_part_eq_part hy hms).1 hxm]
  · rw [glueKey_of_gt hxy, Finpartition.part_restrict _ _ (mem_filter.2 ⟨hy, hxy⟩)]
    refine congrArg (·, _) (eq_empty_of_forall_notMem fun z hz => ?_).symm
    obtain ⟨hzy, hz⟩ := mem_inter.1 hz
    obtain ⟨hzs, hzx⟩ := mem_filter.1 hz
    exact notMem_part_of_le_of_lt hP hm hxm hmax hzs hzx.le hxy (P.mem_part_comm.1 hzy)

/-- Gluing the restrictions of a noncrossing partition to the positions before and after the last
position `x` of the part of the first position recovers the partition. -/
private theorem glue_restrict (hP : P.IsNoncrossing) (hm : ∀ y ∈ s, m ≤ y) (hxm : x ∈ P.part m)
    (hmax : ∀ y ∈ P.part m, y ≤ x) :
    glue s m x (P.restrict (filter_subset _ s)) (P.restrict (filter_subset _ s)) = P := by
  refine Finpartition.ext_of_part fun a ha => Finset.ext fun b => ?_
  have key {y : α} (hy : y ∈ s) := glueKey_restrict hP hm hxm hmax hy
  -- Every position other than `x` lies in one of the two traces of its part.
  have hself {y : α} (hy : y ∈ s) (hyx : y ≠ x) :
      y ∈ P.part y ∩ {z ∈ s | z < x} ∪ P.part y ∩ {z ∈ s | x < z} := by
    rcases hyx.lt_or_gt with hyx | hxy
    · exact mem_union_left _ (mem_inter.2 ⟨P.mem_part_self.2 hy, mem_filter.2 ⟨hy, hyx⟩⟩)
    · exact mem_union_right _ (mem_inter.2 ⟨P.mem_part_self.2 hy, mem_filter.2 ⟨hy, hxy⟩⟩)
  have hsub (y : α) : P.part y ∩ {z ∈ s | z < x} ∪ P.part y ∩ {z ∈ s | x < z} ⊆ P.part y :=
    union_subset inter_subset_left inter_subset_left
  rw [mem_part_glue]
  constructor
  · rintro ⟨-, hb, h⟩
    rw [key ha, key hb, Prod.mk.injEq] at h
    by_cases hbx : b = x
    · by_cases hax : a = x
      · rw [hax, hbx]
        exact P.mem_part_self.2 (hbx ▸ hb)
      · exact P.mem_part_comm.1 (hsub b (by rw [← h.1, ← h.2]; exact hself ha hax))
    · exact hsub a (by rw [h.1, h.2]; exact hself hb hbx)
  · intro hb
    have hbs := P.part_subset a hb
    refine ⟨ha, hbs, ?_⟩
    rw [key ha, key hbs, (P.mem_part_iff_part_eq_part hbs ha).1 hb]

/-- The last position of the part containing the first position `s.min' hs`. -/
private noncomputable def lastOfFirstPart (hs : s.Nonempty) (P : NoncrossingPartition s) : α :=
  (P.1.part (s.min' hs)).max' (P.1.part_nonempty.2 (s.min'_mem hs))

private theorem lastOfFirstPart_mem (hs : s.Nonempty) (P : NoncrossingPartition s) :
    lastOfFirstPart hs P ∈ P.1.part (s.min' hs) :=
  max'_mem _ _

private theorem le_lastOfFirstPart (hs : s.Nonempty) (P : NoncrossingPartition s) {y : α}
    (hy : y ∈ P.1.part (s.min' hs)) : y ≤ lastOfFirstPart hs P :=
  le_max' _ _ hy

/-- The noncrossing partitions of `s` in which the part of the first position ends at `x` are the
pairs of a noncrossing partition of the positions before `x` and one of the positions after
`x`. -/
private noncomputable def fiberEquiv (hs : s.Nonempty) (hx : x ∈ s) :
    {P : NoncrossingPartition s // lastOfFirstPart hs P = x} ≃
      NoncrossingPartition {y ∈ s | y < x} × NoncrossingPartition {y ∈ s | x < y} where
  toFun P := (⟨P.1.1.restrict (filter_subset _ s), P.1.2.restrict _⟩,
    ⟨P.1.1.restrict (filter_subset _ s), P.1.2.restrict _⟩)
  invFun LR := ⟨⟨glue s (s.min' hs) x LR.1.1 LR.2.1,
      isNoncrossing_glue (fun y hy => s.min'_le y hy) LR.1.2 LR.2.2⟩,
    le_antisymm (max'_le _ _ _ fun _ hy => le_of_mem_part_glue (s.min'_le x hx) hy)
      (le_max' _ _ (mem_part_glue_self (s.min'_mem hs) hx (s.min'_le x hx)))⟩
  left_inv P := by
    obtain ⟨P, rfl⟩ := P
    exact Subtype.ext <| Subtype.ext <| glue_restrict P.2 (fun y hy => s.min'_le y hy)
      (lastOfFirstPart_mem hs P) fun _ hy => le_lastOfFirstPart hs P hy
  right_inv LR := Prod.ext (Subtype.ext restrict_glue_lt) (Subtype.ext restrict_glue_gt)

/-- The first component of `fiberEquiv` is the restriction to the positions before `x`. -/
private theorem coe_fiberEquiv_fst (hs : s.Nonempty) (hx : x ∈ s)
    (P : {P : NoncrossingPartition s // lastOfFirstPart hs P = x}) :
    ((fiberEquiv hs hx P).1 : Finpartition {y ∈ s | y < x}) = P.1.1.restrict (filter_subset _ s) :=
  rfl

/-- The second component of `fiberEquiv` is the restriction to the positions after `x`. -/
private theorem coe_fiberEquiv_snd (hs : s.Nonempty) (hx : x ∈ s)
    (P : {P : NoncrossingPartition s // lastOfFirstPart hs P = x}) :
    ((fiberEquiv hs hx P).2 : Finpartition {y ∈ s | x < y}) = P.1.1.restrict (filter_subset _ s) :=
  rfl

/-- The recurrence of noncrossing partitions by the part containing the first position: the
noncrossing partitions of `s` in which that part ends at `x` correspond to the pairs of a
noncrossing partition of the positions before `x` and one of the positions after `x`. -/
theorem card_eq_sum_card_mul_card (hs : s.Nonempty) :
    Fintype.card (NoncrossingPartition s) = ∑ x ∈ s,
      Fintype.card (NoncrossingPartition {y ∈ s | y < x}) *
        Fintype.card (NoncrossingPartition {y ∈ s | x < y}) := by
  rw [← Finset.card_univ, card_eq_sum_card_fiberwise (f := lastOfFirstPart hs) (t := s)
    fun P _ => P.1.part_subset _ (lastOfFirstPart_mem hs P)]
  refine sum_congr rfl fun x hx => ?_
  rw [← Fintype.card_prod, ← Fintype.card_congr (fiberEquiv hs hx), Fintype.card_subtype]

/-- The noncrossing partitions of a finite set `s` of positions in a linear order are counted by
the Catalan number `catalan #s`. -/
theorem card_eq_catalan (s : Finset α) : Fintype.card (NoncrossingPartition s) = catalan #s := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [← hn, card_empty, catalan_zero, Fintype.card_unique]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (hn ▸ hs.card_pos.ne')
  -- The positions before `x ∈ s`, or after it, are fewer than those of `s`.
  have hlt {x : α} (hx : x ∈ s) {p : α → Prop} [DecidablePred p] (hp : ¬p x) :
      #{y ∈ s | p y} < k + 1 :=
    hn ▸ card_lt_card (filter_ssubset.2 ⟨x, hx, hp⟩)
  have h := sum_card_filter_lt_card_filter_gt s fun i j => catalan i * catalan j
  rw [hn, Nat.add_sub_cancel] at h
  rw [card_eq_sum_card_mul_card hs, catalan_succ, ← sum_range fun i => catalan i * catalan (k - i)]
  refine (sum_congr rfl fun x hx => ?_).trans h
  rw [ih #{y ∈ s | y < x} (hlt hx (lt_irrefl x)) _ rfl,
    ih #{y ∈ s | x < y} (hlt hx (lt_irrefl x)) _ rfl]

/-- There are `catalan n` noncrossing partitions of the `n` ordered positions of `Fin n`. -/
theorem card_fin_eq_catalan (n : ℕ) :
    Fintype.card (NoncrossingPartition (univ : Finset (Fin n))) = catalan n := by
  rw [card_eq_catalan, card_univ, Fintype.card_fin]

end Split

section Pairing

variable {P : Finpartition s}

/-- Let `x` be the last position of the part of the first position `m` of a noncrossing partition.
Then the part of a position after `x` lies after `x`. -/
private theorem part_subset_filter_gt (hP : P.IsNoncrossing) (hm : ∀ y ∈ s, m ≤ y)
    (hxm : x ∈ P.part m) (hmax : ∀ y ∈ P.part m, y ≤ x) {a : α} (hxa : x < a) :
    P.part a ⊆ {y ∈ s | x < y} := fun _ hz =>
  mem_filter.2 ⟨P.part_subset a hz, lt_of_not_ge fun hzx =>
    notMem_part_of_le_of_lt hP hm hxm hmax (P.part_subset a hz) hzx hxa (P.mem_part_comm.1 hz)⟩

/-- Let `x` be the last position of the part of the first position `m` of a noncrossing partition.
Then the part of a position before `x` outside the part of `m` lies strictly between `m` and
`x`. -/
private theorem part_subset_filter_between (hP : P.IsNoncrossing) (hm : ∀ y ∈ s, m ≤ y)
    (hxm : x ∈ P.part m) (hmax : ∀ y ∈ P.part m, y ≤ x) {a : α} (ha : a ∈ s) (hax : a ≤ x)
    (ham : a ∉ P.part m) : P.part a ⊆ {y ∈ {y ∈ s | y < x} | m < y} := by
  have hms : m ∈ s := P.part_nonempty.1 ⟨x, hxm⟩
  intro z hz
  have hzs := P.part_subset a hz
  -- The position `z` is not in the part of `m`, since the part of `a` is not.
  have hzm : z ∉ P.part m := fun h => ham <| by
    rwa [P.mem_part_iff_part_eq_part ha hms, ← (P.mem_part_iff_part_eq_part hzs ha).1 hz,
      ← P.mem_part_iff_part_eq_part hzs hms]
  have hzx : z ≤ x := le_of_not_gt fun hxz => notMem_part_of_le_of_lt hP hm hxm hmax ha hax hxz hz
  refine mem_filter.2 ⟨mem_filter.2 ⟨hzs, hzx.lt_of_ne fun h => hzm (h ▸ hxm)⟩, ?_⟩
  exact (hm z hzs).lt_of_ne fun h => hzm (h ▸ P.mem_part_self.2 hms)

/-- Let `x > m` be the last position of the part of the first position `m` of a noncrossing
partition `P`. Then `P` is a pairing iff `m` is the only position before `x` in its part, and the
restrictions of `P` to the positions strictly between `m` and `x` and to the positions after `x`
are pairings. -/
private theorem isPairing_iff_restrict (hP : P.IsNoncrossing) (hm : ∀ y ∈ s, m ≤ y)
    (hxm : x ∈ P.part m) (hmax : ∀ y ∈ P.part m, y ≤ x) (hmx : m < x) :
    P.IsPairing ↔ (P.part m ∩ {y ∈ s | y < x} = {m} ∧
      ((P.restrict (filter_subset (· < x) s)).restrict (filter_subset (m < ·) _)).IsPairing) ∧
      (P.restrict (filter_subset (x < ·) s)).IsPairing := by
  have hms : m ∈ s := P.part_nonempty.1 ⟨x, hxm⟩
  -- A part inside the positions strictly between `m` and `x` is a part of the restriction there.
  have hbetween {a : α} (ha : a ∈ {y ∈ {y ∈ s | y < x} | m < y}) (ham : a ∉ P.part m) :
      ((P.restrict (filter_subset (· < x) s)).restrict (filter_subset (m < ·) _)).part a =
        P.part a := by
    have hsub := part_subset_filter_between hP hm hxm hmax (mem_filter.1 (mem_filter.1 ha).1).1
      (mem_filter.1 (mem_filter.1 ha).1).2.le ham
    rw [Finpartition.part_restrict _ _ ha, Finpartition.part_restrict _ _ (mem_filter.1 ha).1,
      inter_eq_left.2 (hsub.trans (filter_subset _ _)), inter_eq_left.2 hsub]
  -- A part through a position after `x` is a part of the restriction there.
  have hafter {a : α} (ha : a ∈ {y ∈ s | x < y}) :
      (P.restrict (filter_subset (x < ·) s)).part a = P.part a := by
    rw [Finpartition.part_restrict _ _ ha,
      inter_eq_left.2 (part_subset_filter_gt hP hm hxm hmax (mem_filter.1 ha).2)]
  -- The part of `m` is `{m, x}` iff `m` is its only position before `x`.
  have hpair : P.part m = {m, x} ↔ P.part m ∩ {y ∈ s | y < x} = {m} := by
    refine ⟨fun h => ?_, fun h => Subset.antisymm (fun y hy => ?_) ?_⟩
    · rw [h]
      ext y
      simp only [mem_inter, mem_insert, mem_singleton, mem_filter]
      constructor
      · rintro ⟨rfl | rfl, -, hy⟩
        exacts [rfl, absurd hy (lt_irrefl _)]
      · rintro rfl
        exact ⟨Or.inl rfl, hms, hmx⟩
    · rcases (hmax y hy).lt_or_eq with hyx | rfl
      · exact mem_insert.2 <| Or.inl <| mem_singleton.1 <|
          h ▸ mem_inter.2 ⟨hy, mem_filter.2 ⟨P.part_subset m hy, hyx⟩⟩
      · exact mem_insert.2 <| Or.inr <| mem_singleton_self _
    · exact insert_subset (P.mem_part_self.2 hms) (singleton_subset_iff.2 hxm)
  rw [Finpartition.isPairing_iff_part, Finpartition.isPairing_iff_part,
    Finpartition.isPairing_iff_part, ← hpair]
  constructor
  · intro h
    have hm2 : P.part m = {m, x} :=
      (eq_of_subset_of_card_le (insert_subset (P.mem_part_self.2 hms) (singleton_subset_iff.2 hxm))
        (by rw [h m hms, card_pair hmx.ne])).symm
    -- A position strictly between `m` and `x` is not in the part `{m, x}`.
    have hnot {a : α} (ha : a ∈ {y ∈ {y ∈ s | y < x} | m < y}) : a ∉ P.part m := by
      rw [hm2, mem_insert, mem_singleton]
      rintro (rfl | rfl)
      exacts [lt_irrefl _ (mem_filter.1 ha).2, lt_irrefl _ (mem_filter.1 (mem_filter.1 ha).1).2]
    refine ⟨⟨hm2, fun a ha => ?_⟩, fun a ha => ?_⟩
    · rw [hbetween ha (hnot ha)]
      exact h a (mem_filter.1 (mem_filter.1 ha).1).1
    · rw [hafter ha]
      exact h a (mem_filter.1 ha).1
  · rintro ⟨⟨hm2, hM⟩, hR⟩ a ha
    by_cases ham : a ∈ P.part m
    · rw [(P.mem_part_iff_part_eq_part ha hms).1 ham, hm2, card_pair hmx.ne]
    rcases lt_or_gt_of_ne (show a ≠ x by rintro rfl; exact ham hxm) with hax | hxa
    · have hav : a ∈ {y ∈ {y ∈ s | y < x} | m < y} :=
        mem_filter.2 ⟨mem_filter.2 ⟨ha, hax⟩,
          (hm a ha).lt_of_ne fun h => ham (h ▸ P.mem_part_self.2 hms)⟩
      rw [← hbetween hav ham]
      exact hM a hav
    · rw [← hafter (mem_filter.2 ⟨ha, hxa⟩)]
      exact hR a (mem_filter.2 ⟨ha, hxa⟩)

/-- The last position of the part of the first position `m` is `m` itself exactly when that part
is a singleton. -/
private theorem lastOfFirstPart_eq_iff (hs : s.Nonempty) (hm : s.min' hs = m)
    {P : NoncrossingPartition s} : lastOfFirstPart hs P = m ↔ P.1.part m = {m} := by
  subst hm
  refine ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨P.1.mem_part_self.2 (s.min'_mem hs),
    fun y hy => le_antisymm (h ▸ le_lastOfFirstPart hs P hy)
      (s.min'_le y (P.1.part_subset _ hy))⟩, fun h => ?_⟩
  exact le_antisymm (max'_le _ _ _ fun y hy => (mem_singleton.1 (h ▸ hy)).le)
    (s.min'_le _ (P.1.part_subset _ (lastOfFirstPart_mem hs P)))

/-- For a position `x` after the first position `m` of `s`, the noncrossing pairings of `s` in
which `m` is paired with `x` correspond to the pairs of a noncrossing pairing of the positions
strictly between `m` and `x` and one of the positions after `x`. -/
private theorem card_pairing_fiber (hs : s.Nonempty) (hx : x ∈ s) (hmx : s.min' hs < x) :
    Fintype.card {P : NoncrossingPartition s // lastOfFirstPart hs P = x ∧ P.1.IsPairing} =
      Fintype.card {M : NoncrossingPartition {y ∈ {y ∈ s | y < x} | s.min' hs < y} //
        M.1.IsPairing} *
      Fintype.card {R : NoncrossingPartition {y ∈ s | x < y} // R.1.IsPairing} := by
  set m := s.min' hs
  have hm : ∀ y ∈ s, m ≤ y := fun y hy => s.min'_le y hy
  have hmt : m ∈ {y ∈ s | y < x} := mem_filter.2 ⟨s.min'_mem hs, hmx⟩
  have ht : ({y ∈ s | y < x}).Nonempty := ⟨m, hmt⟩
  have hmin : ({y ∈ s | y < x}).min' ht = m :=
    le_antisymm (min'_le _ _ hmt) (le_min' _ _ _ fun y hy => hm y (mem_filter.1 hy).1)
  -- No position of `s` comes before `m`.
  have : Unique (NoncrossingPartition {y ∈ {y ∈ s | y < x} | y < m}) :=
    { default := ⊥
      uniq := eq_bot_of_eq_empty <| filter_eq_empty_iff.2 fun y hy =>
        not_lt.2 (hm y (mem_filter.1 hy).1) }
  -- Splitting at `x` and then splitting the positions before `x` at `m`.
  let e : {L : NoncrossingPartition {y ∈ s | y < x} //
      lastOfFirstPart ht L = m ∧ (L.1.restrict (filter_subset (m < ·) _)).IsPairing} ≃
      {M : NoncrossingPartition {y ∈ {y ∈ s | y < x} | m < y} // M.1.IsPairing} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans <|
      ((fiberEquiv ht hmt).subtypeEquiv (q := fun AM => AM.2.1.IsPairing) fun _ => by
        rw [coe_fiberEquiv_snd]).trans <|
      ((Equiv.prodComm _ _).subtypeEquiv fun _ => Iff.rfl).trans <|
      (Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun M : NoncrossingPartition {y ∈ {y ∈ s | y < x} | m < y} => M.1.IsPairing)).trans
        (Equiv.prodUnique _ _)
  refine Fintype.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans <|
    ((fiberEquiv hs hx).subtypeEquiv fun P => ?_).trans <|
    Equiv.subtypeProdEquivProd.trans (e.prodCongr (Equiv.refl _))) |>.trans (Fintype.card_prod _ _)
  obtain ⟨P, hPx⟩ := P
  have hxm : x ∈ P.1.part m := hPx ▸ lastOfFirstPart_mem hs P
  rw [isPairing_iff_restrict P.2 hm hxm (fun y hy => hPx ▸ le_lastOfFirstPart hs P hy) hmx,
    ← Finpartition.part_restrict _ (filter_subset (· < x) s) hmt, lastOfFirstPart_eq_iff ht hmin,
    coe_fiberEquiv_fst, coe_fiberEquiv_snd]

/-- The recurrence of noncrossing pairings by the partner of the first position `m`: the
noncrossing pairings of `s` in which `m` is paired with `x` correspond to the pairs of a
noncrossing pairing of the positions strictly between `m` and `x` and one of the positions after
`x`. -/
theorem card_isPairing_eq_sum (hs : s.Nonempty) :
    Fintype.card {P : NoncrossingPartition s // P.1.IsPairing} =
      ∑ x ∈ s with s.min' hs < x,
        Fintype.card {M : NoncrossingPartition {y ∈ s | s.min' hs < y ∧ y < x} //
          M.1.IsPairing} *
        Fintype.card {R : NoncrossingPartition {y ∈ s | x < y} // R.1.IsPairing} := by
  rw [Fintype.card_subtype, card_eq_sum_card_fiberwise (f := lastOfFirstPart hs) (t := s)
    fun P _ => P.1.part_subset _ (lastOfFirstPart_mem hs P), sum_filter]
  refine sum_congr rfl fun x hx => ?_
  split_ifs with hmx
  · have hv : {y ∈ {y ∈ s | y < x} | s.min' hs < y} = {y ∈ s | s.min' hs < y ∧ y < x} := by
      ext y
      simp only [mem_filter]
      tauto
    rw [filter_filter, ← Fintype.card_subtype, ← hv, ← card_pairing_fiber hs hx hmx]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
  -- If the part of the first position ends there, it is a singleton, not a pair.
  · refine card_eq_zero.2 <| filter_eq_empty_iff.2 fun P hP hPx => ?_
    have h := (mem_filter.1 hP).2
    have hxm : x = s.min' hs := le_antisymm (not_lt.1 hmx) (s.min'_le x hx)
    have h1 := (lastOfFirstPart_eq_iff hs rfl).1 (hPx.trans hxm)
    have h2 := Finpartition.isPairing_iff_part.1 h (s.min' hs) (s.min'_mem hs)
    rw [h1, card_singleton] at h2
    exact absurd h2 (by decide)

/-- A finite set of odd size has no noncrossing pairing. -/
theorem card_isPairing_eq_zero (hs : Odd #s) :
    Fintype.card {P : NoncrossingPartition s // P.1.IsPairing} = 0 :=
  Fintype.card_eq_zero_iff.2 ⟨fun P => Nat.not_even_iff_odd.2 hs P.2.even_card⟩

/-- The noncrossing pairings of a finite set of `2 * n` positions in a linear order are counted by
the Catalan number `catalan n`. -/
theorem card_isPairing_eq_catalan {n : ℕ} (hn : #s = 2 * n) :
    Fintype.card {P : NoncrossingPartition s // P.1.IsPairing} = catalan n := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  rcases n with _ | k
  · -- The empty set has a single partition, with no parts, and it is a pairing.
    have hs : s = ⊥ := card_eq_zero.1 hn
    rw [catalan_zero, Fintype.card_eq_one_iff]
    refine ⟨⟨⊥, Finpartition.isPairing_iff.2 fun B hB => ?_⟩,
      fun P => Subtype.ext (eq_bot_of_eq_empty hs _)⟩
    rw [Finpartition.parts_eq_empty_iff.2 hs] at hB
    exact absurd hB (notMem_empty B)
  have hs : s.Nonempty := card_pos.1 (by omega)
  -- The number of noncrossing pairings of a smaller set depends only on its size.
  let g (i : ℕ) : ℕ := if Even i then catalan (i / 2) else 0
  have hg {t : Finset α} (ht : #t < 2 * k + 1) :
      Fintype.card {P : NoncrossingPartition t // P.1.IsPairing} = g #t := by
    by_cases he : Even #t
    · obtain ⟨j, hj⟩ := he
      rw [ih j (by omega) (by omega)]
      simp only [g, hj, show Even (j + j) from ⟨j, rfl⟩, ↓reduceIte]
      congr 1
      omega
    · rw [card_isPairing_eq_zero (Nat.not_even_iff_odd.1 he)]
      simp only [g, he, ↓reduceIte]
  -- Reindex the recurrence by the positions after the first position `m`.
  set w := {x ∈ s | s.min' hs < x} with hw_def
  have hw : #w = 2 * k + 1 := by
    have : w = s.erase (s.min' hs) := by
      ext y
      simp only [hw_def, mem_filter, mem_erase]
      exact ⟨fun h => ⟨h.2.ne', h.1⟩, fun h => ⟨h.2, (s.min'_le y h.2).lt_of_ne' h.1⟩⟩
    rw [this, card_erase_of_mem (s.min'_mem hs), hn]
    omega
  have hlt {x : α} (hx : x ∈ w) {p : α → Prop} [DecidablePred p] (hp : ¬p x) :
      #{y ∈ w | p y} < 2 * k + 1 :=
    hw ▸ card_lt_card (filter_ssubset.2 ⟨x, hx, hp⟩)
  have h := sum_card_filter_lt_card_filter_gt w fun i j => g i * g j
  rw [hw, Nat.add_sub_cancel, sum_range_two_mul_add_one] at h
  rw [card_isPairing_eq_sum hs, catalan_succ, ← sum_range fun i => catalan i * catalan (k - i)]
  refine (sum_congr rfl fun x hx => ?_).trans (h.trans ?_)
  · -- The positions between `m` and `x`, or after `x`, are those of `w` before or after `x`.
    have hmx := (mem_filter.1 hx).2
    have hu : {y ∈ s | x < y} = {y ∈ w | x < y} := by
      rw [hw_def, filter_filter]
      exact filter_congr fun y _ => ⟨fun h => ⟨hmx.trans h, h⟩, And.right⟩
    have hv : {y ∈ s | s.min' hs < y ∧ y < x} = {y ∈ w | y < x} := by
      rw [hw_def, filter_filter]
    rw [hu, hv, hg (hlt hx (p := (· < x)) (lt_irrefl x)), hg (hlt hx (p := (x < ·)) (lt_irrefl x))]
  -- Only the even sizes contribute.
  have hodd : ∑ j ∈ range k, g (2 * j + 1) * g (2 * k - (2 * j + 1)) = 0 :=
    sum_eq_zero fun j _ => by simp only [g, Nat.not_even_two_mul_add_one, ↓reduceIte, zero_mul]
  rw [hodd, add_zero]
  refine sum_congr rfl fun j hj => ?_
  have hjk := mem_range_succ_iff.1 hj
  rw [show 2 * k - 2 * j = 2 * (k - j) by omega]
  simp [g]

/-- There are `catalan n` noncrossing pairings of the `2 * n` ordered positions of `Fin (2 * n)`.
-/
theorem card_isPairing_fin_eq_catalan (n : ℕ) :
    Fintype.card {P : NoncrossingPartition (univ : Finset (Fin (2 * n))) // P.1.IsPairing} =
      catalan n :=
  card_isPairing_eq_catalan (by rw [card_univ, Fintype.card_fin])

end Pairing

end TauCeti.NoncrossingPartition
