/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import TauCeti.Combinatorics.NoncrossingPartition.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max

/-!
# Noncrossing partitions are counted by the Catalan numbers

Let `s` be a nonempty finite set of positions in a linear order, with first position `m`. For a
noncrossing partition `P` of `s`, let `x` be the last position of the part of `P` containing `m`.
No part of `P` then joins a position before `x` to a position after `x`, so `P` is the same as a
noncrossing partition of the positions of `s` before `x` (with `x` adjoined to the part of `m`)
together with an arbitrary noncrossing partition of the positions of `s` after `x`. This is the
recurrence of noncrossing partitions by the part containing the first position, and it is the
recurrence of the Catalan numbers; hence there are `catalan n` noncrossing partitions of `n`
ordered positions.

## Main results

* `TauCeti.NoncrossingPartition.card_eq_sum_card_mul_card` — the recurrence by the part containing
  the first position: `|NC(s)| = ∑_{x ∈ s} |NC(s_{<x})| |NC(s_{>x})|`.
* `TauCeti.NoncrossingPartition.card_eq_catalan` — `|NC(s)| = catalan |s|`.
* `TauCeti.NoncrossingPartition.card_fin_eq_catalan` — `|NC(n)| = catalan n` for the positions
  of `Fin n`.

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
  -- The positions before and after `x ∈ s` are the `k` positions of `s` other than `x`.
  have hcard {x : α} (hx : x ∈ s) : #{y ∈ s | y < x} + #{y ∈ s | x < y} = k := by
    have : {y ∈ s | ¬y < x}.erase x = {y ∈ s | x < y} := by
      ext y; simp only [mem_erase, mem_filter, not_lt]; grind
    have h1 := card_erase_add_one (s := {y ∈ s | ¬y < x}) (mem_filter.2 ⟨hx, lt_irrefl x⟩)
    have h2 := card_filter_add_card_filter_not (s := s) (· < x)
    rw [this] at h1
    omega
  have hlt {x : α} (hx : x ∈ s) : #{y ∈ s | y < x} < k + 1 := by
    have := hcard hx; omega
  have hgt {x : α} (hx : x ∈ s) : #{y ∈ s | x < y} < k + 1 := by
    have := hcard hx; omega
  rw [card_eq_sum_card_mul_card hs, catalan_succ, ← sum_range fun i => catalan i * catalan (k - i)]
  -- Reindex by the number of positions before `x`, which is strictly increasing in `x`.
  have hinj : Set.InjOn (fun x => #{y ∈ s | y < x}) s :=
    StrictMonoOn.injOn fun x hx x' hx' hxx' => card_lt_card <|
      (ssubset_iff_of_subset fun y hy =>
        mem_filter.2 ⟨(mem_filter.1 hy).1, (mem_filter.1 hy).2.trans hxx'⟩).2
        ⟨x, mem_filter.2 ⟨hx, hxx'⟩, fun h => lt_irrefl x (mem_filter.1 h).2⟩
  have himage : s.image (fun x => #{y ∈ s | y < x}) = range (k + 1) :=
    eq_of_subset_of_card_le (fun i hi => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
        exact mem_range.2 (hlt hx))
      (by rw [card_range, card_image_of_injOn hinj, hn])
  rw [← himage, sum_image hinj]
  refine sum_congr rfl fun x hx => ?_
  rw [ih _ (hlt hx) _ rfl, ih _ (hgt hx) _ rfl, ← hcard hx, Nat.add_sub_cancel_left]

/-- There are `catalan n` noncrossing partitions of the `n` ordered positions of `Fin n`. -/
theorem card_fin_eq_catalan (n : ℕ) :
    Fintype.card (NoncrossingPartition (univ : Finset (Fin n))) = catalan n := by
  rw [card_eq_catalan, card_univ, Fintype.card_fin]

end Split

end TauCeti.NoncrossingPartition
