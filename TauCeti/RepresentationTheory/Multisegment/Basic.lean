/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Multiset.Filter
public import TauCeti.Order.Interval.NonemptyInterval

/-!
# Integer multisegments, degree dimensions, right truncation, and occurrence labels

An integer segment `[b, e]` is a nonempty closed integer interval `NonemptyInterval ℤ` ordered by
set inclusion (`s ≤ t ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd`), and an integer multisegment
`TauCeti.Multisegment` is a finite multiset of such segments in which repeated segments remain
distinct occurrences.

This file develops the multisegment combinatorics underlying graded nilpotent operators on type-A
windows and the Zelevinsky–Atobe–Kondo–Yasuda multisegment operations:

* `TauCeti.Multisegment.degreeDimension`, `TauCeti.Multisegment.degreeSupport`, and
  `TauCeti.Multisegment.totalLength` record the multiplicity of segments covering each integer
  grade, the finite set of supported grades, and the total basis dimension
  `∑ s ∈ m, #s.toFinset`, linked by double counting (`sum_degreeSupport_degreeDimension`).
* `TauCeti.Multisegment.shift` translates every occurrence on the right by an integer `c`,
  preserving multiplicities and total length while reindexing degree dimensions.
* `TauCeti.Multisegment.rightTruncate` applies `NonemptyInterval.shorten` (mapping `[b, e]` to
  `some [b, e - 1]` when `b < e` and deleting singletons `[b, b]` to `none`) to every occurrence via
  `Multiset.filterMap`, satisfying `(rightTruncate m).count t = m.count t.extendRight` and lowering
  `totalLength m` by `m.card`.
* `TauCeti.Multisegment.occurrenceInterval` indexes the `m.card` occurrences of `m` by
  `Fin m.card` with value multiset `m`, preserving occurrence counts under index permutations.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24 (§§2.1, 2.3, 3.1).
* C. Mœglin, J.-L. Waldspurger, *Sur l'involution de Zelevinski*, J. reine angew. Math. 372 (1986),
  136–177 (§II.1).
-/

public section

open Finset Function

namespace TauCeti

/-- A finite multisegment of nonempty closed integer intervals; repeated intervals remain distinct
occurrences. -/
abbrev Multisegment := Multiset (NonemptyInterval ℤ)

namespace Multisegment

/-- Nonempty closed integer intervals `[b, e]` serving as segments of an integer multisegment. -/
abbrev Interval := NonemptyInterval ℤ

section DegreeAndLength

/-- Number of occurrences in `m` whose closed interval contains the integer grade `a`. -/
def degreeDimension (m : Multisegment) (a : ℤ) : ℕ :=
  m.countP fun s => a ∈ s

theorem degreeDimension_def (m : Multisegment) (a : ℤ) :
    degreeDimension m a = m.countP fun s => a ∈ s :=
  (rfl)

@[simp]
theorem degreeDimension_zero (a : ℤ) : degreeDimension 0 a = 0 :=
  Multiset.countP_zero _

@[simp]
theorem degreeDimension_cons (s : Interval) (m : Multisegment) (a : ℤ) :
    degreeDimension (s ::ₘ m) a = degreeDimension m a + if a ∈ s then 1 else 0 := by
  rw [degreeDimension_def, Multiset.countP_cons, degreeDimension_def]

@[simp]
theorem degreeDimension_singleton (s : Interval) (a : ℤ) :
    degreeDimension {s} a = if a ∈ s then 1 else 0 := by
  rw [← Multiset.cons_zero, degreeDimension_cons, degreeDimension_zero, zero_add]

@[simp]
theorem degreeDimension_add (m₁ m₂ : Multisegment) (a : ℤ) :
    degreeDimension (m₁ + m₂) a = degreeDimension m₁ a + degreeDimension m₂ a :=
  Multiset.countP_add _ m₁ m₂

theorem degreeDimension_sub {m₁ m₂ : Multisegment} (h : m₂ ≤ m₁) (a : ℤ) :
    degreeDimension (m₁ - m₂) a = degreeDimension m₁ a - degreeDimension m₂ a :=
  Multiset.countP_sub h _

theorem degreeDimension_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) (a : ℤ) :
    degreeDimension m₁ a ≤ degreeDimension m₂ a :=
  Multiset.countP_le_of_le _ h

theorem degreeDimension_le_card (m : Multisegment) (a : ℤ) :
    degreeDimension m a ≤ m.card :=
  Multiset.countP_le_card _ m

@[simp]
theorem degreeDimension_pos_iff {m : Multisegment} {a : ℤ} :
    0 < degreeDimension m a ↔ ∃ s ∈ m, a ∈ s := by
  rw [degreeDimension_def, Multiset.countP_pos]

@[simp]
theorem degreeDimension_eq_zero_iff {m : Multisegment} {a : ℤ} :
    degreeDimension m a = 0 ↔ ∀ s ∈ m, a ∉ s := by
  rw [degreeDimension_def, Multiset.countP_eq_zero]

/-- The finite set of integer grades covered by at least one segment of `m`. -/
def degreeSupport (m : Multisegment) : Finset ℤ :=
  m.toFinset.biUnion NonemptyInterval.toFinset

theorem degreeSupport_def (m : Multisegment) :
    degreeSupport m = m.toFinset.biUnion NonemptyInterval.toFinset :=
  (rfl)

@[simp]
theorem mem_degreeSupport_iff {m : Multisegment} {a : ℤ} :
    a ∈ degreeSupport m ↔ ∃ s ∈ m, a ∈ s := by
  simp [degreeSupport]

@[simp]
theorem degreeSupport_zero : degreeSupport 0 = ∅ := by
  simp [degreeSupport]

@[simp]
theorem degreeSupport_singleton (s : Interval) : degreeSupport {s} = s.toFinset := by
  simp [degreeSupport]

@[simp]
theorem degreeSupport_cons (s : Interval) (m : Multisegment) :
    degreeSupport (s ::ₘ m) = s.toFinset ∪ degreeSupport m := by
  ext a
  simp [or_and_right, exists_or]

@[simp]
theorem degreeSupport_add (m₁ m₂ : Multisegment) :
    degreeSupport (m₁ + m₂) = degreeSupport m₁ ∪ degreeSupport m₂ := by
  ext a
  simp [or_and_right, exists_or]

theorem degreeSupport_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) :
    degreeSupport m₁ ⊆ degreeSupport m₂ := by
  intro a ha
  rcases mem_degreeSupport_iff.mp ha with ⟨s, hs, has⟩
  exact mem_degreeSupport_iff.mpr ⟨s, Multiset.mem_of_le h hs, has⟩

theorem degreeDimension_eq_zero_of_notMem_degreeSupport {m : Multisegment} {a : ℤ}
    (ha : a ∉ degreeSupport m) : degreeDimension m a = 0 := by
  rw [degreeDimension_eq_zero_iff]
  intro s hs has
  exact ha (mem_degreeSupport_iff.mpr ⟨s, hs, has⟩)

/-- Total point count `∑ s ∈ m, #s.toFinset` of a multisegment, counting each occurrence with its
full multiplicity. -/
def totalLength (m : Multisegment) : ℕ :=
  (m.map fun s => #s.toFinset).sum

theorem totalLength_def (m : Multisegment) :
    totalLength m = (m.map fun s => #s.toFinset).sum :=
  (rfl)

@[simp]
theorem totalLength_zero : totalLength 0 = 0 := by
  simp [totalLength_def]

@[simp]
theorem totalLength_singleton (s : Interval) : totalLength {s} = #s.toFinset := by
  simp [totalLength_def]

@[simp]
theorem totalLength_cons (s : Interval) (m : Multisegment) :
    totalLength (s ::ₘ m) = #s.toFinset + totalLength m := by
  simp [totalLength_def]

@[simp]
theorem totalLength_add (m₁ m₂ : Multisegment) :
    totalLength (m₁ + m₂) = totalLength m₁ + totalLength m₂ := by
  simp [totalLength_def]

theorem totalLength_sub {m₁ m₂ : Multisegment} (h : m₂ ≤ m₁) :
    totalLength (m₁ - m₂) = totalLength m₁ - totalLength m₂ := by
  have key := totalLength_add (m₁ - m₂) m₂
  rw [Multiset.sub_add_cancel h] at key
  omega

theorem totalLength_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) :
    totalLength m₁ ≤ totalLength m₂ := by
  have key := totalLength_add (m₂ - m₁) m₁
  rw [Multiset.sub_add_cancel h] at key
  omega

theorem card_le_totalLength (m : Multisegment) : m.card ≤ totalLength m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    have hs := s.card_toFinset_pos
    rw [Multiset.card_cons, totalLength_cons]
    omega

@[simp]
theorem totalLength_eq_zero_iff {m : Multisegment} : totalLength m = 0 ↔ m = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hcard := card_le_totalLength m
  rw [h, Nat.le_zero, Multiset.card_eq_zero] at hcard
  exact hcard

@[simp]
theorem totalLength_pos_iff {m : Multisegment} : 0 < totalLength m ↔ m ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, totalLength_eq_zero_iff]

/-- Summing `degreeDimension m` over any finite set of grades containing `degreeSupport m` yields
`totalLength m`. -/
theorem sum_degreeDimension_of_subset {m : Multisegment} {S : Finset ℤ}
    (hS : degreeSupport m ⊆ S) :
    ∑ a ∈ S, degreeDimension m a = totalLength m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    rw [degreeSupport_cons, Finset.union_subset_iff] at hS
    have hfilter : (S.filter fun a => a ∈ s) = s.toFinset := by
      ext a
      simp only [Finset.mem_filter, NonemptyInterval.mem_toFinset, and_iff_right_iff_imp]
      intro has
      exact hS.1 (NonemptyInterval.mem_toFinset.mpr has)
    have hsum : ∑ a ∈ S, (if a ∈ s then 1 else 0) = #s.toFinset := by
      rw [← Finset.sum_filter, hfilter]
      simp
    simp only [degreeDimension_cons, Finset.sum_add_distrib, ih hS.2, hsum, totalLength_cons,
      add_comm]

/-- Double counting: the total length of a multisegment equals the sum of its degree dimensions over
its finite degree support. -/
@[simp]
theorem sum_degreeSupport_degreeDimension (m : Multisegment) :
    ∑ a ∈ degreeSupport m, degreeDimension m a = totalLength m :=
  sum_degreeDimension_of_subset Subset.rfl

end DegreeAndLength

section Shift

/-- Translate every segment occurrence of `m` on the right by `c`. -/
def shift (m : Multisegment) (c : ℤ) : Multisegment :=
  m.map fun s => s.shift c

theorem shift_def (m : Multisegment) (c : ℤ) :
    shift m c = m.map fun s => s.shift c :=
  (rfl)

@[simp]
theorem shift_zero_left (c : ℤ) : shift 0 c = 0 :=
  Multiset.map_zero _

@[simp]
theorem shift_singleton (s : Interval) (c : ℤ) : shift {s} c = {s.shift c} :=
  Multiset.map_singleton _ s

@[simp]
theorem shift_cons (s : Interval) (m : Multisegment) (c : ℤ) :
    shift (s ::ₘ m) c = s.shift c ::ₘ shift m c :=
  Multiset.map_cons _ s m

@[simp]
theorem shift_add (m₁ m₂ : Multisegment) (c : ℤ) :
    shift (m₁ + m₂) c = shift m₁ c + shift m₂ c :=
  Multiset.map_add _ m₁ m₂

@[simp]
theorem shift_zero_right (m : Multisegment) : shift m 0 = m := by
  simp [shift_def]

theorem shift_shift (m : Multisegment) (c d : ℤ) :
    shift (shift m c) d = shift m (c + d) := by
  simp [shift_def, NonemptyInterval.shift_shift]

@[simp]
theorem shift_neg_cancel_right (m : Multisegment) (c : ℤ) :
    shift (shift m c) (-c) = m := by
  rw [shift_shift, add_neg_cancel, shift_zero_right]

@[simp]
theorem neg_shift_cancel_right (m : Multisegment) (c : ℤ) :
    shift (shift m (-c)) c = m := by
  rw [shift_shift, neg_add_cancel, shift_zero_right]

@[simp]
theorem card_shift (m : Multisegment) (c : ℤ) : (shift m c).card = m.card :=
  Multiset.card_map _ m

theorem count_shift (m : Multisegment) (c : ℤ) (s : Interval) :
    (shift m c).count s = m.count (s.shift (-c)) := by
  have hs : s = (s.shift (-c)).shift c := (s.neg_shift_cancel_right c).symm
  conv_lhs => rw [hs]
  exact Multiset.count_map_eq_count' (fun t : Interval => t.shift c) m
    (NonemptyInterval.shift_injective c) (s.shift (-c))

@[simp]
theorem count_shift_shift (m : Multisegment) (c : ℤ) (s : Interval) :
    (shift m c).count (s.shift c) = m.count s :=
  Multiset.count_map_eq_count' (fun t : Interval => t.shift c) m
    (NonemptyInterval.shift_injective c) s

theorem mem_shift_iff {m : Multisegment} {c : ℤ} {s : Interval} :
    s ∈ shift m c ↔ s.shift (-c) ∈ m := by
  rw [← Multiset.count_pos, count_shift, Multiset.count_pos]

@[simp]
theorem shift_mem_shift_iff {m : Multisegment} {c : ℤ} {s : Interval} :
    s.shift c ∈ shift m c ↔ s ∈ m := by
  rw [mem_shift_iff, NonemptyInterval.shift_neg_cancel_right]

@[simp]
theorem shift_sub (m₁ m₂ : Multisegment) (c : ℤ) :
    shift (m₁ - m₂) c = shift m₁ c - shift m₂ c := by
  ext s
  simp [count_shift]

theorem shift_injective (c : ℤ) : Injective fun m : Multisegment => shift m c :=
  Multiset.map_injective (NonemptyInterval.shift_injective c)

@[simp]
theorem shift_inj {m₁ m₂ : Multisegment} {c : ℤ} :
    shift m₁ c = shift m₂ c ↔ m₁ = m₂ :=
  (shift_injective c).eq_iff

@[simp]
theorem totalLength_shift (m : Multisegment) (c : ℤ) :
    totalLength (shift m c) = totalLength m := by
  simp [totalLength_def, shift_def]

theorem degreeDimension_shift (m : Multisegment) (c a : ℤ) :
    degreeDimension (shift m c) a = degreeDimension m (a - c) := by
  rw [degreeDimension_def, shift_def, Multiset.countP_map, degreeDimension_def,
    Multiset.countP_eq_card_filter]
  congr 1
  exact Multiset.filter_congr fun _ _ => NonemptyInterval.mem_shift_iff

@[simp]
theorem degreeDimension_shift_add (m : Multisegment) (c a : ℤ) :
    degreeDimension (shift m c) (a + c) = degreeDimension m a := by
  rw [degreeDimension_shift, add_sub_cancel_right]

end Shift

section RightTruncate

/-- Shorten every segment occurrence of `m` on the right and delete singleton occurrences. -/
def rightTruncate (m : Multisegment) : Multisegment :=
  m.filterMap NonemptyInterval.shorten

theorem rightTruncate_def (m : Multisegment) :
    rightTruncate m = m.filterMap NonemptyInterval.shorten :=
  (rfl)

@[simp]
theorem rightTruncate_zero : rightTruncate 0 = 0 :=
  Multiset.filterMap_zero _

theorem rightTruncate_cons_of_shorten_eq_none {s : Interval} (m : Multisegment)
    (hs : s.shorten = none) :
    rightTruncate (s ::ₘ m) = rightTruncate m :=
  Multiset.filterMap_cons_none s m hs

theorem rightTruncate_cons_of_shorten_eq_some {s t : Interval} (m : Multisegment)
    (hs : s.shorten = some t) :
    rightTruncate (s ::ₘ m) = t ::ₘ rightTruncate m :=
  Multiset.filterMap_cons_some NonemptyInterval.shorten s m hs

theorem rightTruncate_cons (s : Interval) (m : Multisegment) :
    rightTruncate (s ::ₘ m) = match s.shorten with
      | none => rightTruncate m
      | some t => t ::ₘ rightTruncate m := by
  cases hs : s.shorten with
  | none => exact rightTruncate_cons_of_shorten_eq_none m hs
  | some t => exact rightTruncate_cons_of_shorten_eq_some m hs

@[simp]
theorem rightTruncate_singleton_extendRight (s : Interval) :
    rightTruncate {s.extendRight} = {s} := by
  rw [← Multiset.cons_zero,
    rightTruncate_cons_of_shorten_eq_some 0 s.shorten_extendRight,
    rightTruncate_zero, Multiset.cons_zero]

@[simp]
theorem rightTruncate_singleton_pure (a : ℤ) :
    rightTruncate {NonemptyInterval.pure a} = 0 := by
  rw [← Multiset.cons_zero,
    rightTruncate_cons_of_shorten_eq_none 0 (NonemptyInterval.shorten_pure a),
    rightTruncate_zero]

@[simp]
theorem rightTruncate_add (m₁ m₂ : Multisegment) :
    rightTruncate (m₁ + m₂) = rightTruncate m₁ + rightTruncate m₂ :=
  Multiset.filterMap_add NonemptyInterval.shorten m₁ m₂

/-- The multiplicity of `t` in `rightTruncate m` equals the multiplicity of `t.extendRight` in
`m`. -/
@[simp]
theorem count_rightTruncate (m : Multisegment) (t : Interval) :
    (rightTruncate m).count t = m.count t.extendRight := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    cases hs : s.shorten with
    | none =>
      have hne : t.extendRight ≠ s := by
        rintro rfl
        simp at hs
      rw [rightTruncate_cons_of_shorten_eq_none m hs, ih, Multiset.count_cons_of_ne hne]
    | some u =>
      have hsu : s = u.extendRight := NonemptyInterval.shorten_eq_some_iff.mp hs
      subst hsu
      rw [rightTruncate_cons_of_shorten_eq_some m u.shorten_extendRight]
      simp [ih, Multiset.count_cons]

@[simp]
theorem mem_rightTruncate_iff {m : Multisegment} {t : Interval} :
    t ∈ rightTruncate m ↔ t.extendRight ∈ m := by
  rw [← Multiset.count_pos, count_rightTruncate, Multiset.count_pos]

@[simp]
theorem rightTruncate_sub (m₁ m₂ : Multisegment) :
    rightTruncate (m₁ - m₂) = rightTruncate m₁ - rightTruncate m₂ := by
  ext t
  simp [Multiset.count_sub]

theorem rightTruncate_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) :
    rightTruncate m₁ ≤ rightTruncate m₂ :=
  Multiset.filterMap_le_filterMap NonemptyInterval.shorten h

/-- Right truncation commutes with every integer translation. -/
theorem rightTruncate_shift (m : Multisegment) (c : ℤ) :
    rightTruncate (shift m c) = shift (rightTruncate m) c := by
  ext t
  rw [count_rightTruncate, count_shift, count_shift, count_rightTruncate,
    NonemptyInterval.extendRight_shift]

theorem card_rightTruncate_le (m : Multisegment) :
    (rightTruncate m).card ≤ m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    cases hs : s.shorten with
    | none =>
      rw [rightTruncate_cons_of_shorten_eq_none m hs, Multiset.card_cons]
      omega
    | some t =>
      rw [rightTruncate_cons_of_shorten_eq_some m hs, Multiset.card_cons, Multiset.card_cons]
      omega

/-- Right truncation decreases `totalLength` by `m.card`: every singleton contributes `1` to
`totalLength m` and disappears, while every nonsingleton loses one point. -/
theorem totalLength_rightTruncate_add_card (m : Multisegment) :
    totalLength (rightTruncate m) + m.card = totalLength m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    cases hs : s.shorten with
    | none =>
      have hcard : #s.toFinset = 1 :=
        s.card_toFinset_eq_one_iff.mpr (NonemptyInterval.shorten_eq_none_iff.mp hs)
      rw [rightTruncate_cons_of_shorten_eq_none m hs, Multiset.card_cons, totalLength_cons]
      omega
    | some t =>
      have hcard := NonemptyInterval.card_toFinset_of_shorten_eq_some hs
      rw [rightTruncate_cons_of_shorten_eq_some m hs, Multiset.card_cons, totalLength_cons,
        totalLength_cons]
      omega

theorem totalLength_rightTruncate_eq_sub (m : Multisegment) :
    totalLength (rightTruncate m) = totalLength m - m.card := by
  have key := totalLength_rightTruncate_add_card m
  omega

/-- For every nonempty multisegment `m`, right truncation strictly decreases `totalLength`. -/
theorem totalLength_rightTruncate_lt {m : Multisegment} (hm : m ≠ 0) :
    totalLength (rightTruncate m) < totalLength m := by
  have hcard : 0 < m.card := Multiset.card_pos.mpr hm
  have key := totalLength_rightTruncate_add_card m
  omega

end RightTruncate

section OccurrenceInterval

/-- Canonical indexing of the `m.card` occurrences of `m` by `Fin m.card`, read off from
`m.toList`. -/
noncomputable def occurrenceInterval (m : Multisegment) (i : Fin m.card) : Interval :=
  m.toList[i.val]'(by simp)

/-- Listing `occurrenceInterval m` across `Fin m.card` recovers `m.toList`. -/
@[simp]
theorem ofFn_occurrenceInterval (m : Multisegment) :
    List.ofFn (occurrenceInterval m) = m.toList := by
  have hlen : m.toList.length = m.card := Multiset.length_toList m
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi₁ hi₂
    simp [occurrenceInterval]

/-- Mapping `occurrenceInterval m` over all `Fin m.card` indices recovers the multiset `m` with full
multiplicities. -/
theorem map_univ_occurrenceInterval (m : Multisegment) :
    (Finset.univ : Finset (Fin m.card)).val.map (occurrenceInterval m) = m := by
  simp

@[simp]
theorem image_univ_occurrenceInterval (m : Multisegment) :
    (Finset.univ : Finset (Fin m.card)).image (occurrenceInterval m) = m.toFinset := by
  rw [Finset.image, map_univ_occurrenceInterval]

@[simp]
theorem occurrenceInterval_mem (m : Multisegment) (i : Fin m.card) :
    occurrenceInterval m i ∈ m := by
  have h := Multiset.mem_map_of_mem (occurrenceInterval m)
    (Finset.mem_def.mp (Finset.mem_univ i))
  rwa [map_univ_occurrenceInterval] at h

@[simp]
theorem exists_occurrenceInterval_eq_iff {m : Multisegment} {s : Interval} :
    (∃ i : Fin m.card, occurrenceInterval m i = s) ↔ s ∈ m := by
  rw [← Multiset.mem_toList, ← ofFn_occurrenceInterval, List.mem_ofFn]

/-- The number of occurrence labels of `m` carrying segment `s` equals `m.count s`. -/
@[simp]
theorem card_filter_occurrenceInterval_eq (m : Multisegment) (s : Interval) :
    #(Finset.univ.filter fun i : Fin m.card => occurrenceInterval m i = s) = m.count s := by
  conv_rhs => rw [← map_univ_occurrenceInterval m]
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun _ _ => eq_comm

/-- Permuting occurrence labels preserves the multiplicity of every segment. -/
theorem card_filter_occurrenceInterval_comp_equiv (m : Multisegment)
    (σ : Equiv.Perm (Fin m.card)) (s : Interval) :
    #(Finset.univ.filter fun i : Fin m.card => occurrenceInterval m (σ i) = s) = m.count s := by
  rw [← card_filter_occurrenceInterval_eq m s]
  exact Finset.card_equiv σ (by simp)

theorem sum_occurrenceInterval {M : Type*} [AddCommMonoid M]
    (m : Multisegment) (f : Interval → M) :
    ∑ i : Fin m.card, f (occurrenceInterval m i) = (m.map f).sum := by
  conv_rhs => rw [← map_univ_occurrenceInterval m]
  rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

@[simp]
theorem card_filter_mem_occurrenceInterval (m : Multisegment) (a : ℤ) :
    #(Finset.univ.filter fun i : Fin m.card => a ∈ occurrenceInterval m i) =
      degreeDimension m a := by
  conv_rhs => rw [degreeDimension_def, ← map_univ_occurrenceInterval m]
  rw [Multiset.countP_map, Finset.card_def, Finset.filter_val]

@[simp]
theorem sum_card_toFinset_occurrenceInterval (m : Multisegment) :
    ∑ i : Fin m.card, #(occurrenceInterval m i).toFinset = totalLength m :=
  sum_occurrenceInterval m fun s => #s.toFinset

end OccurrenceInterval

end Multisegment

end TauCeti
