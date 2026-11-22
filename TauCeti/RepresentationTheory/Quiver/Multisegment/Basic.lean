/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Interval.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Order.Interval.Set.Card

/-!
# Integral intervals and multisegments

An integral segment is a nonempty closed integer interval `[b, e]` (`b ≤ e`), realized by
specializing Mathlib's `NonemptyInterval ℤ`. Its length is the positive integer point count
`e - b + 1`, translation shifts both endpoints by a fixed integer, and right shortening sends
`[b, e]` to `[b, e - 1]` when `b < e` and deletes singletons (`none`).

A multisegment is a finite multiset of integral intervals (`Multiset IntInterval`). Repeated
intervals remain distinct occurrences: `degreeDimension` counts occurrences containing a given
integer degree, `totalLength` sums their positive lengths, `rightTruncate` shortens every
occurrence while dropping singletons, `shift` translates every occurrence, and
`occurrenceInterval` indexes the occurrences by `Fin m.card` without collapsing multiplicities.

## Main definitions

* `TauCeti.IntInterval`: nonempty closed integer intervals (`NonemptyInterval ℤ`).
* `TauCeti.IntInterval.length`: positive point count `e - b + 1` of an integral interval.
* `TauCeti.IntInterval.shift`: integer translation of an integral interval.
* `TauCeti.IntInterval.shorten`: optional right shortening deleting singletons.
* `TauCeti.IntInterval.extendRight`: right extension `[b, e] ↦ [b, e + 1]`, the unique preimage
  under `shorten`.
* `TauCeti.Multisegment`: finite multisets of integral intervals.
* `TauCeti.Multisegment.degreeDimension`: number of occurrences containing a given degree.
* `TauCeti.Multisegment.supportDegrees`: finite set of degrees covered by at least one occurrence.
* `TauCeti.Multisegment.totalLength`: sum of lengths of all occurrences.
* `TauCeti.Multisegment.rightTruncate`: right shortening applied to every occurrence.
* `TauCeti.Multisegment.shift`: integer translation applied to every occurrence.
* `TauCeti.Multisegment.occurrenceInterval`: finite indexing of occurrences by `Fin m.card`.
* `TauCeti.Multisegment.StandardIndex`: occurrence–degree labels `(i, a)` with `a` in the
  `i`-th occurrence.

## Main results

* `TauCeti.IntInterval.shorten_shift`: right shortening commutes with integer translation.
* `TauCeti.Multisegment.sum_degreeDimension_eq_totalLength`: the sum of degree dimensions over
  any finite set containing the support equals `totalLength`.
* `TauCeti.Multisegment.totalLength_rightTruncate_add_card`: right truncation decreases
  `totalLength` by the occurrence cardinality.
* `TauCeti.Multisegment.rightTruncate_shift`: right truncation commutes with translation.
* `TauCeti.Multisegment.card_filter_occurrenceInterval_eq`: occurrence labels recover exact
  interval multiplicities and are invariant under label permutations.
* `TauCeti.Multisegment.card_standardIndex`: there are `totalLength m` occurrence–degree labels.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §§2.1, 2.3, 3.1.
-/

public section

namespace TauCeti

/-- A nonempty closed integer interval `[b, e]` with `b ≤ e`, modeling an integral segment. -/
abbrev IntInterval := NonemptyInterval ℤ

namespace IntInterval

/-! ### Length -/

/-- The length of `[b, e]` is its positive integer point count `e - b + 1`. -/
def length (s : IntInterval) : ℕ :=
  (s.snd - s.fst + 1).toNat

/-- Explicit formula for `IntInterval.length`. -/
theorem length_def (s : IntInterval) : s.length = (s.snd - s.fst + 1).toNat := (rfl)

/-- Coerced to `ℤ`, the length of `[b, e]` is `e - b + 1`. -/
theorem coe_length (s : IntInterval) : (s.length : ℤ) = s.snd - s.fst + 1 := by
  have := s.fst_le_snd
  rw [length_def]
  omega

/-- Every integral interval has positive length. -/
@[simp]
theorem length_pos (s : IntInterval) : 0 < s.length := by
  have := s.coe_length
  have := s.fst_le_snd
  omega

/-- A singleton interval has length `1`. -/
@[simp]
theorem length_pure (a : ℤ) : IntInterval.length (NonemptyInterval.pure a) = 1 := by
  have h := IntInterval.coe_length (NonemptyInterval.pure a)
  simp only [NonemptyInterval.pure_fst, NonemptyInterval.pure_snd] at h
  omega

/-- An integral interval has length `1` if and only if it is a singleton. -/
theorem length_eq_one_iff (s : IntInterval) : s.length = 1 ↔ s.fst = s.snd := by
  have := s.coe_length
  omega

/-- The length of `[b, e]` equals the cardinality of the integer interval `Finset.Icc b e`. -/
theorem length_eq_card_Icc (s : IntInterval) : s.length = (Finset.Icc s.fst s.snd).card := by
  rw [Int.card_Icc, length_def]
  congr 1
  omega

/-- The length of `[b, e]` equals the cardinality of its underlying set of integers. -/
theorem length_eq_ncard (s : IntInterval) : s.length = (s : Set ℤ).ncard := by
  rw [NonemptyInterval.coe_def, Set.ncard_Icc, length_eq_card_Icc]

/-- Inclusion of integral intervals is monotone for length. -/
theorem length_mono {s t : IntInterval} (h : s ≤ t) : s.length ≤ t.length := by
  rw [NonemptyInterval.le_def] at h
  have := s.coe_length
  have := t.coe_length
  omega

/-- Strict inclusion of integral intervals strictly increases length. -/
theorem length_strictMono {s t : IntInterval} (h : s < t) : s.length < t.length := by
  have hle : s ≤ t := h.le
  rw [NonemptyInterval.le_def] at hle
  have := s.coe_length
  have := t.coe_length
  by_contra hge
  exact h.ne (NonemptyInterval.ext (Prod.ext (by omega) (by omega)))

/-! ### Translation -/

/-- Translate `[b, e]` by an integer `c` to `[b + c, e + c]`. -/
def shift (s : IntInterval) (c : ℤ) : IntInterval :=
  s.map (OrderIso.addRight c).toOrderEmbedding.toOrderHom

/-- The left endpoint of `s.shift c` is `s.fst + c`. -/
@[simp, grind =]
theorem fst_shift (s : IntInterval) (c : ℤ) : (s.shift c).fst = s.fst + c := (rfl)

/-- The right endpoint of `s.shift c` is `s.snd + c`. -/
@[simp, grind =]
theorem snd_shift (s : IntInterval) (c : ℤ) : (s.shift c).snd = s.snd + c := (rfl)

/-- Translating by `0` fixes an interval. -/
@[simp]
theorem shift_zero (s : IntInterval) : s.shift 0 = s :=
  NonemptyInterval.ext (Prod.ext (by simp) (by simp))

/-- Successive translations add their shifts. -/
@[simp]
theorem shift_shift (s : IntInterval) (c d : ℤ) : (s.shift c).shift d = s.shift (c + d) :=
  NonemptyInterval.ext (Prod.ext (by simp [add_assoc]) (by simp [add_assoc]))

/-- Translating a singleton shifts its unique point. -/
@[simp]
theorem shift_pure (a c : ℤ) :
    IntInterval.shift (NonemptyInterval.pure a) c = NonemptyInterval.pure (a + c) :=
  NonemptyInterval.ext (Prod.ext (by simp) (by simp))

/-- Translation preserves interval length. -/
@[simp]
theorem length_shift (s : IntInterval) (c : ℤ) : (s.shift c).length = s.length := by
  have h1 := (s.shift c).coe_length
  have h2 := s.coe_length
  simp only [fst_shift, snd_shift] at h1
  omega

/-- An integer `a + c` lies in `s.shift c` if and only if `a` lies in `s`. -/
@[simp]
theorem add_mem_shift_iff (s : IntInterval) (a c : ℤ) : a + c ∈ s.shift c ↔ a ∈ s := by
  simp only [NonemptyInterval.mem_def, fst_shift, snd_shift]
  omega

/-- Membership in `s.shift c` is shifted by `-c`. -/
theorem mem_shift_iff (s : IntInterval) (a c : ℤ) : a ∈ s.shift c ↔ a - c ∈ s := by
  simpa using add_mem_shift_iff s (a - c) c

/-- Translation preserves and reflects interval inclusion. -/
@[simp]
theorem shift_le_shift_iff {s t : IntInterval} {c : ℤ} : s.shift c ≤ t.shift c ↔ s ≤ t := by
  simp only [NonemptyInterval.le_def, fst_shift, snd_shift]
  omega

/-- Translation by a fixed integer is injective. -/
theorem shift_injective (c : ℤ) : Function.Injective (fun s : IntInterval => s.shift c) := by
  intro s t h
  simpa using congrArg (·.shift (-c)) h

/-! ### Right shortening and extension -/

/-- Shorten `[b, e]` on the right to `[b, e - 1]` when `b < e`, deleting singletons (`none`). -/
def shorten (s : IntInterval) : Option IntInterval :=
  if h : s.fst < s.snd then some ⟨(s.fst, s.snd - 1), by omega⟩ else none

/-- Right shortening returns `none` precisely on singleton intervals. -/
theorem shorten_eq_none_iff (s : IntInterval) : s.shorten = none ↔ s.fst = s.snd := by
  have := s.fst_le_snd
  unfold shorten
  split_ifs with h <;> simp <;> omega

/-- Right shortening deletes every singleton interval. -/
@[simp]
theorem shorten_pure (a : ℤ) : IntInterval.shorten (NonemptyInterval.pure a) = none :=
  (shorten_eq_none_iff _).mpr rfl

/-- Right shortening of a nonsingleton `[b, e]` (`b < e`) is `some [b, e - 1]`. -/
theorem shorten_of_lt {s : IntInterval} (h : s.fst < s.snd) :
    s.shorten = some ⟨(s.fst, s.snd - 1), by omega⟩ := by
  unfold shorten
  simp [h]

/-- Characterization of `s.shorten = some t` by endpoints. -/
theorem shorten_eq_some_iff (s t : IntInterval) :
    s.shorten = some t ↔ s.fst < s.snd ∧ t.fst = s.fst ∧ t.snd = s.snd - 1 := by
  unfold shorten
  split_ifs with h
  · constructor
    · intro hEq
      have hst : (⟨(s.fst, s.snd - 1), by omega⟩ : IntInterval) = t := Option.some.inj hEq
      subst hst
      exact ⟨h, rfl, rfl⟩
    · rintro ⟨-, h1, h2⟩
      exact congrArg some (NonemptyInterval.ext (Prod.ext h1.symm h2.symm))
  · exact ⟨by rintro ⟨⟩, fun ⟨hlt, _⟩ => (h hlt).elim⟩

/-- Membership in a shortened interval `t` (`s.shorten = some t`) is `s.fst ≤ a < s.snd`. -/
theorem mem_of_shorten_eq_some {s t : IntInterval} (h : s.shorten = some t) (a : ℤ) :
    a ∈ t ↔ s.fst ≤ a ∧ a < s.snd := by
  obtain ⟨_, h1, h2⟩ := (shorten_eq_some_iff s t).mp h
  rw [NonemptyInterval.mem_def, h1, h2]
  omega

/-- Right shortening decreases interval length by `1`. -/
theorem length_of_shorten_eq_some {s t : IntInterval} (h : s.shorten = some t) :
    t.length + 1 = s.length := by
  obtain ⟨_, h1, h2⟩ := (shorten_eq_some_iff s t).mp h
  have := s.coe_length
  have := t.coe_length
  omega

/-- Right shortening commutes with integer translation. -/
theorem shorten_shift (s : IntInterval) (c : ℤ) :
    (s.shift c).shorten = s.shorten.map (·.shift c) := by
  by_cases h : s.fst < s.snd
  · have h' : (s.shift c).fst < (s.shift c).snd := by simp; omega
    rw [shorten_of_lt h, shorten_of_lt h', Option.map_some]
    exact congrArg some (NonemptyInterval.ext (Prod.ext (by simp) (by simp; omega)))
  · have hEq : s.fst = s.snd := le_antisymm s.fst_le_snd (not_lt.mp h)
    have h' : (s.shift c).fst = (s.shift c).snd := by simp [hEq]
    rw [(shorten_eq_none_iff _).mpr h', (shorten_eq_none_iff _).mpr hEq, Option.map_none]

/-- Extend `[b, e]` on the right to `[b, e + 1]`; this is the unique preimage under `shorten`. -/
def extendRight (t : IntInterval) : IntInterval :=
  ⟨(t.fst, t.snd + 1), by have := t.fst_le_snd; omega⟩

/-- The left endpoint of `t.extendRight` is `t.fst`. -/
@[simp, grind =]
theorem fst_extendRight (t : IntInterval) : t.extendRight.fst = t.fst := (rfl)

/-- The right endpoint of `t.extendRight` is `t.snd + 1`. -/
@[simp, grind =]
theorem snd_extendRight (t : IntInterval) : t.extendRight.snd = t.snd + 1 := (rfl)

/-- Shortening `t.extendRight` always returns `some t`. -/
@[simp]
theorem shorten_extendRight (t : IntInterval) : t.extendRight.shorten = some t := by
  rw [shorten_eq_some_iff]
  have := t.fst_le_snd
  exact ⟨by simp; omega, by simp, by simp⟩

/-- `s.shorten = some t` holds if and only if `s = t.extendRight`. -/
theorem shorten_eq_some_iff_eq_extendRight (s t : IntInterval) :
    s.shorten = some t ↔ s = t.extendRight := by
  rw [shorten_eq_some_iff]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact NonemptyInterval.ext (Prod.ext h1.symm (by simp; omega))
  · rintro rfl
    have := t.fst_le_snd
    exact ⟨by simp; omega, by simp, by simp⟩

/-- Right extension is injective. -/
theorem extendRight_injective : Function.Injective IntInterval.extendRight := fun t₁ t₂ h =>
  Option.some_injective _ <| by rw [← shorten_extendRight t₁, ← shorten_extendRight t₂, h]

/-- Right shortening is injective on nonsingleton intervals. -/
theorem shorten_injective_of_eq_some {s₁ s₂ t : IntInterval}
    (h₁ : s₁.shorten = some t) (h₂ : s₂.shorten = some t) : s₁ = s₂ := by
  rw [shorten_eq_some_iff_eq_extendRight] at h₁ h₂
  exact h₁.trans h₂.symm

/-- Right extension preserves and reflects interval inclusion. -/
@[simp]
theorem extendRight_le_extendRight_iff {t₁ t₂ : IntInterval} :
    t₁.extendRight ≤ t₂.extendRight ↔ t₁ ≤ t₂ := by
  simp only [NonemptyInterval.le_def, fst_extendRight, snd_extendRight]
  omega

/-- Right shortening preserves and reflects inclusion among surviving intervals. -/
theorem le_iff_of_shorten_eq_some {s₁ s₂ t₁ t₂ : IntInterval}
    (h₁ : s₁.shorten = some t₁) (h₂ : s₂.shorten = some t₂) :
    t₁ ≤ t₂ ↔ s₁ ≤ s₂ := by
  rw [shorten_eq_some_iff_eq_extendRight] at h₁ h₂
  subst h₁; subst h₂
  exact extendRight_le_extendRight_iff.symm

/-- A shortened interval is contained in the original interval. -/
theorem le_of_shorten_eq_some {s t : IntInterval} (h : s.shorten = some t) : t ≤ s := by
  rw [shorten_eq_some_iff_eq_extendRight] at h
  subst h
  rw [NonemptyInterval.le_def]
  simp only [fst_extendRight, snd_extendRight]
  omega

end IntInterval

/-! ## Multisegments -/

/-- A finite multiset of nonempty closed integer intervals; equal intervals remain distinct
occurrences. -/
abbrev Multisegment := Multiset IntInterval

namespace Multisegment

/-! ### Degree dimensions and total length -/

/-- The degree-`a` dimension of a multisegment `m`: the number of interval occurrences
containing `a`. -/
def degreeDimension (m : Multisegment) (a : ℤ) : ℕ :=
  m.countP (a ∈ ·)

/-- `degreeDimension` equals the cardinality of the submultiset of occurrences containing `a`. -/
theorem degreeDimension_eq_card_filter (m : Multisegment) (a : ℤ) :
    degreeDimension m a = (m.filter (a ∈ ·)).card :=
  Multiset.countP_eq_card_filter (a ∈ ·) m

@[simp]
theorem degreeDimension_zero (a : ℤ) : degreeDimension 0 a = 0 :=
  Multiset.countP_zero (a ∈ ·)

@[simp]
theorem degreeDimension_cons (s : IntInterval) (m : Multisegment) (a : ℤ) :
    degreeDimension (s ::ₘ m) a = degreeDimension m a + if a ∈ s then 1 else 0 :=
  Multiset.countP_cons (a ∈ ·) s m

@[simp]
theorem degreeDimension_singleton (s : IntInterval) (a : ℤ) :
    degreeDimension {s} a = if a ∈ s then 1 else 0 := by
  rw [← Multiset.cons_zero, degreeDimension_cons, degreeDimension_zero, zero_add]

@[simp]
theorem degreeDimension_add (m₁ m₂ : Multisegment) (a : ℤ) :
    degreeDimension (m₁ + m₂) a = degreeDimension m₁ a + degreeDimension m₂ a :=
  Multiset.countP_add (a ∈ ·) m₁ m₂

/-- `degreeDimension m a` is positive if and only if some occurrence of `m` contains `a`. -/
theorem degreeDimension_pos_iff (m : Multisegment) (a : ℤ) :
    0 < degreeDimension m a ↔ ∃ s ∈ m, a ∈ s :=
  Multiset.countP_pos

/-- `degreeDimension m a` vanishes if and only if no occurrence of `m` contains `a`. -/
theorem degreeDimension_eq_zero_iff (m : Multisegment) (a : ℤ) :
    degreeDimension m a = 0 ↔ ∀ s ∈ m, a ∉ s :=
  Multiset.countP_eq_zero

/-- `degreeDimension m a` is the multiplicity-weighted sum over distinct intervals containing `a`.
-/
theorem degreeDimension_eq_sum_count (m : Multisegment) (a : ℤ) :
    degreeDimension m a = ∑ s ∈ m.toFinset with a ∈ s, m.count s := by
  rw [degreeDimension_eq_card_filter, ← Multiset.toFinset_sum_count_eq]
  have hsub : (m.filter (a ∈ ·)).toFinset = m.toFinset.filter (a ∈ ·) := by
    ext s; simp
  rw [hsub]
  refine Finset.sum_congr rfl fun s hs => ?_
  exact Multiset.count_filter_of_pos (Finset.mem_filter.mp hs).2

/-- The finite set of integer degrees lying in at least one interval of `m`. -/
def supportDegrees (m : Multisegment) : Finset ℤ :=
  m.toFinset.biUnion fun s => Finset.Icc s.fst s.snd

/-- Membership in `supportDegrees m` is equivalent to lying in some occurrence of `m`. -/
theorem mem_supportDegrees_iff {m : Multisegment} {a : ℤ} :
    a ∈ supportDegrees m ↔ ∃ s ∈ m, a ∈ s := by
  simp [supportDegrees, NonemptyInterval.mem_def]

/-- Membership in `supportDegrees m` is equivalent to positive degree dimension. -/
theorem mem_supportDegrees_iff_degreeDimension_pos {m : Multisegment} {a : ℤ} :
    a ∈ supportDegrees m ↔ 0 < degreeDimension m a :=
  mem_supportDegrees_iff.trans (degreeDimension_pos_iff m a).symm

@[simp]
theorem supportDegrees_zero : supportDegrees 0 = ∅ := by
  simp [supportDegrees]

@[simp]
theorem supportDegrees_add (m₁ m₂ : Multisegment) :
    supportDegrees (m₁ + m₂) = supportDegrees m₁ ∪ supportDegrees m₂ := by
  ext a
  simp [mem_supportDegrees_iff, or_and_right, exists_or]

/-- The total length of `m`: the sum of positive lengths of all interval occurrences. -/
def totalLength (m : Multisegment) : ℕ :=
  (m.map IntInterval.length).sum

@[simp]
theorem totalLength_zero : totalLength 0 = 0 := by
  simp [totalLength]

@[simp]
theorem totalLength_singleton (s : IntInterval) : totalLength {s} = s.length := by
  simp [totalLength]

@[simp]
theorem totalLength_cons (s : IntInterval) (m : Multisegment) :
    totalLength (s ::ₘ m) = s.length + totalLength m := by
  simp [totalLength]

@[simp]
theorem totalLength_add (m₁ m₂ : Multisegment) :
    totalLength (m₁ + m₂) = totalLength m₁ + totalLength m₂ := by
  simp [totalLength]

/-- Total length is at least the number of interval occurrences, since every interval has
length at least `1`. -/
theorem card_le_totalLength (m : Multisegment) : m.card ≤ totalLength m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    simp only [Multiset.card_cons, totalLength_cons]
    have := s.length_pos
    omega

/-- A multisegment has total length zero if and only if it is empty. -/
@[simp]
theorem totalLength_eq_zero_iff (m : Multisegment) : totalLength m = 0 ↔ m = 0 := by
  refine ⟨fun h => Multiset.card_eq_zero.mp ?_, fun h => by simp [h]⟩
  have := card_le_totalLength m
  omega

/-- Summing `degreeDimension m a` over any finite set of integers covering all intervals of `m`
recovers `totalLength m`. -/
theorem sum_degreeDimension_eq_totalLength (m : Multisegment) {F : Finset ℤ}
    (hF : ∀ s ∈ m, ∀ a ∈ s, a ∈ F) :
    ∑ a ∈ F, degreeDimension m a = totalLength m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    have hFm : ∀ t ∈ m, ∀ a ∈ t, a ∈ F := fun t ht => hF t (Multiset.mem_cons_of_mem ht)
    have hFs : Finset.Icc s.fst s.snd ⊆ F := fun a ha =>
      hF s (Multiset.mem_cons_self s m) a (by simpa [NonemptyInterval.mem_def] using ha)
    simp only [degreeDimension_cons, totalLength_cons, Finset.sum_add_distrib, ih hFm]
    rw [add_comm]
    congr 1
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Nat.cast_id,
      mul_one, IntInterval.length_eq_card_Icc]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, NonemptyInterval.mem_def, and_iff_right_iff_imp]
    exact fun ha => hFs (Finset.mem_Icc.mpr ha)

/-- Summing `degreeDimension m a` over `supportDegrees m` equals `totalLength m`. -/
theorem sum_supportDegrees_degreeDimension (m : Multisegment) :
    ∑ a ∈ supportDegrees m, degreeDimension m a = totalLength m :=
  sum_degreeDimension_eq_totalLength m fun s hs _ ha => mem_supportDegrees_iff.mpr ⟨s, hs, ha⟩

/-! ### Right truncation -/

/-- Shorten every occurrence of `m` on the right and delete every singleton occurrence. -/
def rightTruncate (m : Multisegment) : Multisegment :=
  m.filterMap IntInterval.shorten

/-- `rightTruncate` expressed via `Multiset.bind`. -/
theorem rightTruncate_eq_bind (m : Multisegment) :
    rightTruncate m = m.bind fun s => match s.shorten with
      | none => 0
      | some t => {t} := by
  rw [rightTruncate, Multiset.filterMap_eq_bind]
  congr 1
  funext s
  cases s.shorten <;> rfl

@[simp]
theorem rightTruncate_zero : rightTruncate 0 = 0 :=
  Multiset.filterMap_zero _

theorem rightTruncate_cons (s : IntInterval) (m : Multisegment) :
    rightTruncate (s ::ₘ m) = match s.shorten with
      | none => rightTruncate m
      | some t => t ::ₘ rightTruncate m := by
  cases h : s.shorten with
  | none => exact Multiset.filterMap_cons_none s m h
  | some t => exact Multiset.filterMap_cons_some IntInterval.shorten s m h

@[simp]
theorem rightTruncate_singleton_pure (a : ℤ) :
    rightTruncate ({NonemptyInterval.pure a} : Multisegment) = 0 := by
  rw [← Multiset.cons_zero, rightTruncate_cons, IntInterval.shorten_pure, rightTruncate_zero]

@[simp]
theorem rightTruncate_singleton_extendRight (t : IntInterval) :
    rightTruncate ({t.extendRight} : Multisegment) = {t} := by
  rw [← Multiset.cons_zero, rightTruncate_cons, IntInterval.shorten_extendRight,
    rightTruncate_zero]
  exact Multiset.cons_zero t

@[simp]
theorem rightTruncate_add (m₁ m₂ : Multisegment) :
    rightTruncate (m₁ + m₂) = rightTruncate m₁ + rightTruncate m₂ :=
  Multiset.filterMap_add _ m₁ m₂

/-- Right truncation is monotone for submultiset inclusion. -/
theorem rightTruncate_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) :
    rightTruncate m₁ ≤ rightTruncate m₂ :=
  Multiset.filterMap_le_filterMap _ h

/-- Membership in `rightTruncate m` is existence of a preimage under `IntInterval.shorten`. -/
theorem mem_rightTruncate_iff {m : Multisegment} {t : IntInterval} :
    t ∈ rightTruncate m ↔ ∃ s ∈ m, s.shorten = some t :=
  Multiset.mem_filterMap IntInterval.shorten m

/-- Membership in `rightTruncate m` is equivalent to membership of `t.extendRight` in `m`. -/
theorem mem_rightTruncate_iff_extendRight_mem {m : Multisegment} {t : IntInterval} :
    t ∈ rightTruncate m ↔ t.extendRight ∈ m := by
  rw [mem_rightTruncate_iff]
  exact ⟨fun ⟨s, hs, h⟩ => by
      rwa [← (IntInterval.shorten_eq_some_iff_eq_extendRight s t).mp h],
    fun ht => ⟨t.extendRight, ht, IntInterval.shorten_extendRight t⟩⟩

/-- The multiplicity of `t` in `rightTruncate m` is the multiplicity of `t.extendRight` in `m`. -/
theorem count_rightTruncate (m : Multisegment) (t : IntInterval) :
    (rightTruncate m).count t = m.count t.extendRight := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    rw [rightTruncate_cons]
    cases h : s.shorten with
    | none =>
      have hne : t.extendRight ≠ s := fun heq => by
        subst heq; simp [IntInterval.shorten_extendRight] at h
      rw [ih, Multiset.count_cons_of_ne hne]
    | some u =>
      have hu : s = u.extendRight := (IntInterval.shorten_eq_some_iff_eq_extendRight s u).mp h
      by_cases htu : t = u
      · subst htu; rw [hu, Multiset.count_cons_self, Multiset.count_cons_self, ih]
      · rw [hu, Multiset.count_cons_of_ne htu,
          Multiset.count_cons_of_ne (IntInterval.extendRight_injective.ne htu), ih]

/-- Right truncation cannot increase occurrence cardinality. -/
theorem card_rightTruncate_le (m : Multisegment) : (rightTruncate m).card ≤ m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    rw [rightTruncate_cons, Multiset.card_cons]
    cases s.shorten <;> simp <;> omega

/-- Right truncation decreases `totalLength m` by precisely `m.card`. -/
theorem totalLength_rightTruncate_add_card (m : Multisegment) :
    totalLength (rightTruncate m) + m.card = totalLength m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    rw [rightTruncate_cons, Multiset.card_cons, totalLength_cons]
    cases h : s.shorten with
    | none =>
      have hs : s.length = 1 :=
        (IntInterval.length_eq_one_iff s).mpr ((IntInterval.shorten_eq_none_iff s).mp h)
      dsimp only
      omega
    | some t =>
      have hs : t.length + 1 = s.length := IntInterval.length_of_shorten_eq_some h
      dsimp only
      rw [totalLength_cons]
      omega

/-- Right truncation strictly decreases `totalLength` for every nonempty multisegment. -/
theorem totalLength_rightTruncate_lt {m : Multisegment} (hm : m ≠ 0) :
    totalLength (rightTruncate m) < totalLength m := by
  have := totalLength_rightTruncate_add_card m
  have : 0 < m.card := Multiset.card_pos.mpr hm
  omega

/-! ### Translation -/

/-- Translate every interval occurrence of `m` by an integer `c`. -/
def shift (m : Multisegment) (c : ℤ) : Multisegment :=
  m.map (·.shift c)

@[simp]
theorem zero_shift (c : ℤ) : shift 0 c = 0 :=
  Multiset.map_zero _

@[simp]
theorem shift_zero (m : Multisegment) : shift m 0 = m := by
  simp [shift]

@[simp]
theorem shift_singleton (s : IntInterval) (c : ℤ) : shift {s} c = {s.shift c} :=
  Multiset.map_singleton _ _

@[simp]
theorem shift_cons (s : IntInterval) (m : Multisegment) (c : ℤ) :
    shift (s ::ₘ m) c = s.shift c ::ₘ shift m c :=
  Multiset.map_cons _ _ _

@[simp]
theorem shift_add (m₁ m₂ : Multisegment) (c : ℤ) :
    shift (m₁ + m₂) c = shift m₁ c + shift m₂ c :=
  Multiset.map_add _ _ _

@[simp]
theorem shift_shift (m : Multisegment) (c d : ℤ) : shift (shift m c) d = shift m (c + d) := by
  simp [shift, Multiset.map_map]

@[simp]
theorem card_shift (m : Multisegment) (c : ℤ) : (shift m c).card = m.card :=
  Multiset.card_map _ _

/-- Membership in `shift m c` at a shifted interval. -/
@[simp]
theorem shift_mem_shift_iff {m : Multisegment} {s : IntInterval} {c : ℤ} :
    s.shift c ∈ shift m c ↔ s ∈ m := by
  simp [shift, (IntInterval.shift_injective c).eq_iff]

/-- Membership in `shift m c`. -/
theorem mem_shift_iff {m : Multisegment} {s : IntInterval} {c : ℤ} :
    s ∈ shift m c ↔ s.shift (-c) ∈ m := by
  simpa using shift_mem_shift_iff (m := m) (s := s.shift (-c)) (c := c)

/-- Translation preserves interval multiplicities. -/
@[simp]
theorem count_shift_shift (m : Multisegment) (s : IntInterval) (c : ℤ) :
    (shift m c).count (s.shift c) = m.count s :=
  Multiset.count_map_eq_count' _ m (IntInterval.shift_injective c) s

/-- The multiplicity of `s` in `shift m c` equals the multiplicity of `s.shift (-c)` in `m`. -/
theorem count_shift (m : Multisegment) (s : IntInterval) (c : ℤ) :
    (shift m c).count s = m.count (s.shift (-c)) := by
  simpa using count_shift_shift m (s.shift (-c)) c

/-- Translation preserves total length. -/
@[simp]
theorem totalLength_shift (m : Multisegment) (c : ℤ) :
    totalLength (shift m c) = totalLength m := by
  simp [totalLength, shift, Multiset.map_map]

/-- Translation reindexes degree dimensions by the same shift. -/
@[simp]
theorem degreeDimension_shift_add (m : Multisegment) (a c : ℤ) :
    degreeDimension (shift m c) (a + c) = degreeDimension m a := by
  simp [degreeDimension_eq_card_filter, shift, Multiset.filter_map]

/-- The degree-`a` dimension of `shift m c` equals the degree-`(a - c)` dimension of `m`. -/
theorem degreeDimension_shift (m : Multisegment) (a c : ℤ) :
    degreeDimension (shift m c) a = degreeDimension m (a - c) := by
  simpa using degreeDimension_shift_add m (a - c) c

/-- Right truncation commutes with every integer translation. -/
theorem rightTruncate_shift (m : Multisegment) (c : ℤ) :
    rightTruncate (shift m c) = shift (rightTruncate m) c := by
  rw [rightTruncate, shift, rightTruncate, shift, Multiset.filterMap_map, Multiset.map_filterMap]
  congr 1
  funext s
  exact IntInterval.shorten_shift s c

/-! ### Occurrence indexing -/

/-- A fixed occurrence-sensitive indexing of the intervals of `m` by `Fin m.card`, obtained from
`Multiset.toList`. Distinct indices may carry equal intervals. -/
noncomputable def occurrenceInterval (m : Multisegment) (i : Fin m.card) : IntInterval :=
  m.toList[i.val]'(by simp)

/-- Every occurrence label indexes an interval occurring in `m`. -/
theorem occurrenceInterval_mem (m : Multisegment) (i : Fin m.card) :
    occurrenceInterval m i ∈ m := by
  rw [← Multiset.mem_toList]
  exact List.getElem_mem _

/-- Mapping `occurrenceInterval m` over all indices `Fin m.card` recovers the multiset `m`. -/
theorem map_univ_occurrenceInterval (m : Multisegment) :
    (Finset.univ : Finset (Fin m.card)).val.map (occurrenceInterval m) = m := by
  rw [Fin.univ_val_map]
  have hlist : List.ofFn (occurrenceInterval m) = m.toList := by
    apply List.ext_getElem (by simp)
    intro i _ _
    simp [occurrenceInterval]
  rw [hlist, Multiset.coe_toList]

/-- Permuting occurrence labels preserves the multiset of values. -/
theorem map_univ_occurrenceInterval_comp_perm (m : Multisegment) (σ : Equiv.Perm (Fin m.card)) :
    (Finset.univ : Finset (Fin m.card)).val.map (occurrenceInterval m ∘ σ) = m := by
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv, map_univ_occurrenceInterval]

/-- Permuting occurrence labels preserves the count of every interval. -/
theorem card_filter_occurrenceInterval_perm (m : Multisegment) (σ : Equiv.Perm (Fin m.card))
    (s : IntInterval) :
    (Finset.univ.filter fun i : Fin m.card => occurrenceInterval m (σ i) = s).card =
      m.count s := by
  conv_rhs => rw [← map_univ_occurrenceInterval_comp_perm m σ]
  rw [Multiset.count, Multiset.countP_map, Finset.card_def, Finset.filter_val]
  exact congrArg Multiset.card (Multiset.filter_congr fun _ _ => eq_comm)

/-- The number of occurrence labels carrying `s` equals the multiplicity `m.count s`. -/
theorem card_filter_occurrenceInterval_eq (m : Multisegment) (s : IntInterval) :
    (Finset.univ.filter fun i : Fin m.card => occurrenceInterval m i = s).card = m.count s :=
  card_filter_occurrenceInterval_perm m 1 s

/-- Summing interval lengths over all occurrence labels equals `totalLength m`. -/
theorem sum_length_occurrenceInterval (m : Multisegment) :
    ∑ i : Fin m.card, (occurrenceInterval m i).length = totalLength m := by
  conv_rhs =>
    rw [totalLength, ← map_univ_occurrenceInterval m, Multiset.map_map, Finset.sum_map_val]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- Counting occurrence labels whose interval contains `a` gives `degreeDimension m a`. -/
theorem card_filter_mem_occurrenceInterval (m : Multisegment) (a : ℤ) :
    (Finset.univ.filter fun i : Fin m.card => a ∈ occurrenceInterval m i).card =
      degreeDimension m a := by
  conv_rhs =>
    rw [← map_univ_occurrenceInterval m, degreeDimension_eq_card_filter, Multiset.filter_map,
      Multiset.card_map]
  rw [Finset.card_def, Finset.filter_val]
  exact congrArg Multiset.card (Multiset.filter_congr fun _ _ => Iff.rfl)

/-- The occurrence–degree labels of `m`: an occurrence label `i` together with a degree in the
interval `m.occurrenceInterval i`. They index the standard basis of the standard graded space
of `m`. -/
abbrev StandardIndex (m : Multisegment) : Type :=
  Σ i : Fin m.card, Set.Icc (occurrenceInterval m i).fst (occurrenceInterval m i).snd

/-- The number of occurrence–degree labels is the total length of `m`. -/
theorem card_standardIndex (m : Multisegment) :
    Fintype.card (StandardIndex m) = totalLength m := by
  rw [Fintype.card_sigma, ← sum_length_occurrenceInterval]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [IntInterval.length_eq_card_Icc, ← Fintype.card_Icc]

end Multisegment

end TauCeti
