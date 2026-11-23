/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Multisegment.Basic
public import Mathlib.Order.Antichain
public import Mathlib.Order.Minimal
import Mathlib.Data.Multiset.AddSub
import Mathlib.Order.Preorder.Finite

/-!
# Canonical maximal peeling of multisegments

Given a multisegment `m`, its canonical maximal part `maximalPart m` keeps **one** copy of each
distinct interval of `m` that is inclusion-maximal among all intervals occurring in `m`. The
remainder `remainder m := m - maximalPart m` retains every non-maximal occurrence together with
any excess copies of repeated maximal intervals, so `maximalPart m + remainder m = m`.

This file builds the multiplicity-sensitive API of the canonical maximal split and proves that
right truncation commutes with both `maximalPart` and `remainder`.

## Main definitions

* `TauCeti.Multisegment.maximalPart`: one copy of each distinct inclusion-maximal interval of `m`.
* `TauCeti.Multisegment.remainder`: the multiset difference `m - maximalPart m`.

## Main results

* `TauCeti.Multisegment.maximalPart_add_remainder`: `maximalPart m + remainder m = m`.
* `TauCeti.Multisegment.exists_le_mem_maximalPart`: every occurrence lies inside an
  inclusion-maximal interval of `m`.
* `TauCeti.Multisegment.maximalPart_shift` and `TauCeti.Multisegment.remainder_shift`:
  translation commutes with canonical maximal peeling.
* `TauCeti.Multisegment.maximalPart_rightTruncate` and
  `TauCeti.Multisegment.remainder_rightTruncate`: right truncation commutes with canonical
  maximal peeling.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §2.4, Lemma 3.6.
-/

public section

namespace TauCeti.Multisegment

/-! ### Canonical maximal part and remainder -/

/-- One copy of each distinct inclusion-maximal interval occurring in `m`. -/
def maximalPart (m : Multisegment) : Multisegment :=
  (m.toFinset.filter fun s => ∀ t ∈ m.toFinset, s ≤ t → s = t).val

/-- The multiset remaining after peeling one copy of each distinct inclusion-maximal interval. -/
def remainder (m : Multisegment) : Multisegment :=
  m - maximalPart m

/-- An interval belongs to `maximalPart m` if and only if it occurs in `m` and is maximal for
inclusion among all intervals of `m`. -/
theorem mem_maximalPart_iff {m : Multisegment} {s : IntInterval} :
    s ∈ maximalPart m ↔ s ∈ m ∧ ∀ t ∈ m, s ≤ t → s = t := by
  simp [maximalPart]

/-- Membership in `maximalPart m` is equivalent to `Maximal (· ∈ m)`. -/
theorem mem_maximalPart_iff_maximal {m : Multisegment} {s : IntInterval} :
    s ∈ maximalPart m ↔ Maximal (· ∈ m) s := by
  rw [mem_maximalPart_iff]
  constructor
  · rintro ⟨hs, hmax⟩
    exact ⟨hs, fun t ht hst => (hmax t ht hst) ▸ le_rfl⟩
  · rintro ⟨hs, hmax⟩
    exact ⟨hs, fun t ht hst => le_antisymm hst (hmax ht hst)⟩

/-- Every distinct inclusion-maximal interval appears at most once in `maximalPart m`. -/
theorem nodup_maximalPart (m : Multisegment) : (maximalPart m).Nodup :=
  Finset.nodup _

/-- The multiplicity of any interval in `maximalPart m` is at most `1`. -/
theorem count_maximalPart_le_one (m : Multisegment) (s : IntInterval) :
    (maximalPart m).count s ≤ 1 :=
  Multiset.nodup_iff_count_le_one.mp (nodup_maximalPart m) s

/-- The multiplicity of `s` in `maximalPart m` is `1` when `s` is inclusion-maximal in `m` and
`0` otherwise. -/
theorem count_maximalPart (m : Multisegment) (s : IntInterval) :
    (maximalPart m).count s = if s ∈ m ∧ ∀ t ∈ m, s ≤ t → s = t then 1 else 0 := by
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (nodup_maximalPart m) (mem_maximalPart_iff.mpr h)
  · exact Multiset.count_eq_zero.mpr (mt mem_maximalPart_iff.mp h)

/-- An interval has multiplicity `1` in `maximalPart m` if and only if it is inclusion-maximal
in `m`. -/
theorem count_maximalPart_eq_one_iff {m : Multisegment} {s : IntInterval} :
    (maximalPart m).count s = 1 ↔ s ∈ m ∧ ∀ t ∈ m, s ≤ t → s = t := by
  rw [count_maximalPart]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨by simp, fun h' => (h h').elim⟩

/-- `maximalPart m` is a submultiset of `m`. -/
theorem maximalPart_le (m : Multisegment) : maximalPart m ≤ m := by
  rw [Multiset.le_iff_count]
  intro s
  rw [count_maximalPart]
  split_ifs with h
  · exact Multiset.count_pos.mpr h.1
  · exact Nat.zero_le _

/-- `remainder m` is a submultiset of `m`. -/
theorem remainder_le (m : Multisegment) : remainder m ≤ m :=
  Multiset.sub_le_self m (maximalPart m)

/-- `maximalPart m` and `remainder m` decompose `m` as a multiset sum. -/
@[simp]
theorem maximalPart_add_remainder (m : Multisegment) : maximalPart m + remainder m = m :=
  add_tsub_cancel_of_le (maximalPart_le m)

/-- Explicit multiplicity of `s` in `remainder m`. -/
theorem count_remainder (m : Multisegment) (s : IntInterval) :
    (remainder m).count s = m.count s - (maximalPart m).count s :=
  Multiset.count_sub s m (maximalPart m)

@[simp]
theorem maximalPart_zero : maximalPart 0 = 0 := by
  simp [maximalPart]

@[simp]
theorem remainder_zero : remainder 0 = 0 := by
  simp [remainder]

@[simp]
theorem maximalPart_singleton (s : IntInterval) : maximalPart {s} = {s} := by
  apply Multiset.ext.mpr
  intro t
  rw [count_maximalPart, Multiset.count_singleton]
  by_cases h : t = s
  · subst h; simp
  · simp [h]

@[simp]
theorem remainder_singleton (s : IntInterval) : remainder {s} = 0 := by
  simp [remainder]

/-- Comparable elements of `maximalPart m` are equal. -/
theorem eq_of_mem_maximalPart_of_le {m : Multisegment} {s t : IntInterval}
    (hs : s ∈ maximalPart m) (ht : t ∈ maximalPart m) (hst : s ≤ t) : s = t :=
  (mem_maximalPart_iff.mp hs).2 t (mem_maximalPart_iff.mp ht).1 hst

/-- The distinct intervals of `maximalPart m` form an antichain for interval inclusion. -/
theorem isAntichain_maximalPart (m : Multisegment) :
    IsAntichain (· ≤ ·) ((maximalPart m).toFinset : Set IntInterval) := by
  intro s hs t ht hne hst
  exact hne (eq_of_mem_maximalPart_of_le (Multiset.mem_toFinset.mp hs)
    (Multiset.mem_toFinset.mp ht) hst)

/-- Every occurrence of `m` is contained in an interval of `maximalPart m`. -/
theorem exists_le_mem_maximalPart {m : Multisegment} {s : IntInterval} (hs : s ∈ m) :
    ∃ t ∈ maximalPart m, s ≤ t := by
  obtain ⟨t, hst, hmax⟩ := m.toFinset.exists_le_maximal (Multiset.mem_toFinset.mpr hs)
  refine ⟨t, mem_maximalPart_iff_maximal.mpr ?_, hst⟩
  simpa only [Multiset.mem_toFinset] using hmax

/-- `maximalPart m` is empty if and only if `m` is empty. -/
@[simp]
theorem maximalPart_eq_zero_iff (m : Multisegment) : maximalPart m = 0 ↔ m = 0 := by
  constructor
  · intro h
    by_contra hm
    obtain ⟨s, hs⟩ := Multiset.exists_mem_of_ne_zero hm
    obtain ⟨t, ht, -⟩ := exists_le_mem_maximalPart hs
    simp [h] at ht
  · rintro rfl; exact maximalPart_zero

/-! ### Compatibility with translation -/

/-- Integer translation commutes with taking the canonical maximal part. -/
theorem maximalPart_shift (m : Multisegment) (c : ℤ) :
    maximalPart (shift m c) = shift (maximalPart m) c := by
  apply Multiset.ext.mpr
  intro s
  rw [count_shift, count_maximalPart, count_maximalPart]
  have hiff : (s ∈ shift m c ∧ ∀ t ∈ shift m c, s ≤ t → s = t) ↔
      (s.shift (-c) ∈ m ∧ ∀ u ∈ m, s.shift (-c) ≤ u → s.shift (-c) = u) := by
    rw [mem_shift_iff]
    refine and_congr_right fun _ => ⟨fun h u hu hle => ?_, fun h t ht hle => ?_⟩
    · have hle' : s ≤ u.shift c := by
        simpa [IntInterval.shift_shift] using
          (IntInterval.shift_le_shift_iff (c := c)).mpr hle
      have heq := h (u.shift c) (shift_mem_shift_iff.mpr hu) hle'
      simpa using congrArg (·.shift (-c)) heq
    · have ht' : t.shift (-c) ∈ m := mem_shift_iff.mp ht
      have hle' : s.shift (-c) ≤ t.shift (-c) := IntInterval.shift_le_shift_iff.mpr hle
      exact IntInterval.shift_injective (-c) (h (t.shift (-c)) ht' hle')
  simp [hiff]

/-- Integer translation commutes with taking the remainder. -/
theorem remainder_shift (m : Multisegment) (c : ℤ) :
    remainder (shift m c) = shift (remainder m) c := by
  apply add_left_cancel (a := maximalPart (shift m c))
  rw [maximalPart_add_remainder, maximalPart_shift, ← shift_add, maximalPart_add_remainder]

/-! ### Compatibility with right truncation -/

/-- Right truncation commutes with taking the canonical maximal part. -/
theorem maximalPart_rightTruncate (m : Multisegment) :
    maximalPart (rightTruncate m) = rightTruncate (maximalPart m) := by
  apply Multiset.ext.mpr
  intro t
  rw [count_rightTruncate, count_maximalPart, count_maximalPart]
  have hiff : (t ∈ rightTruncate m ∧ ∀ u ∈ rightTruncate m, t ≤ u → t = u) ↔
      (t.extendRight ∈ m ∧ ∀ v ∈ m, t.extendRight ≤ v → t.extendRight = v) := by
    rw [mem_rightTruncate_iff_extendRight_mem]
    refine and_congr_right fun _ => ⟨fun h v hv hle => ?_, fun h u hu hle => ?_⟩
    · have hv_lt : v.fst < v.snd := by
        rw [NonemptyInterval.le_def] at hle
        have := t.fst_le_snd
        simp only [IntInterval.fst_extendRight, IntInterval.snd_extendRight] at hle
        omega
      obtain ⟨u, hu⟩ : ∃ u, v.shorten = some u := ⟨_, IntInterval.shorten_of_lt hv_lt⟩
      have hv_eq : v = u.extendRight := (IntInterval.shorten_eq_some_iff_eq_extendRight v u).mp hu
      subst hv_eq
      have htu : t ≤ u := IntInterval.extendRight_le_extendRight_iff.mp hle
      exact congrArg IntInterval.extendRight
        (h u (mem_rightTruncate_iff_extendRight_mem.mpr hv) htu)
    · exact IntInterval.extendRight_injective
        (h u.extendRight (mem_rightTruncate_iff_extendRight_mem.mp hu)
          (IntInterval.extendRight_le_extendRight_iff.mpr hle))
  simp [hiff]

/-- Right truncation commutes with taking the remainder. -/
theorem remainder_rightTruncate (m : Multisegment) :
    remainder (rightTruncate m) = rightTruncate (remainder m) := by
  apply add_left_cancel (a := maximalPart (rightTruncate m))
  rw [maximalPart_add_remainder, maximalPart_rightTruncate, ← rightTruncate_add,
    maximalPart_add_remainder]

end TauCeti.Multisegment
