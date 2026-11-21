/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Order.Preorder.Finite
public import TauCeti.RepresentationTheory.Multisegment.Basic

/-!
# Canonical maximal decomposition of integer multisegments and commutation with right truncation

Every integer multisegment `m` admits a canonical multiplicity-sensitive maximal decomposition
`m = maximalPart m + remainder m`:

* `TauCeti.Multisegment.maximalPart` retains **one** copy of each distinct inclusion-maximal segment
  occurring in `m`, forming an inclusion antichain of distinct intervals that shadows all of `m`.
* `TauCeti.Multisegment.remainder` is `m - maximalPart m`, retaining every non-maximal occurrence
  together with `m.count s - 1` remaining copies of each inclusion-maximal segment `s`.

This file establishes the characteristic API of `maximalPart` and `remainder` (multiplicities,
antichain property, shadowing of arbitrary occurrences, strict drop of `totalLength` for nonempty
`m`, and translation equivariance) and proves that right truncation commutes with both components of
the canonical maximal split (`maximalPart_rightTruncate` and `remainder_rightTruncate`).

## Main definitions and results

* `TauCeti.Multisegment.maximalPart`: one copy of each distinct inclusion-maximal interval of `m`.
* `TauCeti.Multisegment.remainder`: the remaining occurrences `m - maximalPart m`.
* `TauCeti.Multisegment.exists_mem_maximalPart_ge`: every occurrence of `m` is contained in some
  member of `maximalPart m`.
* `TauCeti.Multisegment.maximalPart_rightTruncate`:
  `maximalPart (rightTruncate m) = rightTruncate (maximalPart m)`.
* `TauCeti.Multisegment.remainder_rightTruncate`:
  `remainder (rightTruncate m) = rightTruncate (remainder m)`.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24 (§2.4, p. 10; Lemma 3.6,
  p. 19).
-/

public section

namespace TauCeti.Multisegment

/-- Inclusion maximality among segments occurring in `m` is computably decidable via
`m.toFinset`. -/
instance instDecidableMaximalMem (m : Multisegment) (s : Interval) :
    Decidable (Maximal (· ∈ m) s) :=
  decidable_of_iff' (s ∈ m.toFinset ∧ ∀ t ∈ m.toFinset, s ≤ t → s = t) <| by
    rw [maximal_iff]
    simp

/-- One copy of each distinct inclusion-maximal interval occurring in `m`. -/
def maximalPart (m : Multisegment) : Multisegment :=
  (m.toFinset.filter fun s => ∀ t ∈ m.toFinset, s ≤ t → s = t).val

theorem maximalPart_def (m : Multisegment) :
    maximalPart m = (m.toFinset.filter fun s => ∀ t ∈ m.toFinset, s ≤ t → s = t).val :=
  (rfl)

/-- A segment belongs to `maximalPart m` if and only if it is inclusion-maximal among segments
occurring in `m`. -/
@[simp]
theorem mem_maximalPart_iff {m : Multisegment} {s : Interval} :
    s ∈ maximalPart m ↔ Maximal (· ∈ m) s := by
  rw [maximalPart_def, ← Finset.mem_def, Finset.mem_filter, Multiset.mem_toFinset, maximal_iff]
  simp

theorem mem_maximalPart_iff_forall {m : Multisegment} {s : Interval} :
    s ∈ maximalPart m ↔ s ∈ m ∧ ∀ t ∈ m, s ≤ t → s = t := by
  rw [mem_maximalPart_iff, maximal_iff]

theorem nodup_maximalPart (m : Multisegment) : (maximalPart m).Nodup :=
  Finset.nodup _

theorem mem_of_mem_maximalPart {m : Multisegment} {s : Interval} (hs : s ∈ maximalPart m) :
    s ∈ m :=
  (mem_maximalPart_iff.mp hs).prop

theorem eq_of_mem_maximalPart_of_le {m : Multisegment} {s t : Interval}
    (hs : s ∈ maximalPart m) (ht : t ∈ m) (hle : s ≤ t) :
    s = t :=
  (mem_maximalPart_iff.mp hs).eq_of_le ht hle

/-- The multiplicity of `s` in `maximalPart m` is `1` when `s` is inclusion-maximal in `m` and `0`
otherwise. -/
theorem count_maximalPart (m : Multisegment) (s : Interval) :
    (maximalPart m).count s = if Maximal (· ∈ m) s then 1 else 0 := by
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (nodup_maximalPart m) (mem_maximalPart_iff.mpr h)
  · exact Multiset.count_eq_zero_of_notMem (mt mem_maximalPart_iff.mp h)

theorem maximalPart_le (m : Multisegment) : maximalPart m ≤ m := by
  rw [Multiset.le_iff_count]
  intro s
  rw [count_maximalPart]
  split_ifs with h
  · exact Nat.succ_le_of_lt (Multiset.count_pos.mpr h.prop)
  · exact Nat.zero_le _

/-- Distinct intervals in `maximalPart m` are incomparable under set inclusion. -/
theorem isAntichain_maximalPart (m : Multisegment) :
    IsAntichain (· ≤ ·) {s : Interval | s ∈ maximalPart m} := by
  have hset : {s : Interval | s ∈ maximalPart m} = {s : Interval | Maximal (· ∈ m) s} := by
    ext s
    exact mem_maximalPart_iff
  rw [hset]
  exact setOfPred_maximal_antichain (· ∈ m)

/-- Every occurrence in `m` is contained in some inclusion-maximal interval belonging to
`maximalPart m`. -/
theorem exists_mem_maximalPart_ge {m : Multisegment} {s : Interval} (hs : s ∈ m) :
    ∃ t ∈ maximalPart m, s ≤ t := by
  obtain ⟨t, hst, htmax⟩ := m.toFinset.exists_le_maximal (Multiset.mem_toFinset.mpr hs)
  refine ⟨t, mem_maximalPart_iff.mpr ?_, hst⟩
  simpa [Maximal] using htmax

@[simp]
theorem maximalPart_zero : maximalPart 0 = 0 := by
  ext s
  rw [count_maximalPart]
  simp

@[simp]
theorem maximalPart_singleton (s : Interval) : maximalPart {s} = {s} := by
  ext t
  by_cases hts : t = s <;> simp [hts, count_maximalPart, maximal_iff]

@[simp]
theorem maximalPart_eq_zero_iff {m : Multisegment} : maximalPart m = 0 ↔ m = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra hm
  obtain ⟨s, hs⟩ := Multiset.exists_mem_of_ne_zero hm
  obtain ⟨t, ht, -⟩ := exists_mem_maximalPart_ge hs
  rw [h] at ht
  exact Multiset.notMem_zero t ht

theorem maximalPart_ne_zero_iff {m : Multisegment} : maximalPart m ≠ 0 ↔ m ≠ 0 :=
  not_congr maximalPart_eq_zero_iff

/-- Subtract `maximalPart m` from `m`, removing one copy of each distinct inclusion-maximal interval
and retaining all other occurrences. -/
def remainder (m : Multisegment) : Multisegment :=
  m - maximalPart m

theorem remainder_def (m : Multisegment) : remainder m = m - maximalPart m :=
  (rfl)

@[simp]
theorem remainder_add_maximalPart (m : Multisegment) :
    remainder m + maximalPart m = m :=
  Multiset.sub_add_cancel (maximalPart_le m)

@[simp]
theorem maximalPart_add_remainder (m : Multisegment) :
    maximalPart m + remainder m = m := by
  rw [add_comm, remainder_add_maximalPart]

theorem remainder_le (m : Multisegment) : remainder m ≤ m :=
  Multiset.sub_le_self m (maximalPart m)

theorem count_remainder (m : Multisegment) (s : Interval) :
    (remainder m).count s = if Maximal (· ∈ m) s then m.count s - 1 else m.count s := by
  rw [remainder_def, Multiset.count_sub, count_maximalPart]
  split_ifs <;> simp

@[simp]
theorem remainder_zero : remainder 0 = 0 := by
  rw [remainder_def, maximalPart_zero, tsub_zero]

@[simp]
theorem remainder_singleton (s : Interval) : remainder {s} = 0 := by
  simp [remainder_def]

theorem card_maximalPart_add_card_remainder (m : Multisegment) :
    (maximalPart m).card + (remainder m).card = m.card := by
  rw [← Multiset.card_add, maximalPart_add_remainder]

theorem totalLength_maximalPart_add_totalLength_remainder (m : Multisegment) :
    totalLength (maximalPart m) + totalLength (remainder m) = totalLength m := by
  rw [← totalLength_add, maximalPart_add_remainder]

theorem degreeDimension_maximalPart_add_degreeDimension_remainder (m : Multisegment) (a : ℤ) :
    degreeDimension (maximalPart m) a + degreeDimension (remainder m) a =
      degreeDimension m a := by
  rw [← degreeDimension_add, maximalPart_add_remainder]

/-- Peeling `maximalPart m` strictly decreases `totalLength` whenever `m` is nonempty. -/
theorem totalLength_remainder_lt {m : Multisegment} (hm : m ≠ 0) :
    totalLength (remainder m) < totalLength m := by
  have hpos : 0 < totalLength (maximalPart m) :=
    totalLength_pos_iff.mpr (maximalPart_ne_zero_iff.mpr hm)
  have hsum := totalLength_maximalPart_add_totalLength_remainder m
  omega

/-- Inclusion maximality commutes with integer translation. -/
theorem maximal_mem_shift_iff {m : Multisegment} {c : ℤ} {s : Interval} :
    Maximal (· ∈ shift m c) s ↔ Maximal (· ∈ m) (s.shift (-c)) := by
  simp only [maximal_iff, mem_shift_iff]
  refine and_congr_right fun _ => ⟨fun h t ht hle => ?_, fun h t ht hle => ?_⟩
  · have ht' : (t.shift c).shift (-c) ∈ m := by simpa using ht
    have hle' : s ≤ t.shift c := by simpa using NonemptyInterval.shift_mono c hle
    have heq := congrArg (fun u : Interval => u.shift (-c)) (h ht' hle')
    simpa using heq
  · have hle' : s.shift (-c) ≤ t.shift (-c) := NonemptyInterval.shift_mono (-c) hle
    have heq := congrArg (fun u : Interval => u.shift c) (h ht hle')
    simpa using heq

/-- `maximalPart` commutes with integer translation. -/
theorem maximalPart_shift (m : Multisegment) (c : ℤ) :
    maximalPart (shift m c) = shift (maximalPart m) c := by
  ext s
  simp [count_maximalPart, count_shift, maximal_mem_shift_iff]

/-- `remainder` commutes with integer translation. -/
theorem remainder_shift (m : Multisegment) (c : ℤ) :
    remainder (shift m c) = shift (remainder m) c := by
  rw [remainder_def, remainder_def, shift_sub, maximalPart_shift]

/-- A segment `t` is inclusion-maximal in `rightTruncate m` if and only if `t.extendRight` is
inclusion-maximal in `m`: nonsingleton segments preserve and reflect inclusion under shortening, and
no singleton segment can contain `t.extendRight`. -/
theorem maximal_mem_rightTruncate_iff {m : Multisegment} {t : Interval} :
    Maximal (· ∈ rightTruncate m) t ↔ Maximal (· ∈ m) t.extendRight := by
  simp only [maximal_iff, mem_rightTruncate_iff]
  refine and_congr_right fun _ => ⟨fun h u hu hle => ?_, fun h v hv hle => ?_⟩
  · cases hshort : u.shorten with
    | none =>
      exact (NonemptyInterval.not_extendRight_le_of_fst_eq_snd
        (NonemptyInterval.shorten_eq_none_iff.mp hshort) hle).elim
    | some v =>
      have huv : u = v.extendRight := NonemptyInterval.shorten_eq_some_iff.mp hshort
      subst huv
      rw [h hu (NonemptyInterval.extendRight_le_extendRight.mp hle)]
  · exact NonemptyInterval.extendRight_inj.mp
      (h hv (NonemptyInterval.extendRight_le_extendRight.mpr hle))

/-- Right truncation commutes with taking the one-copy maximal part (Atobe–Kondo–Yasuda,
Lemma 3.6). -/
theorem maximalPart_rightTruncate (m : Multisegment) :
    maximalPart (rightTruncate m) = rightTruncate (maximalPart m) := by
  ext t
  rw [count_maximalPart, count_rightTruncate, count_maximalPart]
  exact ite_congr (propext maximal_mem_rightTruncate_iff) (fun _ => rfl) (fun _ => rfl)

/-- Right truncation commutes with taking the multiplicity-sensitive maximal-peeling remainder
(Atobe–Kondo–Yasuda, Lemma 3.6). -/
theorem remainder_rightTruncate (m : Multisegment) :
    remainder (rightTruncate m) = rightTruncate (remainder m) := by
  rw [remainder_def, remainder_def, rightTruncate_sub, maximalPart_rightTruncate]

end TauCeti.Multisegment
