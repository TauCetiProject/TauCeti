/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import TauCeti.Order.Chain
public import TauCeti.RepresentationTheory.Multisegment.MaximalPeeling

/-!
# Adjacent cut multisegments, weighted inclusion chains, and peeling decrement

For an integer multisegment `m` and an integer degree `a : ℤ`, the adjacent cut multisegment
`TauCeti.Multisegment.cutPart m a` retains every occurrence of `m` meeting `a` or `a + 1` with its
full multiplicity in `m`. An inclusion chain in its finite support is a `Finset` of pairwise
inclusion-comparable intervals (`TauCeti.Multisegment.IsInclusionChain`), and
`TauCeti.Multisegment.chainWeight m a` is the maximum multiplicity-weighted size
`∑ s ∈ A, (cutPart m a).count s` over all inclusion chains `A` in `(cutPart m a).toFinset`.

Under the canonical maximal decomposition `m = maximalPart m + remainder m`, distinct intervals in
`maximalPart m` form an inclusion antichain of multiplicity `1`, while every occurrence in
`remainder m` is contained in some member of `maximalPart m`. Consequently:

* when `cutPart m a = 0`, all three chain weights `chainWeight m a`,
  `chainWeight (maximalPart m) a`, and `chainWeight (remainder m) a` vanish;
* when `cutPart m a ≠ 0`, `chainWeight (maximalPart m) a = 1` and
  `chainWeight m a = chainWeight (remainder m) a + 1`;
* unconditionally for every `m` and `a`,
  `chainWeight (maximalPart m) a + chainWeight (remainder m) a = chainWeight m a`.

## Main definitions and results

* `TauCeti.Multisegment.cutPart`: occurrences of `m` containing `a` or `a + 1`.
* `TauCeti.Multisegment.IsInclusionChain`: pairwise inclusion comparability on `Finset Interval`.
* `TauCeti.Multisegment.chainWeight`: maximum multiplicity-weighted inclusion-chain size at cut `a`.
* `TauCeti.Multisegment.exists_isInclusionChain_sum_eq_chainWeight`: attainment of `chainWeight m a`
  on an inclusion chain in `(cutPart m a).toFinset`.
* `TauCeti.Multisegment.chainWeight_maximalPart_eq_one`: if `cutPart m a ≠ 0`, then
  `chainWeight (maximalPart m) a = 1`.
* `TauCeti.Multisegment.chainWeight_eq_chainWeight_remainder_add_one`: if `cutPart m a ≠ 0`, then
  `chainWeight m a = chainWeight (remainder m) a + 1`.
* `TauCeti.Multisegment.chainWeight_maximalPart_add_chainWeight_remainder`: additivity of
  `chainWeight` across the canonical maximal split for every `m` and `a`.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24 (§3.3, Proposition 3.7,
  pp. 19–20; proof of Proposition 2.7, pp. 21–22).
-/

public section

open Finset

namespace TauCeti.Multisegment

/-! ### Adjacent cut multisegments -/

/-- Retain every occurrence of `m` containing `a` or `a + 1`, with its full multiplicity in `m`. -/
def cutPart (m : Multisegment) (a : ℤ) : Multisegment :=
  m.filter fun s => a ∈ s ∨ a + 1 ∈ s

theorem cutPart_def (m : Multisegment) (a : ℤ) :
    cutPart m a = m.filter fun s => a ∈ s ∨ a + 1 ∈ s :=
  (rfl)

theorem count_cutPart (m : Multisegment) (a : ℤ) (s : Interval) :
    (cutPart m a).count s = if a ∈ s ∨ a + 1 ∈ s then m.count s else 0 := by
  simp [cutPart_def, Multiset.count_filter]

@[simp]
theorem mem_cutPart_iff {m : Multisegment} {a : ℤ} {s : Interval} :
    s ∈ cutPart m a ↔ s ∈ m ∧ (a ∈ s ∨ a + 1 ∈ s) := by
  simp [cutPart_def]

/-- Any segment in `m₂` containing a member of `cutPart m₁ a` belongs to `cutPart m₂ a`. -/
theorem mem_cutPart_of_le {m₁ m₂ : Multisegment} {a : ℤ} {s t : Interval}
    (hs : s ∈ cutPart m₁ a) (ht : t ∈ m₂) (hst : s ≤ t) :
    t ∈ cutPart m₂ a := by
  rw [mem_cutPart_iff] at hs ⊢
  have hsub := NonemptyInterval.coe_subset_coe.mpr hst
  exact ⟨ht, hs.2.imp (fun ha => hsub ha) (fun ha1 => hsub ha1)⟩

@[simp]
theorem cutPart_zero (a : ℤ) : cutPart 0 a = 0 := by
  simp [cutPart_def]

theorem cutPart_singleton (s : Interval) (a : ℤ) :
    cutPart {s} a = if a ∈ s ∨ a + 1 ∈ s then {s} else 0 := by
  simp [cutPart_def, Multiset.filter_singleton]

@[simp]
theorem cutPart_add (m₁ m₂ : Multisegment) (a : ℤ) :
    cutPart (m₁ + m₂) a = cutPart m₁ a + cutPart m₂ a := by
  simp [cutPart_def]

theorem cutPart_sub (m₁ m₂ : Multisegment) (a : ℤ) :
    cutPart (m₁ - m₂) a = cutPart m₁ a - cutPart m₂ a :=
  Multiset.filter_sub _ m₁ m₂

theorem cutPart_le (m : Multisegment) (a : ℤ) : cutPart m a ≤ m :=
  Multiset.filter_le _ m

theorem cutPart_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) (a : ℤ) :
    cutPart m₁ a ≤ cutPart m₂ a :=
  Multiset.filter_le_filter _ h

@[simp]
theorem cutPart_maximalPart_add_cutPart_remainder (m : Multisegment) (a : ℤ) :
    cutPart (maximalPart m) a + cutPart (remainder m) a = cutPart m a := by
  rw [← cutPart_add, maximalPart_add_remainder]

/-- The cut of `maximalPart m` at `a` vanishes if and only if the cut of `m` at `a` vanishes,
because every segment in `cutPart m a` is shadowed by a member of `maximalPart m` that still meets
`{a, a + 1}`. -/
@[simp]
theorem cutPart_maximalPart_eq_zero_iff {m : Multisegment} {a : ℤ} :
    cutPart (maximalPart m) a = 0 ↔ cutPart m a = 0 := by
  refine ⟨fun h => ?_, fun h => Multiset.le_zero.mp (h ▸ cutPart_mono (maximalPart_le m) a)⟩
  by_contra hne
  obtain ⟨s, hs⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, ht, hst⟩ := exists_mem_maximalPart_ge (mem_cutPart_iff.mp hs).1
  have htcut : t ∈ cutPart (maximalPart m) a := mem_cutPart_of_le hs ht hst
  rw [h] at htcut
  exact Multiset.notMem_zero t htcut

theorem cutPart_maximalPart_ne_zero_iff {m : Multisegment} {a : ℤ} :
    cutPart (maximalPart m) a ≠ 0 ↔ cutPart m a ≠ 0 :=
  not_congr cutPart_maximalPart_eq_zero_iff

theorem cutPart_remainder_eq_zero_of_eq_zero {m : Multisegment} {a : ℤ} (h : cutPart m a = 0) :
    cutPart (remainder m) a = 0 :=
  Multiset.le_zero.mp (h ▸ cutPart_mono (remainder_le m) a)

/-- Taking the adjacent cut commutes with integer translation of segments and degrees. -/
theorem cutPart_shift (m : Multisegment) (a c : ℤ) :
    cutPart (shift m c) (a + c) = shift (cutPart m a) c := by
  ext s
  rw [count_cutPart, count_shift, count_shift, count_cutPart]
  have hiff : (a + c ∈ s ∨ a + c + 1 ∈ s) ↔ (a ∈ s.shift (-c) ∨ a + 1 ∈ s.shift (-c)) := by
    simp only [NonemptyInterval.mem_shift_iff, sub_neg_eq_add]
    exact or_congr_right (by rw [add_right_comm])
  exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)

/-! ### Inclusion chains of intervals -/

/-- A finite set of distinct intervals is an inclusion chain when any two of its members are
comparable under set inclusion. -/
def IsInclusionChain (A : Finset Interval) : Prop :=
  IsChain (· ≤ ·) (A : Set Interval)

/-- Pairwise inclusion comparability on a finite set of intervals is computably decidable. -/
instance instDecidableIsInclusionChain (A : Finset Interval) :
    Decidable (IsInclusionChain A) :=
  decidable_of_iff' (∀ s ∈ A, ∀ t ∈ A, s ≠ t → s ≤ t ∨ t ≤ s) <| by
    simp [IsInclusionChain, IsChain, Set.Pairwise]

theorem isInclusionChain_def (A : Finset Interval) :
    IsInclusionChain A ↔ IsChain (· ≤ ·) (A : Set Interval) :=
  Iff.rfl

theorem isInclusionChain_iff_forall {A : Finset Interval} :
    IsInclusionChain A ↔ ∀ s ∈ A, ∀ t ∈ A, s ≤ t ∨ t ≤ s :=
  ⟨fun h _ hs _ ht => h.total hs ht, fun h s hs t ht _ => h s hs t ht⟩

@[simp]
theorem isInclusionChain_empty : IsInclusionChain ∅ := by
  simp [IsInclusionChain]

@[simp]
theorem isInclusionChain_singleton (s : Interval) : IsInclusionChain {s} := by
  simp [IsInclusionChain]

theorem isInclusionChain_pair {s t : Interval} :
    IsInclusionChain {s, t} ↔ s ≤ t ∨ t ≤ s := by
  rw [isInclusionChain_iff_forall]
  refine ⟨fun h => h s (by simp) t (by simp), fun h u hu v hv => ?_⟩
  rcases Finset.mem_insert.mp hu with rfl | hu' <;>
    rcases Finset.mem_insert.mp hv with rfl | hv'
  · exact Or.inl le_rfl
  · rw [Finset.mem_singleton.mp hv']
    exact h
  · rw [Finset.mem_singleton.mp hu']
    exact h.symm
  · rw [Finset.mem_singleton.mp hu', Finset.mem_singleton.mp hv']
    exact Or.inl le_rfl

theorem IsInclusionChain.subset {A B : Finset Interval} (hB : IsInclusionChain B) (hAB : A ⊆ B) :
    IsInclusionChain A :=
  hB.mono (Finset.coe_subset.mpr hAB)

theorem IsInclusionChain.insert_of_forall_le {A : Finset Interval} {t : Interval}
    (hA : IsInclusionChain A) (ht : ∀ s ∈ A, s ≤ t) :
    IsInclusionChain (insert t A) := by
  rw [isInclusionChain_iff_forall] at hA ⊢
  intro u hu v hv
  rcases Finset.mem_insert.mp hu with rfl | hu' <;>
    rcases Finset.mem_insert.mp hv with rfl | hv'
  · exact Or.inl le_rfl
  · exact Or.inr (ht v hv')
  · exact Or.inl (ht u hu')
  · exact hA u hu' v hv'

theorem IsInclusionChain.card_le_one_of_isAntichain {A : Finset Interval}
    (hchain : IsInclusionChain A) (hanti : IsAntichain (· ≤ ·) (A : Set Interval)) :
    #A ≤ 1 := by
  have hsub : (A : Set Interval).Subsingleton :=
    subsingleton_of_isChain_of_isAntichain hchain hanti
  exact Finset.card_le_one.mpr fun s hs t ht => hsub hs ht

/-! ### Multiplicity-weighted chain maximum at an adjacent cut -/

/-- Maximum multiplicity-weighted size of an inclusion chain in `(cutPart m a).toFinset`, counting
all copies of each chosen interval in `cutPart m a` (Atobe–Kondo–Yasuda, Proposition 3.7). -/
def chainWeight (m : Multisegment) (a : ℤ) : ℕ :=
  ((cutPart m a).toFinset.powerset.filter IsInclusionChain).sup
    fun A => ∑ s ∈ A, (cutPart m a).count s

theorem chainWeight_def (m : Multisegment) (a : ℤ) :
    chainWeight m a =
      ((cutPart m a).toFinset.powerset.filter IsInclusionChain).sup
        fun A => ∑ s ∈ A, (cutPart m a).count s :=
  (rfl)

/-- Every inclusion chain of intervals has cut multiplicity sum bounded by `chainWeight m a`
(elements outside `(cutPart m a).toFinset` contribute zero). -/
theorem sum_count_cutPart_le_chainWeight {m : Multisegment} {a : ℤ} {A : Finset Interval}
    (hA : IsInclusionChain A) :
    ∑ s ∈ A, (cutPart m a).count s ≤ chainWeight m a := by
  let B := A ∩ (cutPart m a).toFinset
  have hsum : ∑ s ∈ A, (cutPart m a).count s = ∑ s ∈ B, (cutPart m a).count s := by
    symm
    refine Finset.sum_subset Finset.inter_subset_left fun s hsA hsB => ?_
    have hsnot : s ∉ cutPart m a := fun hmem =>
      hsB (Finset.mem_inter.mpr ⟨hsA, Multiset.mem_toFinset.mpr hmem⟩)
    exact Multiset.count_eq_zero_of_notMem hsnot
  rw [hsum, chainWeight_def]
  refine Finset.le_sup (f := fun C => ∑ s ∈ C, (cutPart m a).count s) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.inter_subset_right, hA.subset Finset.inter_subset_left⟩

theorem chainWeight_le_iff {m : Multisegment} {a : ℤ} {n : ℕ} :
    chainWeight m a ≤ n ↔
      ∀ A ⊆ (cutPart m a).toFinset, IsInclusionChain A →
        ∑ s ∈ A, (cutPart m a).count s ≤ n := by
  rw [chainWeight_def, Finset.sup_le_iff]
  simp only [Finset.mem_filter, Finset.mem_powerset, and_imp]

theorem count_cutPart_le_chainWeight (m : Multisegment) (a : ℤ) (s : Interval) :
    (cutPart m a).count s ≤ chainWeight m a := by
  simpa using sum_count_cutPart_le_chainWeight (m := m) (a := a) (isInclusionChain_singleton s)

/-- Some inclusion chain in `(cutPart m a).toFinset` attains `chainWeight m a`. -/
theorem exists_isInclusionChain_sum_eq_chainWeight (m : Multisegment) (a : ℤ) :
    ∃ A ⊆ (cutPart m a).toFinset,
      IsInclusionChain A ∧ ∑ s ∈ A, (cutPart m a).count s = chainWeight m a := by
  have hne : ((cutPart m a).toFinset.powerset.filter IsInclusionChain).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, isInclusionChain_empty⟩⟩
  obtain ⟨A, hA, heq⟩ :=
    Finset.exists_mem_eq_sup _ hne (fun C => ∑ s ∈ C, (cutPart m a).count s)
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, heq.symm⟩

/-- `chainWeight m a` never exceeds the total occurrence count `(cutPart m a).card`. -/
theorem chainWeight_le_card_cutPart (m : Multisegment) (a : ℤ) :
    chainWeight m a ≤ (cutPart m a).card := by
  rw [chainWeight_le_iff]
  intro A hA _
  calc
    ∑ s ∈ A, (cutPart m a).count s ≤ ∑ s ∈ (cutPart m a).toFinset, (cutPart m a).count s :=
      Finset.sum_le_sum_of_subset hA
    _ = (cutPart m a).card := Multiset.toFinset_sum_count_eq (cutPart m a)

@[simp]
theorem chainWeight_eq_zero_iff {m : Multisegment} {a : ℤ} :
    chainWeight m a = 0 ↔ cutPart m a = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hne
    obtain ⟨s, hs⟩ := Multiset.exists_mem_of_ne_zero hne
    have hpos : 0 < (cutPart m a).count s := Multiset.count_pos.mpr hs
    have hle := count_cutPart_le_chainWeight m a s
    omega
  · exact Nat.eq_zero_of_le_zero ((chainWeight_le_card_cutPart m a).trans (by simp [h]))

theorem chainWeight_pos_iff {m : Multisegment} {a : ℤ} :
    0 < chainWeight m a ↔ cutPart m a ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, not_iff_not, chainWeight_eq_zero_iff]

@[simp]
theorem chainWeight_zero (a : ℤ) : chainWeight 0 a = 0 := by
  simp

/-- `chainWeight` is subadditive across multisegment sums. -/
theorem chainWeight_add_le (m₁ m₂ : Multisegment) (a : ℤ) :
    chainWeight (m₁ + m₂) a ≤ chainWeight m₁ a + chainWeight m₂ a := by
  rw [chainWeight_le_iff]
  intro A _ hA
  calc
    ∑ s ∈ A, (cutPart (m₁ + m₂) a).count s
      = (∑ s ∈ A, (cutPart m₁ a).count s) + ∑ s ∈ A, (cutPart m₂ a).count s := by
          simp [cutPart_add, Finset.sum_add_distrib]
    _ ≤ chainWeight m₁ a + chainWeight m₂ a :=
          Nat.add_le_add (sum_count_cutPart_le_chainWeight hA)
            (sum_count_cutPart_le_chainWeight hA)

theorem chainWeight_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) (a : ℤ) :
    chainWeight m₁ a ≤ chainWeight m₂ a := by
  rw [chainWeight_le_iff]
  intro A _ hA
  calc
    ∑ s ∈ A, (cutPart m₁ a).count s ≤ ∑ s ∈ A, (cutPart m₂ a).count s :=
      Finset.sum_le_sum fun s _ => Multiset.count_le_of_le s (cutPart_mono h a)
    _ ≤ chainWeight m₂ a := sum_count_cutPart_le_chainWeight hA

private theorem chainWeight_shift_le (m : Multisegment) (a c : ℤ) :
    chainWeight (shift m c) (a + c) ≤ chainWeight m a := by
  rw [chainWeight_le_iff]
  intro A _ hA
  let e : Interval ↪ Interval := ⟨fun s => s.shift (-c), NonemptyInterval.shift_injective (-c)⟩
  have hAe : IsInclusionChain (A.map e) := by
    rw [isInclusionChain_iff_forall] at hA ⊢
    intro u hu v hv
    rcases Finset.mem_map.mp hu with ⟨s, hs, rfl⟩
    rcases Finset.mem_map.mp hv with ⟨t, ht, rfl⟩
    exact (hA s hs t ht).imp (NonemptyInterval.shift_mono (-c)) (NonemptyInterval.shift_mono (-c))
  calc
    ∑ s ∈ A, (cutPart (shift m c) (a + c)).count s
      = ∑ s ∈ A, (cutPart m a).count (e s) := by
          simp [cutPart_shift, count_shift, e]
    _ = ∑ u ∈ A.map e, (cutPart m a).count u :=
          (Finset.sum_map A e fun u => (cutPart m a).count u).symm
    _ ≤ chainWeight m a := sum_count_cutPart_le_chainWeight hAe

/-- `chainWeight` is invariant under simultaneous integer translation of segments and the cut. -/
theorem chainWeight_shift (m : Multisegment) (a c : ℤ) :
    chainWeight (shift m c) (a + c) = chainWeight m a := by
  refine le_antisymm (chainWeight_shift_le m a c) ?_
  have h := chainWeight_shift_le (shift m c) (a + c) (-c)
  simpa using h

/-! ### Behavior of `chainWeight` under canonical maximal peeling -/

theorem chainWeight_maximalPart_eq_zero_iff {m : Multisegment} {a : ℤ} :
    chainWeight (maximalPart m) a = 0 ↔ cutPart m a = 0 := by
  rw [chainWeight_eq_zero_iff, cutPart_maximalPart_eq_zero_iff]

theorem chainWeight_remainder_eq_zero_of_eq_zero {m : Multisegment} {a : ℤ}
    (h : cutPart m a = 0) :
    chainWeight (remainder m) a = 0 :=
  chainWeight_eq_zero_iff.mpr (cutPart_remainder_eq_zero_of_eq_zero h)

/-- An inclusion chain in `maximalPart m` has multiplicity-weighted cut sum at most `1`, since
`maximalPart m` is a multiplicity-free inclusion antichain. -/
theorem chainWeight_maximalPart_le_one (m : Multisegment) (a : ℤ) :
    chainWeight (maximalPart m) a ≤ 1 := by
  rw [chainWeight_le_iff]
  intro A hAsub hAchain
  have hanti : IsAntichain (· ≤ ·) (A : Set Interval) := by
    refine (isAntichain_maximalPart m).subset fun s hs => ?_
    have hmem : s ∈ cutPart (maximalPart m) a := Multiset.mem_toFinset.mp (hAsub hs)
    exact Multiset.mem_of_le (cutPart_le (maximalPart m) a) hmem
  have hcard : #A ≤ 1 := hAchain.card_le_one_of_isAntichain hanti
  have hnodup : (cutPart (maximalPart m) a).Nodup :=
    Multiset.nodup_of_le (cutPart_le (maximalPart m) a) (nodup_maximalPart m)
  calc
    ∑ s ∈ A, (cutPart (maximalPart m) a).count s ≤ ∑ _s ∈ A, 1 :=
      Finset.sum_le_sum fun s _ => Multiset.nodup_iff_count_le_one.mp hnodup s
    _ = #A := by simp
    _ ≤ 1 := hcard

/-- When the cut `cutPart m a` is nonempty, `maximalPart m` contributes chain weight `1` at `a`
(Atobe–Kondo–Yasuda, proof of Proposition 2.7, pp. 21–22). -/
theorem chainWeight_maximalPart_eq_one {m : Multisegment} {a : ℤ} (h : cutPart m a ≠ 0) :
    chainWeight (maximalPart m) a = 1 := by
  have hpos : 0 < chainWeight (maximalPart m) a :=
    chainWeight_pos_iff.mpr (cutPart_maximalPart_ne_zero_iff.mpr h)
  have hle := chainWeight_maximalPart_le_one m a
  omega

/-- Peeling `maximalPart m` decreases `chainWeight m a` by exactly `1` whenever the adjacent cut
`cutPart m a` is nonempty (Atobe–Kondo–Yasuda, proof of Proposition 2.7, pp. 21–22). -/
theorem chainWeight_eq_chainWeight_remainder_add_one {m : Multisegment} {a : ℤ}
    (h : cutPart m a ≠ 0) :
    chainWeight m a = chainWeight (remainder m) a + 1 := by
  refine le_antisymm ?_ ?_
  · calc
      chainWeight m a = chainWeight (remainder m + maximalPart m) a := by
        rw [remainder_add_maximalPart]
      _ ≤ chainWeight (remainder m) a + chainWeight (maximalPart m) a :=
        chainWeight_add_le (remainder m) (maximalPart m) a
      _ = chainWeight (remainder m) a + 1 := by
        rw [chainWeight_maximalPart_eq_one h]
  · obtain ⟨A, hAsub, hAchain, hAsum⟩ :=
      exists_isInclusionChain_sum_eq_chainWeight (remainder m) a
    rcases A.eq_empty_or_nonempty with rfl | hAne
    · have hzero : chainWeight (remainder m) a = 0 := by simpa using hAsum.symm
      have hpos : 0 < chainWeight m a := chainWeight_pos_iff.mpr h
      omega
    · obtain ⟨s₀, hs₀great⟩ :=
        hAchain.exists_isGreatest A.finite_toSet (Finset.coe_nonempty.mpr hAne)
      have hs₀cut : s₀ ∈ cutPart (remainder m) a := Multiset.mem_toFinset.mp (hAsub hs₀great.1)
      have hs₀m : s₀ ∈ m :=
        Multiset.mem_of_le (remainder_le m) (mem_cutPart_iff.mp hs₀cut).1
      obtain ⟨t₀, ht₀max, hs₀t₀⟩ := exists_mem_maximalPart_ge hs₀m
      have ht₀cut : t₀ ∈ cutPart (maximalPart m) a := mem_cutPart_of_le hs₀cut ht₀max hs₀t₀
      let B := insert t₀ A
      have hBchain : IsInclusionChain B :=
        hAchain.insert_of_forall_le fun s hs => (hs₀great.2 hs).trans hs₀t₀
      have hmax_pos : 1 ≤ ∑ s ∈ B, (cutPart (maximalPart m) a).count s :=
        (Nat.succ_le_of_lt (Multiset.count_pos.mpr ht₀cut)).trans <|
          Finset.single_le_sum (f := fun s => (cutPart (maximalPart m) a).count s)
            (fun _ _ => Nat.zero_le _) (Finset.mem_insert_self t₀ A)
      have hrem_le : chainWeight (remainder m) a ≤ ∑ s ∈ B, (cutPart (remainder m) a).count s :=
        hAsum ▸ Finset.sum_le_sum_of_subset (Finset.subset_insert t₀ A)
      calc
        chainWeight (remainder m) a + 1
          ≤ (∑ s ∈ B, (cutPart (remainder m) a).count s) +
              ∑ s ∈ B, (cutPart (maximalPart m) a).count s :=
            Nat.add_le_add hrem_le hmax_pos
        _ = ∑ s ∈ B, (cutPart m a).count s := by
            rw [add_comm, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← Multiset.count_add, cutPart_maximalPart_add_cutPart_remainder]
        _ ≤ chainWeight m a := sum_count_cutPart_le_chainWeight hBchain

/-- `chainWeight` is additive across the canonical maximal split `m = maximalPart m + remainder m`
for every multisegment `m` and every cut `a : ℤ`. -/
theorem chainWeight_maximalPart_add_chainWeight_remainder (m : Multisegment) (a : ℤ) :
    chainWeight (maximalPart m) a + chainWeight (remainder m) a = chainWeight m a := by
  by_cases h : cutPart m a = 0
  · simp [chainWeight_eq_zero_iff.mpr h, chainWeight_maximalPart_eq_zero_iff.mpr h,
      chainWeight_remainder_eq_zero_of_eq_zero h]
  · rw [chainWeight_maximalPart_eq_one h, chainWeight_eq_chainWeight_remainder_add_one h, add_comm]

end TauCeti.Multisegment
