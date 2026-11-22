/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Chain
public import TauCeti.RepresentationTheory.Quiver.Multisegment.MaximalPart
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset

/-!
# Adjacent cut multisegments and weighted inclusion chains

For an integer degree `a`, the adjacent cut `cutPart m a` retains every occurrence of a
multisegment `m` containing `a` or `a + 1`, preserving multiplicities. An inclusion chain is a
finite set of distinct integral intervals forming a chain under interval inclusion
(`IsChain (· ≤ ·)`), and the chain weight `chainWeight m a` is the maximum multiplicity-weighted
sum over inclusion chains supported in `cutPart m a`.

This file builds the API for `cutPart` and `chainWeight`, and proves the peeling decrement and
additivity identities for the canonical maximal decomposition: whenever `cutPart m a ≠ 0`,
`chainWeight (maximalPart m) a = 1` and `chainWeight m a = chainWeight (remainder m) a + 1`,
yielding the unconditional identity
`chainWeight m a = chainWeight (maximalPart m) a + chainWeight (remainder m) a`.

## Main definitions

* `TauCeti.Multisegment.cutPart`: submultisegment of occurrences containing `a` or `a + 1`.
* `TauCeti.Multisegment.IsInclusionChain`: finite sets of intervals pairwise comparable by
  inclusion (`IsChain (· ≤ ·)`).
* `TauCeti.Multisegment.chainWeight`: maximum multiplicity-weighted inclusion-chain sum in
  `cutPart m a`.

## Main results

* `TauCeti.Multisegment.exists_isInclusionChain_weight_eq`: `chainWeight m a` is attained by an
  inclusion chain in `(cutPart m a).toFinset`.
* `TauCeti.Multisegment.chainWeight_add_le`: `chainWeight` is subadditive in the multisegment.
* `TauCeti.Multisegment.chainWeight_maximalPart_of_cutPart_ne_zero`: on any nonempty cut,
  `chainWeight (maximalPart m) a = 1`.
* `TauCeti.Multisegment.chainWeight_eq_chainWeight_remainder_add_one`: on any nonempty cut,
  peeling `maximalPart m` lowers `chainWeight m a` by exactly `1`.
* `TauCeti.Multisegment.chainWeight_maximalPart_add_remainder`: unconditional additivity
  `chainWeight m a = chainWeight (maximalPart m) a + chainWeight (remainder m) a`.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, Proposition 2.7,
  §3.3, Proposition 3.7.
-/

public section

namespace TauCeti.Multisegment

/-! ### Adjacent cut multisegments -/

/-- The full submultisegment of occurrences in `m` containing `a` or `a + 1`. -/
def cutPart (m : Multisegment) (a : ℤ) : Multisegment :=
  m.filter fun s => a ∈ s ∨ a + 1 ∈ s

/-- An interval occurs in `cutPart m a` if and only if it occurs in `m` and contains `a` or
`a + 1`. -/
theorem mem_cutPart_iff {m : Multisegment} {a : ℤ} {s : IntInterval} :
    s ∈ cutPart m a ↔ s ∈ m ∧ (a ∈ s ∨ a + 1 ∈ s) :=
  Multiset.mem_filter

/-- Retained intervals keep their full multiplicity in `cutPart m a`; omitted intervals have
multiplicity `0`. -/
theorem count_cutPart (m : Multisegment) (a : ℤ) (s : IntInterval) :
    (cutPart m a).count s = if a ∈ s ∨ a + 1 ∈ s then m.count s else 0 :=
  Multiset.count_filter

/-- Every interval meeting `{a, a + 1}` keeps its full multiplicity in `cutPart m a`. -/
theorem count_cutPart_of_mem {m : Multisegment} {a : ℤ} {s : IntInterval}
    (hs : a ∈ s ∨ a + 1 ∈ s) : (cutPart m a).count s = m.count s :=
  Multiset.count_filter_of_pos hs

/-- `cutPart m a` is a submultiset of `m`. -/
theorem cutPart_le (m : Multisegment) (a : ℤ) : cutPart m a ≤ m :=
  Multiset.filter_le _ m

@[simp]
theorem cutPart_zero (a : ℤ) : cutPart 0 a = 0 :=
  Multiset.filter_zero _

@[simp]
theorem cutPart_add (m₁ m₂ : Multisegment) (a : ℤ) :
    cutPart (m₁ + m₂) a = cutPart m₁ a + cutPart m₂ a :=
  Multiset.filter_add _ m₁ m₂

/-- `cutPart` is monotone with respect to submultiset inclusion. -/
theorem cutPart_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) (a : ℤ) :
    cutPart m₁ a ≤ cutPart m₂ a :=
  Multiset.filter_le_filter _ h

/-- The cut of `m` decomposes as the sum of the cuts of `maximalPart m` and `remainder m`. -/
theorem cutPart_maximalPart_add_remainder (m : Multisegment) (a : ℤ) :
    cutPart (maximalPart m) a + cutPart (remainder m) a = cutPart m a := by
  rw [← cutPart_add, maximalPart_add_remainder]

/-- Integer translation reindexes cuts by the same shift. -/
@[simp]
theorem cutPart_shift_add (m : Multisegment) (a c : ℤ) :
    cutPart (shift m c) (a + c) = shift (cutPart m a) c := by
  apply Multiset.ext.mpr
  intro s
  rw [count_cutPart, count_shift, count_shift, count_cutPart]
  have hiff : (a + c ∈ s ∨ a + c + 1 ∈ s) ↔
      (a ∈ s.shift (-c) ∨ a + 1 ∈ s.shift (-c)) := by
    simp only [IntInterval.mem_shift_iff, sub_neg_eq_add]
    exact or_congr Iff.rfl (by rw [add_right_comm])
  simp [hiff]

/-- The cut of `maximalPart m` is empty if and only if the cut of `m` is empty. -/
theorem cutPart_maximalPart_eq_zero_iff (m : Multisegment) (a : ℤ) :
    cutPart (maximalPart m) a = 0 ↔ cutPart m a = 0 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨s, hs⟩ := Multiset.exists_mem_of_ne_zero hne
    obtain ⟨hsm, hcut⟩ := mem_cutPart_iff.mp hs
    obtain ⟨t, ht, hst⟩ := exists_le_mem_maximalPart hsm
    have hsub : (s : Set ℤ) ⊆ (t : Set ℤ) := NonemptyInterval.coe_subset_coe.mpr hst
    have htcut : t ∈ cutPart (maximalPart m) a :=
      mem_cutPart_iff.mpr ⟨ht, hcut.imp (fun ha => hsub ha) (fun ha => hsub ha)⟩
    simp [h] at htcut
  · intro h
    exact le_antisymm ((cutPart_mono (maximalPart_le m) a).trans h.le) (Multiset.zero_le _)

/-- If the cut of `m` is empty, then the cut of `remainder m` is also empty. -/
theorem cutPart_remainder_eq_zero_of_cutPart_eq_zero {m : Multisegment} {a : ℤ}
    (h : cutPart m a = 0) : cutPart (remainder m) a = 0 :=
  le_antisymm ((cutPart_mono (remainder_le m) a).trans h.le) (Multiset.zero_le _)

/-! ### Inclusion chains and weighted chain maxima -/

/-- A finite set of integral intervals is an inclusion chain when its elements form a chain under
interval inclusion. -/
abbrev IsInclusionChain (A : Finset IntInterval) : Prop :=
  IsChain (· ≤ ·) (A : Set IntInterval)

/-- The maximum multiplicity-weighted sum of an inclusion chain in `cutPart m a`. -/
def chainWeight (m : Multisegment) (a : ℤ) : ℕ :=
  ((cutPart m a).toFinset.powerset.filter IsInclusionChain).sup
    fun A => ∑ s ∈ A, (cutPart m a).count s

/-- The multiplicity-weighted sum over any inclusion chain is bounded above by `chainWeight m a`.
-/
theorem sum_count_le_chainWeight {m : Multisegment} {a : ℤ} {A : Finset IntInterval}
    (hA : IsInclusionChain A) :
    ∑ s ∈ A, (cutPart m a).count s ≤ chainWeight m a := by
  let A' : Finset IntInterval := A.filter (· ∈ cutPart m a)
  have hsum : ∑ s ∈ A, (cutPart m a).count s = ∑ s ∈ A', (cutPart m a).count s := by
    refine (Finset.sum_subset (Finset.filter_subset _ A) fun s hs hs' => ?_).symm
    have hnot : s ∉ cutPart m a := fun hmem => hs' (Finset.mem_filter.mpr ⟨hs, hmem⟩)
    exact Multiset.count_eq_zero.mpr hnot
  rw [hsum, chainWeight]
  refine Finset.le_sup (f := fun B => ∑ s ∈ B, (cutPart m a).count s) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun s hs => Multiset.mem_toFinset.mpr (Finset.mem_filter.mp hs).2,
    hA.mono (Finset.coe_subset.mpr (Finset.filter_subset _ A))⟩

/-- `chainWeight m a` is attained by some inclusion chain in the distinct support of `cutPart m a`.
-/
theorem exists_isInclusionChain_weight_eq (m : Multisegment) (a : ℤ) :
    ∃ A ⊆ (cutPart m a).toFinset, IsInclusionChain A ∧
      ∑ s ∈ A, (cutPart m a).count s = chainWeight m a := by
  have hne : ((cutPart m a).toFinset.powerset.filter IsInclusionChain).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      by simp [IsInclusionChain]⟩⟩
  obtain ⟨A, hA, hEq⟩ :=
    Finset.exists_mem_eq_sup _ hne fun B => ∑ s ∈ B, (cutPart m a).count s
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, hEq.symm⟩

/-- Upper-bound characterization of `chainWeight m a`. -/
theorem chainWeight_le_iff {m : Multisegment} {a : ℤ} {k : ℕ} :
    chainWeight m a ≤ k ↔
      ∀ A ⊆ (cutPart m a).toFinset, IsInclusionChain A →
        ∑ s ∈ A, (cutPart m a).count s ≤ k := by
  rw [chainWeight, Finset.sup_le_iff]
  constructor
  · intro h A hsub hchain
    exact h A (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hchain⟩)
  · intro h A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    exact h A hA.1 hA.2

/-- `chainWeight m a` is at most the total number of occurrences in `cutPart m a`. -/
theorem chainWeight_le_card_cutPart (m : Multisegment) (a : ℤ) :
    chainWeight m a ≤ (cutPart m a).card := by
  rw [chainWeight_le_iff]
  intro A hsub _
  calc ∑ s ∈ A, (cutPart m a).count s
      ≤ ∑ s ∈ (cutPart m a).toFinset, (cutPart m a).count s :=
        Finset.sum_le_sum_of_subset hsub
    _ = (cutPart m a).card := Multiset.toFinset_sum_count_eq (cutPart m a)

/-- `chainWeight m a` vanishes if and only if `cutPart m a` is empty. -/
@[simp]
theorem chainWeight_eq_zero_iff (m : Multisegment) (a : ℤ) :
    chainWeight m a = 0 ↔ cutPart m a = 0 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨s, hs⟩ := Multiset.exists_mem_of_ne_zero hne
    have hle : (cutPart m a).count s ≤ chainWeight m a := by
      simpa using sum_count_le_chainWeight (m := m) (a := a) (A := {s}) (by simp [IsInclusionChain])
    have hpos : 0 < (cutPart m a).count s := Multiset.count_pos.mpr hs
    omega
  · intro h
    have hle := chainWeight_le_card_cutPart m a
    rw [h, Multiset.card_zero] at hle
    omega

@[simp]
theorem chainWeight_zero (a : ℤ) : chainWeight 0 a = 0 :=
  (chainWeight_eq_zero_iff 0 a).mpr (cutPart_zero a)

/-- `chainWeight m a` is positive if and only if `cutPart m a` is nonempty. -/
theorem chainWeight_pos_iff (m : Multisegment) (a : ℤ) :
    0 < chainWeight m a ↔ cutPart m a ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, chainWeight_eq_zero_iff]

/-- `chainWeight` is monotone with respect to submultiset inclusion. -/
theorem chainWeight_mono {m₁ m₂ : Multisegment} (h : m₁ ≤ m₂) (a : ℤ) :
    chainWeight m₁ a ≤ chainWeight m₂ a := by
  obtain ⟨A, -, hA, hsum⟩ := exists_isInclusionChain_weight_eq m₁ a
  calc chainWeight m₁ a
      = ∑ s ∈ A, (cutPart m₁ a).count s := hsum.symm
    _ ≤ ∑ s ∈ A, (cutPart m₂ a).count s :=
        Finset.sum_le_sum fun s _ => Multiset.count_le_of_le s (cutPart_mono h a)
    _ ≤ chainWeight m₂ a := sum_count_le_chainWeight hA

/-- `chainWeight` is subadditive in the multisegment. -/
theorem chainWeight_add_le (m₁ m₂ : Multisegment) (a : ℤ) :
    chainWeight (m₁ + m₂) a ≤ chainWeight m₁ a + chainWeight m₂ a := by
  obtain ⟨A, -, hA, hsum⟩ := exists_isInclusionChain_weight_eq (m₁ + m₂) a
  calc chainWeight (m₁ + m₂) a
      = ∑ s ∈ A, (cutPart (m₁ + m₂) a).count s := hsum.symm
    _ = ∑ s ∈ A, (cutPart m₁ a).count s + ∑ s ∈ A, (cutPart m₂ a).count s := by
        simp_rw [cutPart_add, Multiset.count_add, Finset.sum_add_distrib]
    _ ≤ chainWeight m₁ a + chainWeight m₂ a :=
        add_le_add (sum_count_le_chainWeight hA) (sum_count_le_chainWeight hA)

/-- Integer translation reindexes `chainWeight` by the same shift. -/
@[simp]
theorem chainWeight_shift_add (m : Multisegment) (a c : ℤ) :
    chainWeight (shift m c) (a + c) = chainWeight m a := by
  have hmono : ∀ d : ℤ, Monotone (fun s : IntInterval => s.shift d) :=
    fun d _ _ => IntInterval.shift_le_shift_iff.mpr
  refine le_antisymm ?_ ?_
  · obtain ⟨A, -, hA, hsum⟩ := exists_isInclusionChain_weight_eq (shift m c) (a + c)
    have hA' : IsInclusionChain (A.image (·.shift (-c))) := by
      simpa only [IsInclusionChain, Finset.coe_image] using (hmono (-c)).isChain_image hA
    calc chainWeight (shift m c) (a + c)
        = ∑ s ∈ A, (cutPart (shift m c) (a + c)).count s := hsum.symm
      _ = ∑ s ∈ A, (cutPart m a).count (s.shift (-c)) := by
          simp_rw [cutPart_shift_add, count_shift]
      _ = ∑ t ∈ A.image (·.shift (-c)), (cutPart m a).count t :=
          (Finset.sum_image (f := fun t => (cutPart m a).count t)
            fun _ _ _ _ h => IntInterval.shift_injective (-c) h).symm
      _ ≤ chainWeight m a := sum_count_le_chainWeight hA'
  · obtain ⟨A, -, hA, hsum⟩ := exists_isInclusionChain_weight_eq m a
    have hA' : IsInclusionChain (A.image (·.shift c)) := by
      simpa only [IsInclusionChain, Finset.coe_image] using (hmono c).isChain_image hA
    calc chainWeight m a
        = ∑ s ∈ A, (cutPart m a).count s := hsum.symm
      _ = ∑ s ∈ A, (cutPart (shift m c) (a + c)).count (s.shift c) := by
          simp_rw [cutPart_shift_add, count_shift_shift]
      _ = ∑ t ∈ A.image (·.shift c), (cutPart (shift m c) (a + c)).count t :=
          (Finset.sum_image (f := fun t => (cutPart (shift m c) (a + c)).count t)
            fun _ _ _ _ h => IntInterval.shift_injective c h).symm
      _ ≤ chainWeight (shift m c) (a + c) := sum_count_le_chainWeight hA'

/-! ### Peeling decrement and additivity -/

/-- Every inclusion chain in `cutPart (maximalPart m) a` has weight at most `1`. -/
theorem chainWeight_maximalPart_le_one (m : Multisegment) (a : ℤ) :
    chainWeight (maximalPart m) a ≤ 1 := by
  rw [chainWeight_le_iff]
  intro A hsub hchain
  have hcard : A.card ≤ 1 := Finset.card_le_one.mpr fun s hs t ht => by
    have hsm : s ∈ maximalPart m := (mem_cutPart_iff.mp (Multiset.mem_toFinset.mp (hsub hs))).1
    have htm : t ∈ maximalPart m := (mem_cutPart_iff.mp (Multiset.mem_toFinset.mp (hsub ht))).1
    rcases hchain.total hs ht with hle | hle
    · exact eq_of_mem_maximalPart_of_le hsm htm hle
    · exact (eq_of_mem_maximalPart_of_le htm hsm hle).symm
  calc ∑ s ∈ A, (cutPart (maximalPart m) a).count s
      ≤ ∑ _s ∈ A, 1 := Finset.sum_le_sum fun s _ =>
        (Multiset.count_le_of_le s (cutPart_le (maximalPart m) a)).trans
          (count_maximalPart_le_one m s)
    _ = A.card := by simp
    _ ≤ 1 := hcard

/-- On any nonempty cut, the canonical maximal part has chain weight `1`. -/
theorem chainWeight_maximalPart_of_cutPart_ne_zero {m : Multisegment} {a : ℤ}
    (h : cutPart m a ≠ 0) : chainWeight (maximalPart m) a = 1 := by
  have hle := chainWeight_maximalPart_le_one m a
  have hpos : 0 < chainWeight (maximalPart m) a :=
    (chainWeight_pos_iff (maximalPart m) a).mpr (mt (cutPart_maximalPart_eq_zero_iff m a).mp h)
  omega

/-- On any nonempty cut, peeling `maximalPart m` reduces `chainWeight m a` by exactly `1`. -/
theorem chainWeight_eq_chainWeight_remainder_add_one {m : Multisegment} {a : ℤ}
    (h : cutPart m a ≠ 0) : chainWeight m a = chainWeight (remainder m) a + 1 := by
  refine le_antisymm ?_ ?_
  · calc chainWeight m a
        = chainWeight (maximalPart m + remainder m) a := by rw [maximalPart_add_remainder]
      _ ≤ chainWeight (maximalPart m) a + chainWeight (remainder m) a :=
          chainWeight_add_le _ _ _
      _ = chainWeight (remainder m) a + 1 := by
          rw [chainWeight_maximalPart_of_cutPart_ne_zero h, add_comm]
  · obtain ⟨B, hBsub, hBchain, hBsum⟩ := exists_isInclusionChain_weight_eq (remainder m) a
    rcases B.eq_empty_or_nonempty with rfl | hBne
    · have hzero : chainWeight (remainder m) a = 0 := by simpa using hBsum.symm
      have hpos : 0 < chainWeight m a := (chainWeight_pos_iff m a).mpr h
      omega
    · obtain ⟨g, hgB, hgmax⟩ := hBchain.exists_isGreatest
        B.finite_toSet (Finset.coe_nonempty.mpr hBne)
      obtain ⟨hgrem, hgcut⟩ := mem_cutPart_iff.mp (Multiset.mem_toFinset.mp (hBsub hgB))
      obtain ⟨t, htmax, hgt⟩ :=
        exists_le_mem_maximalPart (Multiset.mem_of_le (remainder_le m) hgrem)
      have hsub : (g : Set ℤ) ⊆ (t : Set ℤ) := NonemptyInterval.coe_subset_coe.mpr hgt
      have htcut : a ∈ t ∨ a + 1 ∈ t := hgcut.imp (fun ha => hsub ha) (fun ha => hsub ha)
      have htcount : (cutPart (maximalPart m) a).count t = 1 := by
        rw [count_cutPart_of_mem htcut]
        exact Multiset.count_eq_one_of_mem (nodup_maximalPart m) htmax
      have hChain : IsInclusionChain (insert t B) := by
        simpa only [IsInclusionChain, Finset.coe_insert] using
          hBchain.insert fun s hsB _ => Or.inr ((hgmax hsB).trans hgt)
      calc chainWeight (remainder m) a + 1
          = ∑ s ∈ B, (cutPart (remainder m) a).count s +
              (cutPart (maximalPart m) a).count t := by rw [hBsum, htcount]
        _ ≤ ∑ s ∈ insert t B, (cutPart (remainder m) a).count s +
              ∑ s ∈ insert t B, (cutPart (maximalPart m) a).count s :=
            add_le_add
              (Finset.sum_le_sum_of_subset (Finset.subset_insert t B))
              (Finset.single_le_sum (f := fun s => (cutPart (maximalPart m) a).count s)
                (fun _ _ => Nat.zero_le _) (Finset.mem_insert_self t B))
        _ = ∑ s ∈ insert t B, (cutPart m a).count s := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← cutPart_maximalPart_add_remainder m a, Multiset.count_add, add_comm]
        _ ≤ chainWeight m a := sum_count_le_chainWeight hChain

/-- Unconditional additivity of `chainWeight` across the canonical maximal decomposition. -/
theorem chainWeight_maximalPart_add_remainder (m : Multisegment) (a : ℤ) :
    chainWeight m a = chainWeight (maximalPart m) a + chainWeight (remainder m) a := by
  by_cases h : cutPart m a = 0
  · have hmax : cutPart (maximalPart m) a = 0 := (cutPart_maximalPart_eq_zero_iff m a).mpr h
    have hrem : cutPart (remainder m) a = 0 := cutPart_remainder_eq_zero_of_cutPart_eq_zero h
    rw [(chainWeight_eq_zero_iff m a).mpr h, (chainWeight_eq_zero_iff _ a).mpr hmax,
      (chainWeight_eq_zero_iff _ a).mpr hrem]
  · rw [chainWeight_eq_chainWeight_remainder_add_one h,
      chainWeight_maximalPart_of_cutPart_ne_zero h, add_comm]

end TauCeti.Multisegment
