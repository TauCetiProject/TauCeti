/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Lex
public import TauCeti.Combinatorics.Enumerative.Partition.Basic

/-!
# Dominance order on partitions

This file defines dominance of partitions of a fixed natural number by comparing all partial
sums of their decreasingly sorted parts. It proves that dominance is a partial order and that
dominance implies the corresponding lexicographic comparison, strictly for strict dominance.

The dominance order is the triangular order governing Kostka numbers and the occurrence of
Specht modules in permutation modules.

The lexicographic linear order and the dominance partial order on `n.Partition` are provided as
scoped instances, activated by `open scoped TauCeti.PartitionLex` and
`open scoped TauCeti.DominanceOrder` respectively.

## References

* [Mathlib PR #42725](https://github.com/leanprover-community/mathlib4/pull/42725)
  (Kim Morrison) — the draft upstream adaptation of this file; the ℕ-indexed definition of
  `Nat.Partition.Dominates` and the `Fin`-indexed decidability characterization follow the form
  prepared for that PR.
-/

public section

namespace Nat.Partition

/-- The decreasingly sorted parts of a partition of `n` sum to `n`. -/
@[simp]
theorem sum_sort_parts {n : ℕ} (μ : n.Partition) : (μ.parts.sort (· ≥ ·)).sum = n := by
  rw [← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

/-- A partition is determined by its decreasingly sorted parts. -/
theorem sort_parts_injective {n : ℕ} :
    Function.Injective fun μ : n.Partition => μ.parts.sort (· ≥ ·) :=
  fun μ ν h => Nat.Partition.ext <| by simpa using congrArg ((↑) : List ℕ → Multiset ℕ) h

end Nat.Partition

namespace TauCeti.PartitionLex

/-- The lexicographic linear order on partitions, obtained from their decreasingly sorted parts.
Activate it with `open scoped TauCeti.PartitionLex`. -/
scoped instance partitionLinearOrder {n : ℕ} : LinearOrder n.Partition :=
  LinearOrder.lift' (fun μ => μ.parts.sort (· ≥ ·)) Nat.Partition.sort_parts_injective

/-- Partition comparison in the lexicographic order is comparison of the decreasingly sorted
parts. -/
@[simp]
theorem partition_lt_iff {n : ℕ} {μ ν : n.Partition} :
    @LT.lt n.Partition partitionLinearOrder.toLT μ ν ↔
      μ.parts.sort (· ≥ ·) < ν.parts.sort (· ≥ ·) :=
  Iff.rfl

/-- Partition comparison in the non-strict lexicographic order is comparison of the decreasingly
sorted parts. -/
@[simp]
theorem partition_le_iff {n : ℕ} {μ ν : n.Partition} :
    @LE.le n.Partition partitionLinearOrder.toLE μ ν ↔
      μ.parts.sort (· ≥ ·) ≤ ν.parts.sort (· ≥ ·) :=
  Iff.rfl

end TauCeti.PartitionLex

namespace Nat.Partition

/-- A partition `μ` dominates a partition `ν` when every partial sum of the decreasingly
sorted parts of `μ` is at least the corresponding partial sum of `ν`.

The definition quantifies over all of `ℕ`, following the form prepared for
[Mathlib PR #42725](https://github.com/leanprover-community/mathlib4/pull/42725); use
`dominates_iff` to unfold it outside this module and `dominates_iff_forall_fin` to reduce
to the first `n + 1` partial sums. -/
def Dominates {n : ℕ} (μ ν : n.Partition) : Prop :=
  ∀ k : ℕ,
    ((ν.parts.sort (· ≥ ·)).take k).sum ≤ ((μ.parts.sort (· ≥ ·)).take k).sum

/-- The defining partial-sum characterization of dominance. -/
theorem dominates_iff {n : ℕ} {μ ν : n.Partition} :
    μ.Dominates ν ↔
      ∀ k : ℕ,
        ((ν.parts.sort (· ≥ ·)).take k).sum ≤
          ((μ.parts.sort (· ≥ ·)).take k).sum :=
  Iff.rfl

/-- Partial sums of sorted parts of partitions of `n` agree from index `n` on, so dominance is
determined by the first `n + 1` partial sums. In particular it is decidable. -/
theorem dominates_iff_forall_fin {n : ℕ} {μ ν : n.Partition} :
    μ.Dominates ν ↔
      ∀ k : Fin (n + 1),
        ((ν.parts.sort (· ≥ ·)).take k).sum ≤
          ((μ.parts.sort (· ≥ ·)).take k).sum := by
  refine ⟨fun h k => h k, fun h k => ?_⟩
  rcases le_or_gt k n with hk | hk
  · exact h ⟨k, Nat.lt_succ_of_le hk⟩
  · have hlen (ξ : n.Partition) : (ξ.parts.sort (· ≥ ·)).length ≤ k :=
      ((Multiset.length_sort _).trans_le ξ.card_parts_le).trans hk.le
    rw [List.take_of_length_le (hlen ν), List.take_of_length_le (hlen μ), sum_sort_parts,
      sum_sort_parts]

instance {n : ℕ} (μ ν : n.Partition) : Decidable (μ.Dominates ν) :=
  decidable_of_iff _ dominates_iff_forall_fin.symm

/-- Every partition dominates itself. -/
@[simp, refl]
theorem dominates_refl {n : ℕ} (μ : n.Partition) : μ.Dominates μ :=
  fun _ => le_rfl

/-- Dominance is transitive. -/
@[trans]
theorem Dominates.trans {n : ℕ} {μ ν ξ : n.Partition}
    (hμν : μ.Dominates ν) (hνξ : ν.Dominates ξ) : μ.Dominates ξ :=
  fun k => (hνξ k).trans (hμν k)

/-- If every partial sum of `l₂` is at most the corresponding partial sum of `l₁`, the entries
of `l₂` are positive and the lists differ, then `l₂` is lexicographically smaller than `l₁`. -/
private theorem lex_lt_of_sum_take_le {l₁ l₂ : List ℕ} (hpos : ∀ i ∈ l₂, 0 < i)
    (hle : ∀ k : ℕ, (l₂.take k).sum ≤ (l₁.take k).sum) (hne : l₁ ≠ l₂) : l₂ < l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact absurd rfl hne
      | cons b l₂ =>
          have hb := hpos b (by simp)
          have := hle 1
          simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
            List.take_nil] at this
          omega
  | cons a l₁ ih =>
      cases l₂ with
      | nil => exact List.Lex.nil
      | cons b l₂ =>
          have hba : b ≤ a := by simpa using hle 1
          rcases hba.eq_or_lt with rfl | hba
          · exact List.Lex.cons <| ih (fun i hi => hpos i (by simp [hi]))
              (fun k => by simpa using hle (k + 1)) (by simpa using hne)
          · exact List.Lex.rel hba

private theorem lex_lt_of_dominates_of_ne {n : ℕ} {μ ν : n.Partition}
    (hdom : μ.Dominates ν) (hne : μ ≠ ν) :
    ν.parts.sort (· ≥ ·) < μ.parts.sort (· ≥ ·) :=
  lex_lt_of_sum_take_le (fun _ hi => ν.parts_pos ((Multiset.mem_sort _).mp hi)) hdom
    (sort_parts_injective.ne hne)

/-- Dominance is antisymmetric. -/
theorem Dominates.antisymm {n : ℕ} {μ ν : n.Partition}
    (hμν : μ.Dominates ν) (hνμ : ν.Dominates μ) : μ = ν := by
  by_contra hne
  exact (lex_lt_of_dominates_of_ne hμν hne).asymm (lex_lt_of_dominates_of_ne hνμ (Ne.symm hne))

end Nat.Partition

namespace TauCeti.DominanceOrder

/-- The dominance partial order on partitions, oriented so that `ν ≤ μ` means that `μ`
dominates `ν`. Activate it with `open scoped TauCeti.DominanceOrder`. -/
scoped instance partitionPartialOrder {n : ℕ} : PartialOrder n.Partition where
  le μ ν := ν.Dominates μ
  le_refl μ := Nat.Partition.dominates_refl μ
  le_trans _ _ _ hμν hνξ := hνξ.trans hμν
  le_antisymm _ _ hμν hνμ := hνμ.antisymm hμν

/-- Partition comparison in the dominance order is dominance in the reverse direction. -/
@[simp]
theorem partition_le_iff {n : ℕ} {μ ν : n.Partition} :
    @LE.le n.Partition partitionPartialOrder.toLE μ ν ↔ ν.Dominates μ :=
  Iff.rfl

/-- Strict partition comparison in the dominance order is strict dominance in the reverse
direction. -/
@[simp]
theorem partition_lt_iff {n : ℕ} {μ ν : n.Partition} :
    @LT.lt n.Partition partitionPartialOrder.toLT μ ν ↔ ν.Dominates μ ∧ μ ≠ ν := by
  let := partitionPartialOrder (n := n)
  exact lt_iff_le_and_ne.trans (and_congr partition_le_iff Iff.rfl)

end TauCeti.DominanceOrder

namespace Nat.Partition

/-- Strict dominance is the strict relation of the dominance partial order. -/
def StrictlyDominates {n : ℕ} (μ ν : n.Partition) : Prop :=
  TauCeti.DominanceOrder.partitionPartialOrder.lt ν μ

/-- Strict dominance is dominance between unequal partitions. -/
@[simp]
theorem strictlyDominates_iff {n : ℕ} {μ ν : n.Partition} :
    μ.StrictlyDominates ν ↔ μ.Dominates ν ∧ μ ≠ ν :=
  TauCeti.DominanceOrder.partition_lt_iff.trans (and_congr Iff.rfl ne_comm)

/-- Strict dominance is a strict order on partitions, inherited from the dominance partial
order. -/
instance {n : ℕ} : IsStrictOrder n.Partition StrictlyDominates :=
  letI := TauCeti.DominanceOrder.partitionPartialOrder (n := n)
  inferInstanceAs (IsStrictOrder n.Partition (Function.swap (· < ·)))

instance {n : ℕ} (μ ν : n.Partition) : Decidable (μ.StrictlyDominates ν) :=
  decidable_of_iff _ strictlyDominates_iff.symm

open scoped TauCeti.PartitionLex

/-- Strict dominance refines the lexicographic linear order on partitions. -/
theorem lex_lt_of_strictlyDominates {n : ℕ} {μ ν : n.Partition}
    (h : μ.StrictlyDominates ν) : ν < μ :=
  lex_lt_of_dominates_of_ne (strictlyDominates_iff.mp h).1 (strictlyDominates_iff.mp h).2

/-- Dominance refines the lexicographic linear order on partitions. -/
theorem lex_le_of_dominates {n : ℕ} {μ ν : n.Partition} (h : μ.Dominates ν) : ν ≤ μ := by
  rcases eq_or_ne μ ν with rfl | hne
  · exact le_rfl
  · exact (lex_lt_of_dominates_of_ne h hne).le

/-- The one-part partition dominates every partition of the same natural number. -/
@[simp]
theorem indiscrete_dominates {n : ℕ} (μ : n.Partition) : (indiscrete n).Dominates μ := by
  rintro (_ | k)
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simpa [indiscrete_parts hn] using
      ((List.take_sublist _ _).sum_le_sum fun _ _ => Nat.zero_le _).trans_eq (sum_sort_parts μ)

/-- A partition dominates the one-part partition only when it is that partition. -/
@[simp]
theorem dominates_indiscrete_iff {n : ℕ} {μ : n.Partition} :
    μ.Dominates (indiscrete n) ↔ μ = indiscrete n :=
  ⟨fun h => h.antisymm (indiscrete_dominates μ), by rintro rfl; exact dominates_refl _⟩

end Nat.Partition
