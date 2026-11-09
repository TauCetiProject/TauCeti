/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Trivialization
public import TauCeti.Topology.PartitionOfUnity.Gap

/-!
# Countably many trivializations from partition-of-unity gaps

For a partition of unity subordinate to bundle charts, the positive gap strata of any fixed
cardinality are disjoint. Choosing a chart from each nonempty finite set of indices and gluing
these restrictions gives a genuine trivialization over the positive set of the corresponding
weight of `PartitionOfUnity.gapPartition`. These countably many open sets cover the set on which
the partition sums to one. This is the countabilization argument of Milnor and Stasheff,
*Characteristic Classes*, Lemma 5.9. No metric, rank, or countability assumption is needed.

The charts here do not assert extension of weighted coordinates across zero-weight boundaries.
-/

public section

noncomputable section

open Bundle Set

namespace PartitionOfUnity

variable {ι B F : Type*} {E : B → Type*} {s : Set B}
  [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
  [Nonempty F] [∀ b, Nonempty (E b)] (ρ : PartitionOfUnity ι B s)
  (e : ι → Trivialization F (π F E)) (he : ρ.IsSubordinate fun i ↦ (e i).baseSet)

private def gapChart (n : ℕ) (S : {S : Finset ι // S.Nonempty ∧ S.card = n}) :
    Trivialization F (π F E) :=
  (e (S.2.1.choose)).restrOpen {b | 0 < ρ.gap S.1 b}
    (isOpen_lt continuous_const (ρ.continuous_gap S.1))

omit [Nonempty F] [∀ b, Nonempty (E b)] in
private theorem gapChart_apply (n : ℕ) (S : {S : Finset ι // S.Nonempty ∧ S.card = n})
    (p : TotalSpace F E) : gapChart ρ e n S p = e S.2.1.choose p :=
  rfl

omit [Nonempty F] [∀ b, Nonempty (E b)] in
private theorem gapChart_symm_apply (n : ℕ) (S : {S : Finset ι // S.Nonempty ∧ S.card = n})
    (p : B × F) :
    (gapChart ρ e n S).toOpenPartialHomeomorph.symm p =
      (e S.2.1.choose).toOpenPartialHomeomorph.symm p :=
  rfl

omit [Nonempty F] [∀ b, Nonempty (E b)] in
include he in
private theorem gapChart_baseSet (n : ℕ) (S : {S : Finset ι // S.Nonempty ∧ S.card = n}) :
    (gapChart ρ e n S).baseSet = {b | 0 < ρ.gap S.1 b} := by
  exact Set.inter_eq_right.mpr fun _ hb ↦ he.mem_of_gap_pos hb S.2.1.choose_spec

omit [Nonempty F] [∀ b, Nonempty (E b)] in
include he in
private theorem pairwise_disjoint_gapChart (n : ℕ) :
    Pairwise fun S T : {S : Finset ι // S.Nonempty ∧ S.card = n} ↦
      Disjoint (gapChart ρ e n S).baseSet (gapChart ρ e n T).baseSet := by
  intro S T hST
  rw [gapChart_baseSet ρ e he, gapChart_baseSet ρ e he]
  exact Set.disjoint_left.2 fun _ hS hT ↦ hST (Subtype.ext <|
    ρ.eq_of_gap_pos_of_card_eq hS hT (S.2.2.trans T.2.2.symm))

/-- Glue the subordinate charts on the positive gap strata of cardinality `n`. The resulting
native trivialization has base set exactly the positive set of `ρ.gapPartition n`. On a stratum
indexed by `S`, it uses the chart whose index is `S.Nonempty.choose`. -/
def gapTrivialization (n : ℕ) : Trivialization F (π F E) :=
  Trivialization.iUnion (gapChart ρ e n) (pairwise_disjoint_gapChart ρ e he n)

/-- The `n`-th glued chart is defined exactly where the `n`-th countable weight is positive. -/
@[simp]
theorem gapTrivialization_baseSet (n : ℕ) :
    (ρ.gapTrivialization e he n).baseSet = {b | 0 < ρ.gapPartition n b} := by
  rw [gapTrivialization, Trivialization.iUnion_baseSet]
  ext b
  simp only [Set.mem_iUnion, gapChart_baseSet ρ e he, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨S, hS, hcard⟩, hpos⟩
    rw [← hcard, ρ.gapPartition_card_eq hpos]
    exact mul_pos (Nat.cast_pos.2 hS.card_pos) hpos
  · intro h
    obtain ⟨S, hcard, hpos⟩ := ρ.exists_gap_pos_of_gapPartition_pos h
    exact ⟨⟨S, (ρ.gap_pos_iff.1 hpos).1, hcard⟩, hpos⟩

/-- On a positive gap stratum the glued chart is the chosen original chart. -/
theorem gapTrivialization_apply {S : Finset ι} (hS : S.Nonempty) {b : B}
    (hb : 0 < ρ.gap S b) (v : E b) :
    ρ.gapTrivialization e he S.card ⟨b, v⟩ = e hS.choose ⟨b, v⟩ := by
  calc
    ρ.gapTrivialization e he S.card ⟨b, v⟩ =
        gapChart ρ e S.card ⟨S, hS, rfl⟩ ⟨b, v⟩ :=
      Trivialization.iUnion_apply (gapChart ρ e S.card)
        (pairwise_disjoint_gapChart ρ e he S.card)
        (i := ⟨S, hS, rfl⟩) (by rw [gapChart_baseSet ρ e he]; exact hb)
    _ = e hS.choose ⟨b, v⟩ := gapChart_apply ρ e S.card ⟨S, hS, rfl⟩ ⟨b, v⟩

/-- The inverse glued chart on a positive gap stratum is the chosen original inverse. -/
theorem gapTrivialization_symm_apply {S : Finset ι} (hS : S.Nonempty) {b : B}
    (hb : 0 < ρ.gap S b) (v : F) :
    (ρ.gapTrivialization e he S.card).toOpenPartialHomeomorph.symm (b, v) =
      (e hS.choose).toOpenPartialHomeomorph.symm (b, v) := by
  calc
    (ρ.gapTrivialization e he S.card).toOpenPartialHomeomorph.symm (b, v) =
        (gapChart ρ e S.card ⟨S, hS, rfl⟩).toOpenPartialHomeomorph.symm (b, v) :=
      Trivialization.iUnion_symm_apply (gapChart ρ e S.card)
        (pairwise_disjoint_gapChart ρ e he S.card)
        (i := ⟨S, hS, rfl⟩) (by rw [gapChart_baseSet ρ e he]; exact hb)
    _ = (e hS.choose).toOpenPartialHomeomorph.symm (b, v) :=
      gapChart_symm_apply ρ e S.card ⟨S, hS, rfl⟩ (b, v)

/-- The countably many glued charts cover the set on which the supplied partition sums to one. -/
theorem subset_iUnion_gapTrivialization_baseSet :
    s ⊆ ⋃ n, (ρ.gapTrivialization e he n).baseSet := by
  intro b hb
  obtain ⟨n, hn⟩ := ρ.gapPartition.exists_pos hb
  exact Set.mem_iUnion.2 ⟨n, by simpa only [gapTrivialization_baseSet, Set.mem_ofPred_eq] using hn⟩

/-- The countable chart domains are locally finite, as are the positive sets of their weights. -/
theorem locallyFinite_gapTrivialization_baseSet :
    LocallyFinite fun n ↦ (ρ.gapTrivialization e he n).baseSet := by
  apply ρ.gapPartition.locallyFinite.subset
  intro n b hb
  rw [gapTrivialization_baseSet] at hb
  exact hb.ne'

end PartitionOfUnity
