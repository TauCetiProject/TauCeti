/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Dilworth
public import TauCeti.RepresentationTheory.Quiver.Multisegment.CutWeight
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# The endpoint order on occurrences of a multisegment

The occurrences of a multisegment `q`, labelled by `Fin q.card` through `occurrenceInterval`,
carry the strict endpoint order `endpointBefore q`: the label `i` lies before `j` when both
endpoints of its interval are strictly smaller than those of the interval of `j`. Different
labels carrying the same interval are incomparable, as are labels whose intervals share an
endpoint.

This file defines the largest size `antichainWidth q` of an antichain of labels and the largest
size `matchingNumber q` of a matching in the split bipartite graph of the endpoint order, and
proves that they add up to the number of occurrences, by Fulkerson's form of Dilworth's theorem.

Two labels are incomparable for the endpoint order exactly when their intervals are comparable
for inclusion. So endpoint antichains are inclusion chains in which every interval may be taken
with all its copies, and on the adjacent cut `cutPart m a` the antichain width is the weighted
chain maximum `chainWeight m a`. This identifies `chainWeight m a` with the number of occurrences
of `cutPart m a` minus its matching number.

## Main definitions

* `TauCeti.Multisegment.endpointBefore`: the strict endpoint order on occurrence labels.
* `TauCeti.Multisegment.antichainWidth`: the largest size of an endpoint antichain of labels.
* `TauCeti.Multisegment.matchingNumber`: the largest size of a matching in the split bipartite
  graph of the endpoint order.

## Main results

* `TauCeti.Multisegment.le_or_le_iff_not_endpointBefore`: two labels are incomparable for the
  endpoint order if and only if their intervals are comparable for inclusion.
* `TauCeti.Multisegment.matchingNumber_add_antichainWidth`: the matching number and the antichain
  width add up to the number of occurrences.
* `TauCeti.Multisegment.antichainWidth_cutPart`: the antichain width of the adjacent cut
  `cutPart m a` is the weighted inclusion-chain maximum `chainWeight m a`.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, Proposition 3.7.
* C. Mœglin, J.-L. Waldspurger, *Sur l'involution de Zelevinski*, J. Reine Angew. Math. 372
  (1986), 136–177, §II.1 and Lemma II.4.
* D. R. Fulkerson, *Note on Dilworth's decomposition theorem for partially ordered sets*, Proc.
  Amer. Math. Soc. 7 (1956), 701–702.
-/

public section

open Finset

namespace TauCeti.Multisegment

variable {q : Multisegment}

/-! ### The endpoint order -/

/-- The label `i` lies before `j` in the strict endpoint order when both endpoints of the interval
of `i` are strictly smaller than the corresponding endpoints of the interval of `j`. -/
def endpointBefore (q : Multisegment) (i j : Fin q.card) : Prop :=
  (occurrenceInterval q i).fst < (occurrenceInterval q j).fst ∧
    (occurrenceInterval q i).snd < (occurrenceInterval q j).snd

theorem endpointBefore_def {i j : Fin q.card} :
    endpointBefore q i j ↔ (occurrenceInterval q i).fst < (occurrenceInterval q j).fst ∧
      (occurrenceInterval q i).snd < (occurrenceInterval q j).snd :=
  Iff.rfl

/-- The endpoint order is a strict order on occurrence labels. -/
instance (q : Multisegment) : IsStrictOrder (Fin q.card) (endpointBefore q) where
  irrefl _ h := lt_irrefl _ h.1
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Two labels are incomparable for the endpoint order if and only if their intervals are
comparable for inclusion. In particular different labels of the same interval are incomparable.
-/
theorem le_or_le_iff_not_endpointBefore {i j : Fin q.card} :
    occurrenceInterval q i ≤ occurrenceInterval q j ∨
        occurrenceInterval q j ≤ occurrenceInterval q i ↔
      ¬endpointBefore q i j ∧ ¬endpointBefore q j i := by
  simp only [NonemptyInterval.le_def, endpointBefore_def]
  omega

/-! ### Antichain width and matching number -/

open Classical in
/-- The largest number of occurrence labels of `q` forming an antichain for the endpoint order.
-/
noncomputable def antichainWidth (q : Multisegment) : ℕ :=
  ((univ : Finset (Fin q.card)).powerset.filter
    fun A : Finset (Fin q.card) => IsAntichain (endpointBefore q) (A : Set (Fin q.card))).sup card

open Classical in
/-- The largest number of edges of a matching in the split bipartite graph of the endpoint order
on the occurrence labels of `q`. A label may be used once as a first and once as a second
coordinate. -/
noncomputable def matchingNumber (q : Multisegment) : ℕ :=
  ((univ : Finset (Fin q.card × Fin q.card)).powerset.filter
    (IsSplitMatching (endpointBefore q) univ)).sup card

/-- Every endpoint antichain of labels has at most `antichainWidth q` labels. -/
theorem card_le_antichainWidth {A : Finset (Fin q.card)}
    (hA : IsAntichain (endpointBefore q) (A : Set (Fin q.card))) : #A ≤ antichainWidth q := by
  classical
  exact le_sup (f := card) (mem_filter.2 ⟨mem_powerset.2 (subset_univ A), hA⟩)

/-- Some endpoint antichain of labels has exactly `antichainWidth q` labels. -/
theorem exists_isAntichain_card_eq_antichainWidth (q : Multisegment) :
    ∃ A : Finset (Fin q.card), IsAntichain (endpointBefore q) (A : Set (Fin q.card)) ∧
      #A = antichainWidth q := by
  classical
  obtain ⟨A, hA, hcard⟩ := exists_mem_eq_sup _
    ⟨∅, (mem_filter (p := fun A : Finset (Fin q.card) =>
      IsAntichain (endpointBefore q) (A : Set (Fin q.card)))).2
      ⟨empty_mem_powerset _, by simp⟩⟩ (card (α := Fin q.card))
  exact ⟨A, (mem_filter.1 hA).2, by rw [antichainWidth, hcard]⟩

/-- Upper bounds on `antichainWidth q` are upper bounds on all endpoint antichains of labels. -/
theorem antichainWidth_le_iff {k : ℕ} :
    antichainWidth q ≤ k ↔
      ∀ A : Finset (Fin q.card), IsAntichain (endpointBefore q) (A : Set (Fin q.card)) →
        #A ≤ k := by
  refine ⟨fun h A hA => (card_le_antichainWidth hA).trans h, fun h => ?_⟩
  obtain ⟨A, hA, hcard⟩ := exists_isAntichain_card_eq_antichainWidth q
  exact hcard ▸ h A hA

/-- Every split-graph matching of the endpoint order has at most `matchingNumber q` edges. -/
theorem card_le_matchingNumber {E : Finset (Fin q.card × Fin q.card)}
    (hE : IsSplitMatching (endpointBefore q) univ E) : #E ≤ matchingNumber q := by
  classical
  exact le_sup (f := card) (mem_filter.2 ⟨mem_powerset.2 (subset_univ E), hE⟩)

/-- Some split-graph matching of the endpoint order has exactly `matchingNumber q` edges. -/
theorem exists_isSplitMatching_card_eq_matchingNumber (q : Multisegment) :
    ∃ E : Finset (Fin q.card × Fin q.card), IsSplitMatching (endpointBefore q) univ E ∧
      #E = matchingNumber q := by
  classical
  obtain ⟨E, hE, hcard⟩ := exists_mem_eq_sup _
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, IsSplitMatching.empty _ _⟩⟩
    (card (α := Fin q.card × Fin q.card))
  exact ⟨E, (mem_filter.1 hE).2, by rw [matchingNumber, hcard]⟩

/-- Upper bounds on `matchingNumber q` are upper bounds on all split-graph matchings of the
endpoint order. -/
theorem matchingNumber_le_iff {k : ℕ} :
    matchingNumber q ≤ k ↔
      ∀ E : Finset (Fin q.card × Fin q.card), IsSplitMatching (endpointBefore q) univ E →
        #E ≤ k := by
  refine ⟨fun h E hE => (card_le_matchingNumber hE).trans h, fun h => ?_⟩
  obtain ⟨E, hE, hcard⟩ := exists_isSplitMatching_card_eq_matchingNumber q
  exact hcard ▸ h E hE

/-- The matching number and the antichain width of the endpoint order add up to the number of
occurrences. -/
theorem matchingNumber_add_antichainWidth (q : Multisegment) :
    matchingNumber q + antichainWidth q = q.card := by
  refine le_antisymm ?_ ?_
  · obtain ⟨E, hE, hEcard⟩ := exists_isSplitMatching_card_eq_matchingNumber q
    obtain ⟨A, hA, hAcard⟩ := exists_isAntichain_card_eq_antichainWidth q
    simpa [← hEcard, ← hAcard, add_comm] using hE.card_add_card_le_card hA (subset_univ A)
  · obtain ⟨A, -, hA, E, hE, hcard⟩ :=
      exists_isAntichain_isSplitMatching_card_add_card_eq (endpointBefore q) univ
    rw [card_univ, Fintype.card_fin] at hcard
    have := card_le_antichainWidth hA
    have := card_le_matchingNumber hE
    omega

/-- The antichain width is at most the number of occurrences. -/
theorem antichainWidth_le_card (q : Multisegment) : antichainWidth q ≤ q.card := by
  rw [← matchingNumber_add_antichainWidth q]
  exact Nat.le_add_left _ _

/-- The matching number is at most the number of occurrences. -/
theorem matchingNumber_le_card (q : Multisegment) : matchingNumber q ≤ q.card := by
  rw [← matchingNumber_add_antichainWidth q]
  exact Nat.le_add_right _ _

/-- The empty multisegment has antichain width zero. -/
@[simp]
theorem antichainWidth_zero : antichainWidth 0 = 0 :=
  Nat.le_zero.1 (antichainWidth_le_card 0)

/-- The empty multisegment has matching number zero. -/
@[simp]
theorem matchingNumber_zero : matchingNumber 0 = 0 :=
  Nat.le_zero.1 (matchingNumber_le_card 0)

/-! ### Invariance under relabeling -/

/-- Relabeling the occurrences by a permutation `σ` does not change the antichain width: the
antichains of the endpoint order of the relabeled family `occurrenceInterval q ∘ σ` have the same
upper bounds as those of `endpointBefore q`. -/
theorem antichainWidth_le_iff_perm (σ : Equiv.Perm (Fin q.card)) {k : ℕ} :
    antichainWidth q ≤ k ↔
      ∀ A : Finset (Fin q.card),
        IsAntichain (fun i j => endpointBefore q (σ i) (σ j)) (A : Set (Fin q.card)) →
          #A ≤ k := by
  rw [antichainWidth_le_iff]
  refine ⟨fun h A hA => ?_, fun h A hA => ?_⟩
  · rw [← card_map σ.toEmbedding]
    exact h _ (by simpa using hA.image σ fun _ _ => id)
  · rw [← card_map σ.symm.toEmbedding]
    exact h _ (by simpa using hA.image σ.symm fun _ _ => by simp)

/-- Relabeling the occurrences by a permutation `σ` does not change the matching number: the
split-graph matchings of the endpoint order of the relabeled family `occurrenceInterval q ∘ σ` have
the same upper bounds as those of `endpointBefore q`. -/
theorem matchingNumber_le_iff_perm (σ : Equiv.Perm (Fin q.card)) {k : ℕ} :
    matchingNumber q ≤ k ↔
      ∀ E : Finset (Fin q.card × Fin q.card),
        IsSplitMatching (fun i j => endpointBefore q (σ i) (σ j)) univ E → #E ≤ k := by
  rw [matchingNumber_le_iff]
  refine ⟨fun h E hE => ?_, fun h E hE => ?_⟩
  · rw [← card_map (σ.toEmbedding.prodMap σ.toEmbedding)]
    exact h _ (hE.map σ.toEmbedding (fun _ _ h => by simpa using h) (subset_univ _))
  · rw [← card_map (σ.symm.toEmbedding.prodMap σ.symm.toEmbedding)]
    exact h _ (hE.map σ.symm.toEmbedding (fun _ _ => by simp) (subset_univ _))

/-! ### Endpoint antichains and inclusion chains -/

/-- The labels carrying the intervals of an inclusion chain form an endpoint antichain. -/
theorem isAntichain_filter_occurrenceInterval_mem {B : Finset IntInterval}
    (hB : IsInclusionChain B) :
    IsAntichain (endpointBefore q)
      ((univ.filter fun i : Fin q.card => occurrenceInterval q i ∈ B : Finset _) :
        Set (Fin q.card)) := by
  intro i hi j hj _
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
  exact (le_or_le_iff_not_endpointBefore.1 (hB.total hi hj)).1

/-- The intervals carried by an endpoint antichain of labels form an inclusion chain in the
support of `q`, whose occurrences counted with multiplicity are at least as many as the labels of
the antichain. -/
theorem exists_isInclusionChain_card_le_sum_count {A : Finset (Fin q.card)}
    (hA : IsAntichain (endpointBefore q) (A : Set (Fin q.card))) :
    ∃ B ⊆ q.toFinset, IsInclusionChain B ∧ #A ≤ ∑ s ∈ B, q.count s := by
  classical
  refine ⟨A.image (occurrenceInterval q), fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := mem_image.1 hs
    exact Multiset.mem_toFinset.2 (occurrenceInterval_mem q i)
  · rintro _ hs _ ht hst
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hs
    obtain ⟨j, hj, rfl⟩ := mem_image.1 ht
    have hij : i ≠ j := fun h => hst (h ▸ rfl)
    exact le_or_le_iff_not_endpointBefore.2 ⟨hA hi hj hij, hA hj hi hij.symm⟩
  · rw [← card_filter_occurrenceInterval_mem]
    exact card_le_card fun i hi => mem_filter.2 ⟨mem_univ i, mem_image_of_mem _ hi⟩

/-- On the adjacent cut, the antichain width of the endpoint order is the weighted inclusion-chain
maximum `chainWeight m a`. -/
theorem antichainWidth_cutPart (m : Multisegment) (a : ℤ) :
    antichainWidth (cutPart m a) = chainWeight m a := by
  refine le_antisymm (antichainWidth_le_iff.2 fun A hA => ?_) ?_
  · obtain ⟨B, -, hB, hAB⟩ := exists_isInclusionChain_card_le_sum_count hA
    exact hAB.trans (sum_count_le_chainWeight hB)
  · obtain ⟨B, -, hB, hweight⟩ := exists_isInclusionChain_weight_eq m a
    rw [← hweight, ← card_filter_occurrenceInterval_mem]
    exact card_le_antichainWidth (isAntichain_filter_occurrenceInterval_mem hB)

/-- On the adjacent cut, the matching number of the endpoint order is the number of occurrences
minus the weighted inclusion-chain maximum `chainWeight m a`. -/
theorem matchingNumber_cutPart_add_chainWeight (m : Multisegment) (a : ℤ) :
    matchingNumber (cutPart m a) + chainWeight m a = (cutPart m a).card := by
  rw [← antichainWidth_cutPart, matchingNumber_add_antichainWidth]

end TauCeti.Multisegment
