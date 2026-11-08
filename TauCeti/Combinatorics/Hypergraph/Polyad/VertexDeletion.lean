/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Subpolyad
import TauCeti.Data.Fintype.CardEmbedding
import Mathlib.Tactic.Linarith

/-!
# Support mass lost by deleting vertices

Deleting a set `B` of vertices removes at most `3 |B| |V|²` role-ordered injective triples.
Polyad supports are disjoint, so the same bound controls the sum of their support losses,
without a factor depending on the number of polyads. Consequently, polyads losing more than
an `η`-fraction of their support have total original support mass at most
`3 |B| |V|² / η`.

The retained support is expressed using `Subpolyad3.ofSubcells` with all three subcells equal
to `univ \ B`. This estimate charges the polyads on which support retention is insufficient
for slicing top regularity after removing auxiliary vertices. It applies to any finite
selection of polyads, including repeated vertex cells, and requires no finite palette,
equitability, or regularity hypothesis.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the padding-and-restriction setting.
-/

public section

open Finset

namespace TauCeti.Polyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V}

/-- Deleting `B` removes at most `3 |B| |V|²` triples from any finite selection of polyad
supports. Each removed triple is charged only once, independently of the palette size. -/
theorem sum_card_support_sdiff_ofSubcells_le (A : Finset (Polyad3 S)) (B : Finset V) :
    ∑ P ∈ A, #(P.support \
      (Subpolyad3.ofSubcells P (univ \ B) (univ \ B) (univ \ B)).support) ≤
      3 * #B * Fintype.card V ^ 2 := by
  classical
  let lost (P : Polyad3 S) := P.support \
    (Subpolyad3.ofSubcells P (univ \ B) (univ \ B) (univ \ B)).support
  have hdisj : (A : Set (Polyad3 S)).PairwiseDisjoint lost := by
    intro P _ Q _ hPQ
    exact (pairwise_disjoint_support hPQ).mono sdiff_subset sdiff_subset
  rw [← card_biUnion hdisj]
  calc
    #(A.biUnion lost) ≤
        #{x : {x : Fin 3 → V // Function.Injective x} | ∃ i, x.1 i ∈ B} := by
      apply card_le_card
      intro x hx
      obtain ⟨P, _, hx⟩ := mem_biUnion.1 hx
      obtain ⟨hP, hnot⟩ := mem_sdiff.1 hx
      apply mem_filter.2 ⟨mem_univ _, ?_⟩
      by_contra! h
      exact hnot ((Subpolyad3.mem_ofSubcells_support P _ _ _ x).2
        ⟨hP, by simp [h 0], by simp [h 1], by simp [h 2]⟩)
    _ ≤ 3 * #B * Fintype.card V ^ 2 :=
      card_filter_injective_exists_mem_le B

/-- Polyads losing more than an `η`-fraction of their support under vertex deletion have
original support mass at most `3 |B| |V|² / η`. The mass is measured before deletion, so it
also bounds the mass of retained triples in these polyads. -/
theorem sum_card_support_filter_card_ofSubcells_lt_le
    (A : Finset (Polyad3 S)) (B : Finset V) {η : ℝ} (hη : 0 < η) :
    ∑ P ∈ A with
        (#(Subpolyad3.ofSubcells P (univ \ B) (univ \ B) (univ \ B)).support : ℝ) <
          (1 - η) * #P.support,
      (#P.support : ℝ) ≤ 3 * #B * (Fintype.card V : ℝ) ^ 2 / η := by
  classical
  let bad := A.filter fun P ↦
    (#(Subpolyad3.ofSubcells P (univ \ B) (univ \ B) (univ \ B)).support : ℝ) <
      (1 - η) * #P.support
  apply (le_div_iff₀ hη).2
  rw [mul_comm, mul_sum]
  calc
    ∑ P ∈ bad, η * (#P.support : ℝ) ≤
        ∑ P ∈ bad, (#(P.support \
          (Subpolyad3.ofSubcells P (univ \ B) (univ \ B) (univ \ B)).support) : ℝ) := by
      refine sum_le_sum fun P hP ↦ ?_
      have hsmall := (mem_filter.1 hP).2
      have hcard := card_sdiff_add_card_eq_card
        (Subpolyad3.ofSubcells P (univ \ B) (univ \ B) (univ \ B)).support_subset
      have hcard' :
          (#(P.support \
            (Subpolyad3.ofSubcells P (univ \ B) (univ \ B) (univ \ B)).support) : ℝ) +
            #(Subpolyad3.ofSubcells P (univ \ B) (univ \ B) (univ \ B)).support =
            #P.support := by exact_mod_cast hcard
      linarith
    _ ≤ 3 * #B * (Fintype.card V : ℝ) ^ 2 := by
      exact_mod_cast sum_card_support_sdiff_ofSubcells_le bad B

end TauCeti.Polyad3
