/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Graph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.BigOperators
import TauCeti.Data.Finset.Basic

/-!
# Graphs selected by pair colors

A reversal-invariant finite set of colors in a coherent pair coloring selects an undirected
simple graph. Between disjoint vertex sets its edge density is the sum of the selected color
densities. Coordinatewise pair regularity therefore gives graph uniformity, with a loss equal
to the number of selected colors and a strict enlargement of the error parameter.

This is a graph-facing interpretation of lower-skeleton regularity. It applies to unions of
reversal orbits, not just to palettes whose reversal is the identity. The disjointness assumption
in the density comparison is essential: graph densities include diagonal pairs in the denominator,
whereas pair-color densities exclude them.
-/

public section

open Finset

namespace TauCeti.PairColorSystem

variable {κ V : Type*} (S : PairColorSystem κ V) (K : Finset κ)
  (hK : ∀ c ∈ K, S.rev c ∈ K)

/-- The simple graph selecting the colors in a reversal-invariant finite set `K`. -/
noncomputable def colorGraph : SimpleGraph V where
  Adj u v := ∃ c ∈ K, S.colorOfPair u v = some c
  symm := ⟨by
    rintro u v ⟨c, hc, huv⟩
    exact ⟨S.rev c, hK c hc, (S.colorOfPair_swap_eq_some_iff u v c).2 huv⟩⟩
  loopless := ⟨by simp⟩

/-- Adjacency means that the ordered pair has one of the selected colors. -/
@[simp]
theorem colorGraph_adj (u v : V) :
    (S.colorGraph K hK).Adj u v ↔ ∃ c ∈ K, S.colorOfPair u v = some c :=
  Iff.rfl

/-- Color graphs have classically decidable adjacency. -/
noncomputable instance : DecidableRel (S.colorGraph K hK).Adj := Classical.decRel _

/-- Selecting no colors gives the empty graph. -/
@[simp]
theorem colorGraph_empty (h : ∀ c ∈ (∅ : Finset κ), S.rev c ∈ (∅ : Finset κ)) :
    S.colorGraph ∅ h = ⊥ := by
  ext u v
  simp

/-- The edge count of a color graph is the sum of the selected color counts. This identity
also holds for overlapping vertex sets: it counts edges, without normalizing. -/
theorem card_interedges_colorGraph [DecidableEq κ] (s t : Finset V) :
    #((S.colorGraph K hK).interedges s t) =
      ∑ c ∈ K, #{p ∈ s ×ˢ t | S.colorOfPair p.1 p.2 = some c} := by
  classical
  have hcount := sum_card_fiberwise_eq_card_filter (s ×ˢ t) (K.image some)
    (fun p ↦ S.colorOfPair p.1 p.2)
  rw [sum_image (fun _ _ _ _ h ↦ Option.some_injective _ h)] at hcount
  simpa [SimpleGraph.interedges_def, colorGraph_adj, eq_comm] using hcount.symm

/-- On disjoint sets, the graph density is the sum of the selected pair-color densities,
including when either vertex set or the selected palette is empty. -/
theorem edgeDensity_colorGraph {s t : Finset V} (hst : Disjoint s t) :
    (S.colorGraph K hK).edgeDensity s t = ∑ c ∈ K, pairColorDensity S c s t := by
  classical
  simp_rw [pairColorDensity_def, filter_ne_product_of_disjoint hst, card_product, Nat.cast_mul]
  rw [← sum_div, ← Nat.cast_sum, SimpleGraph.edgeDensity_def, card_interedges_colorGraph]

variable {S K hK} {ε ε' : ℝ} {s t : Finset V}

/-- Coordinatewise regularity controls the density of any reversal-invariant union of colors
on large subrectangles, with error at most `#K * ε`. -/
theorem IsRegularPair.abs_edgeDensity_colorGraph_sub_le (h : S.IsRegularPair ε s t)
    (hst : Disjoint s t) (K : Finset κ) (hK : ∀ c ∈ K, S.rev c ∈ K)
    {s' t' : Finset V} (hs' : s' ⊆ s) (ht' : t' ⊆ t)
    (hs : ε * #s ≤ #s') (ht : ε * #t ≤ #t') :
    |((S.colorGraph K hK).edgeDensity s' t' : ℝ) -
      (S.colorGraph K hK).edgeDensity s t| ≤ #K * ε := by
  rw [S.edgeDensity_colorGraph K hK (hst.mono hs' ht'), S.edgeDensity_colorGraph K hK hst]
  push_cast
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ c ∈ K, |(pairColorDensity S c s' t' : ℝ) - pairColorDensity S c s t| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ K, ε := sum_le_sum fun c _ ↦ (isRegularPair_iff.1 h) c s' hs' t' ht' hs ht
    _ = #K * ε := by simp

/-- A regular pair gives a uniform pair for the color graph at every parameter strictly
exceeding the accumulated color error. The empty selection needs only `0 < ε'`. -/
theorem IsRegularPair.isUniform_colorGraph (h : S.IsRegularPair ε s t)
    (hst : Disjoint s t) (K : Finset κ) (hK : ∀ c ∈ K, S.rev c ∈ K)
    (hbound : (#K : ℝ) * ε < ε') :
    (S.colorGraph K hK).IsUniform ε' s t := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · intro s' _ t' _ _ _
    simpa [SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def, colorGraph_adj] using hbound
  have : Nonempty κ := ⟨hne.choose⟩
  have hcard : (1 : ℝ) ≤ #K := by exact_mod_cast one_le_card.2 hne
  have hε : ε ≤ ε' := (le_mul_of_one_le_left h.nonneg hcard).trans hbound.le
  intro s' hs' t' ht' hs ht
  apply (h.abs_edgeDensity_colorGraph_sub_le hst K hK hs' ht' ?_ ?_).trans_lt hbound
  · exact (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans (by rwa [mul_comm])
  · exact (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans (by rwa [mul_comm])

end TauCeti.PairColorSystem

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Selecting the edge color in the pair coloring of a graph recovers the graph. -/
@[simp]
theorem colorGraph_toPairColorSystem_true :
    G.toPairColorSystem.colorGraph {true} (by simp) = G := by
  ext u v
  simp

/-- Selecting the nonedge color recovers the complement, not the complete relation with loops. -/
@[simp]
theorem colorGraph_toPairColorSystem_false :
    G.toPairColorSystem.colorGraph {false} (by simp) = Gᶜ := by
  ext u v
  simp

end SimpleGraph

namespace TauCeti.PairSkeleton3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V} {ε ε' : ℝ}

/-- No distinct pair of cells is nonuniform in a color graph of a regular lower skeleton,
provided the graph tolerance strictly exceeds the accumulated coordinatewise error. -/
theorem IsPairColorRegular.nonUniforms_colorGraph_eq_empty (h : S.IsPairColorRegular ε)
    (K : Finset κ) (hK : ∀ c ∈ K, S.pairColors.rev c ∈ K)
    (hbound : (#K : ℝ) * ε < ε') :
    S.vertexPart.nonUniforms (S.pairColors.colorGraph K hK) ε' = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  rintro ⟨A, B⟩ hAB
  obtain ⟨hA, hB, hne, hnu⟩ := (S.vertexPart.mk_mem_nonUniforms _).1 hAB
  exact hnu <| (h.isRegularPair hA hB).isUniform_colorGraph
    (S.vertexPart.disjoint hA hB hne) K hK hbound

/-- The vertex partition of a regular lower skeleton is uniform for every graph selected by
a reversal-invariant union of colors, at any tolerance strictly exceeding the color error. -/
theorem IsPairColorRegular.isUniform_colorGraph (h : S.IsPairColorRegular ε)
    (K : Finset κ) (hK : ∀ c ∈ K, S.pairColors.rev c ∈ K)
    (hbound : (#K : ℝ) * ε < ε') :
    S.vertexPart.IsUniform (S.pairColors.colorGraph K hK) ε' := by
  rw [Finpartition.IsUniform, h.nonUniforms_colorGraph_eq_empty K hK hbound, card_empty,
    Nat.cast_zero]
  rcases isEmpty_or_nonempty V with hV | hV
  · have hP : S.vertexPart.parts = ∅ :=
      Finpartition.parts_eq_empty_iff.2 (by simp [univ_eq_empty])
    simp [hP]
  have hpos : 0 ≤ ε' := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simpa using hbound.le
    · have : Nonempty κ := ⟨hne.choose⟩
      exact (mul_nonneg (Nat.cast_nonneg _) h.nonneg).trans hbound.le
  positivity

end TauCeti.PairSkeleton3
