/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform

/-!
# Uniformity of the complement graph

Between two disjoint vertex sets, every vertex pair is an edge of exactly one of `G` and `Gᶜ`,
so on nonempty sets the two edge densities sum to one. Consequently an `ε`-uniform pair of
disjoint sets in `G` is also `ε`-uniform in `Gᶜ`. Disjointness is needed: within a single set the
diagonal pairs are edges of neither graph.
-/

public section

open Finset

namespace SimpleGraph

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DecidableEq α]
  {G : SimpleGraph α} [DecidableRel G.Adj] {ε : 𝕜} {s t : Finset α}

/-- An `ε`-uniform pair of disjoint vertex sets is `ε`-uniform in the complement graph. -/
theorem IsUniform.compl (h : G.IsUniform ε s t) (hst : Disjoint s t) : Gᶜ.IsUniform ε s t := by
  intro s' hs' t' ht' hs ht
  have hε := h.pos
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simpa [subset_empty.mp hs'] using hε
  rcases t.eq_empty_or_nonempty with rfl | htne
  · simpa [subset_empty.mp ht'] using hε
  -- Subsets of relative size at least `ε > 0` of nonempty sets are nonempty.
  have hs'ne : s'.Nonempty := card_pos.mp <| Nat.cast_pos.mp <|
    (mul_pos (Nat.cast_pos.mpr hsne.card_pos) hε).trans_le hs
  have ht'ne : t'.Nonempty := card_pos.mp <| Nat.cast_pos.mp <|
    (mul_pos (Nat.cast_pos.mpr htne.card_pos) hε).trans_le ht
  have hc : (Gᶜ.edgeDensity s t : 𝕜) = 1 - G.edgeDensity s t := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact_mod_cast G.edgeDensity_add_edgeDensity_compl hsne htne hst
  have hc' : (Gᶜ.edgeDensity s' t' : 𝕜) = 1 - G.edgeDensity s' t' := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact_mod_cast G.edgeDensity_add_edgeDensity_compl hs'ne ht'ne (hst.mono hs' ht')
  rw [hc, hc', sub_sub_sub_cancel_left, abs_sub_comm]
  exact h hs' ht' hs ht

/-- For disjoint vertex sets, uniformity in `G` and in `Gᶜ` coincide. -/
theorem isUniform_compl_iff (hst : Disjoint s t) : Gᶜ.IsUniform ε s t ↔ G.IsUniform ε s t := by
  refine ⟨fun h => ?_, fun h => h.compl hst⟩
  classical
  simpa using h.compl hst

end SimpleGraph
