/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
import TauCeti.Combinatorics.SimpleGraph.Density

/-!
# Uniform pairs: complements and discrepancy

Between two disjoint vertex sets, every vertex pair is an edge of exactly one of `G` and `Gᶜ`,
so on nonempty sets the two edge densities sum to one. Consequently an `ε`-uniform pair of
disjoint sets in `G` is also `ε`-uniform in `Gᶜ`. Disjointness is needed: within a single set the
diagonal pairs are edges of neither graph.

An `ε`-uniform pair `(s, t)` also has small *rectangle discrepancy*: the number of edges between
`s' ⊆ s` and `t' ⊆ t` is within `ε |s| |t|` of `d(s, t) |s'| |t'|`. Large rectangles are
controlled by uniformity itself, and small ones because both counts are then at most
`|s'| |t'| ≤ ε |s| |t|`. Testing against functions with values in `[0, 1]` instead of indicator
functions does not increase the discrepancy (`Finset.abs_sum_sum_mul_mul_le_of_forall_subset`).
Neither bound needs the sets to be disjoint.

## Main results

* `SimpleGraph.IsUniform.compl`: uniformity of disjoint sets passes to the complement graph.
* `SimpleGraph.IsUniform.abs_card_interedges_sub_le`: rectangle discrepancy of a uniform pair.
* `SimpleGraph.IsUniform.abs_sum_sum_mul_sub_le`: the same bound for tests with values in `[0, 1]`.
-/

public section

open Finset

namespace SimpleGraph

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {G : SimpleGraph α} [DecidableRel G.Adj] {ε : 𝕜} {s t s' t' : Finset α}

section DecidableEq

variable [DecidableEq α]

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

end DecidableEq

/-- **Rectangle discrepancy of a uniform pair.** If `(s, t)` is `ε`-uniform, then for all `s' ⊆ s`
and `t' ⊆ t` the number of edges between `s'` and `t'` is within `ε |s| |t|` of the count
`d(s, t) |s'| |t'|` predicted by the density of `(s, t)`. -/
theorem IsUniform.abs_card_interedges_sub_le (h : G.IsUniform ε s t) (hs' : s' ⊆ s)
    (ht' : t' ⊆ t) :
    |(#(G.interedges s' t') : 𝕜) - G.edgeDensity s t * #s' * #t'| ≤ ε * #s * #t := by
  have hε := h.pos
  have hs : (#s' : 𝕜) ≤ #s := by exact_mod_cast card_le_card hs'
  have ht : (#t' : 𝕜) ≤ #t := by exact_mod_cast card_le_card ht'
  by_cases hbig : (#s : 𝕜) * ε ≤ #s' ∧ (#t : 𝕜) * ε ≤ #t'
  · have hcard : (#(G.interedges s' t') : 𝕜) = G.edgeDensity s' t' * (#s' * #t') := by
      rw [mul_comm]
      exact_mod_cast (G.card_mul_card_mul_edgeDensity s' t').symm
    rw [hcard, mul_assoc (G.edgeDensity s t : 𝕜), ← sub_mul,
      abs_mul, abs_of_nonneg (a := (#s' : 𝕜) * #t') (by positivity), mul_assoc]
    exact mul_le_mul (h hs' ht' hbig.1 hbig.2).le (mul_le_mul hs ht (by positivity)
      (by positivity)) (by positivity) hε.le
  · have hsmall : (#s' : 𝕜) * #t' ≤ ε * #s * #t := by
      rcases not_and_or.1 hbig with hb | hb
      · calc (#s' : 𝕜) * #t' ≤ (#s * ε) * #t :=
              mul_le_mul (not_le.1 hb).le ht (by positivity) (by positivity)
          _ = ε * #s * #t := by ring
      · calc (#s' : 𝕜) * #t' ≤ #s * (#t * ε) :=
              mul_le_mul hs (not_le.1 hb).le (by positivity) (by positivity)
          _ = ε * #s * #t := by ring
    refine (abs_sub_le_of_nonneg_of_le (by positivity) ?_ ?_ ?_).trans hsmall
    · exact_mod_cast G.card_interedges_le_mul s' t'
    · exact mul_nonneg (mul_nonneg (by exact_mod_cast G.edgeDensity_nonneg s t)
        (by positivity)) (by positivity)
    · rw [mul_assoc]
      exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast G.edgeDensity_le_one s t)

/-- **Test-function discrepancy of a uniform pair.** If `(s, t)` is `ε`-uniform, then testing the
deviation of the adjacency indicator from the density `d(s, t)` against functions `f` on `s` and
`g` on `t` with values in `[0, 1]` gives at most `ε |s| |t|`. -/
theorem IsUniform.abs_sum_sum_mul_sub_le (h : G.IsUniform ε s t) {f g : α → 𝕜}
    (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hf₁ : ∀ x ∈ s, f x ≤ 1) (hg₀ : ∀ y ∈ t, 0 ≤ g y)
    (hg₁ : ∀ y ∈ t, g y ≤ 1) :
    |∑ x ∈ s, ∑ y ∈ t, f x * g y * ((if G.Adj x y then 1 else 0) - G.edgeDensity s t)| ≤
      ε * #s * #t := by
  refine abs_sum_sum_mul_mul_le_of_forall_subset hf₀ hf₁ hg₀ hg₁ fun s' hs' t' ht' ↦ ?_
  convert h.abs_card_interedges_sub_le hs' ht' using 2
  rw [interedges, Rel.interedges, ← sum_boole, sum_product]
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

end SimpleGraph
