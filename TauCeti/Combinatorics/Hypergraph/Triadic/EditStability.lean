/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.EditStability
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic

/-!
# Exceptional polyad mass after recoloring

A small total edit count need not be small relative to every polyad. Charge polyads on which
more than an `η`-fraction of the support is edited to the total edit count, with a loss of
`1 / η`. All other polyads inherit top regularity from the original coloring. Thus recoloring
increases exceptional mass by at most the selected edit fraction divided by `η`, after the
local regularity parameter is worsened to absorb the edits.

The denominator is the total selected support, as in `exceptionalPolyadMass`, not `|V|³`.
For a polyad decomposition it is `|V|.descFactorial 3`. The estimates also hold for an arbitrary
selected family, including one of total support zero, without any nonempty-palette hypothesis.

This is the edit-error bookkeeping used when cleanup or rebalancing changes a regular
approximation; see Rödl–Schacht, *Regular partitions of hypergraphs: regularity lemmas* (2007).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {H H' : Colored3Graph κ V} {δ ε η : ℝ} {r : ℕ}

open Classical in
/-- After recoloring, the support of irregular selected polyads is bounded by the old
irregular support plus the number of selected edited triples divided by `η`. Polyads with an
edit fraction at most `η` retain regularity with the new parameter `ε`. -/
theorem sum_card_support_not_topRegular_edit_le (C : TriadicComplex3 V)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + η + η / ε ≤ ε) :
    (∑ P ∈ C.polyads with ¬H'.IsTopRegularOverPolyad P ε r, (#P.support : ℝ)) ≤
      (∑ P ∈ C.polyads with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
        (∑ P ∈ C.polyads, (#{x ∈ P.support |
          H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
            H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ)) / η := by
  classical
  rw [sum_filter, sum_filter, sum_div, ← sum_add_distrib]
  apply sum_le_sum
  intro P _
  have he : 0 ≤ (#{x ∈ P.support |
      H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
        H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) / η := by positivity
  by_cases hnew : H'.IsTopRegularOverPolyad P ε r
  · simp only [hnew, not_true_eq_false, ↓reduceIte]
    positivity
  by_cases hold : H.IsTopRegularOverPolyad P δ r
  · simp only [hnew, hold, not_true_eq_false, not_false_eq_true, ↓reduceIte, zero_add]
    apply (le_div_iff₀ hη).2
    have hbad : ¬(#{x ∈ P.support |
        H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
          H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) ≤ η * #P.support :=
      fun hed ↦ hnew (hold.edit_of_card_filter_ne_le hε hη.le hbudget hed)
    linarith [lt_of_not_ge hbad]
  · simpa only [hnew, hold, not_false_eq_true, ↓reduceIte] using le_add_of_nonneg_right he

open Classical in
/-- Recoloring increases exceptional polyad mass by at most the selected edit fraction
divided by `η`, provided the new regularity parameter absorbs local edit errors. The family
need not be a polyad decomposition, and zero total support is allowed. -/
theorem exceptionalPolyadMass_edit_le (C : TriadicComplex3 V)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + η + η / ε ≤ ε) :
    H'.exceptionalPolyadMass C ε r ≤ H.exceptionalPolyadMass C δ r +
      (∑ P ∈ C.polyads, (#{x ∈ P.support |
        H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
          H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ)) /
        (η * ∑ P ∈ C.polyads, (#P.support : ℝ)) := by
  classical
  rw [exceptionalPolyadMass_def, exceptionalPolyadMass_def]
  calc
    _ ≤ ((∑ P ∈ C.polyads with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
        (∑ P ∈ C.polyads, (#{x ∈ P.support |
          H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
            H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ)) / η) /
          (∑ P ∈ C.polyads, (#P.support : ℝ)) := by
      apply div_le_div_of_nonneg_right
      · exact sum_card_support_not_topRegular_edit_le C hε hη hbudget
      · exact sum_nonneg fun P _ ↦ Nat.cast_nonneg _
    _ = _ := by rw [add_div, div_div]

end TauCeti.Colored3Graph
