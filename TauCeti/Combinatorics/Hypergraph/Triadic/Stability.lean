/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Stability
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
import Mathlib.Tactic.Linarith

/-!
# Stability of exceptional polyad mass under recoloring

Suppose a coloring is `(δ, r)`-top-regular outside an `ε`-fraction of the selected polyad
support. If recoloring changes at most an `η δ²`-fraction of that support, the resulting
coloring is `(2δ, r)`-top-regular outside an `(ε + η)`-fraction. Indeed, polyads on which more
than a `δ²`-fraction of the support is edited carry at most an `η`-fraction of the total mass;
on every other previously regular polyad, local edit stability applies.

This estimate budgets nonuniformly distributed recoloring errors in regular approximation.
It does not require a polyad decomposition, equitable cells, or a nonempty host: both the edit
budget and the exceptional mass are measured over the selected supports.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), for regular approximation by editing.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V]
  {C : TriadicComplex3 V} {H H' : Colored3Graph κ V} {δ ε η : ℝ} {r : ℕ}

open Classical in
/-- Editing an `η δ²`-fraction of the selected support increases the exceptional proportion
by at most `η` when the top-regularity tolerance is doubled. The local edit proportions need
not be uniformly bounded, and the rank is preserved. -/
theorem TopRegularOverMostPolyads.of_sum_card_edits_le
    (h : H.TopRegularOverMostPolyads C δ ε r) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hedit : (∑ P ∈ C.polyads,
      (#{x ∈ P.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
        H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ)) ≤
      η * δ ^ 2 * ∑ P ∈ C.polyads, (#P.support : ℝ)) :
    H'.TopRegularOverMostPolyads C (2 * δ) (ε + η) r := by
  have hold := (topRegularOverMostPolyads_iff_sum_card_support_le h.nonneg).1 h
  apply (topRegularOverMostPolyads_iff_sum_card_support_le (add_nonneg h.nonneg hη)).2
  -- Charge a newly irregular polyad either to its old irregularity or to its edits.
  have hweighted : δ ^ 2 *
      (∑ P ∈ C.polyads with ¬H'.IsTopRegularOverPolyad P (2 * δ) r, (#P.support : ℝ)) ≤
      δ ^ 2 * (∑ P ∈ C.polyads with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
        ∑ P ∈ C.polyads,
          (#{x ∈ P.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
            H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) := by
    simp only [sum_filter, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun P _ ↦ ?_
    by_cases hnew : H'.IsTopRegularOverPolyad P (2 * δ) r
    · simp only [hnew, not_true_eq_false, ite_false, mul_zero]
      positivity
    by_cases hprev : H.IsTopRegularOverPolyad P δ r
    · have hheavy : δ ^ 2 * #P.support ≤
          (#{x ∈ P.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
            H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) := by
        by_contra! hlight
        exact hnew (hprev.of_card_edits_le_sq hδ hlight.le)
      simpa only [hnew, hprev, not_false_eq_true, not_true_eq_false, ite_true, ite_false,
        mul_zero, zero_add] using hheavy
    · simp only [hnew, hprev, not_false_eq_true, ite_true, le_add_iff_nonneg_right]
      exact Nat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hold (sq_nonneg δ)
  -- The positive factor `δ²` cancels, including when the total selected support is zero.
  nlinarith [sq_pos_of_pos hδ]

end TauCeti.Colored3Graph
