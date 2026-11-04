/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Stability of top regularity under recoloring

Top regularity is stable under edits measured relative to the support of the polyad, not the
whole host. If at most an `η`-fraction of that support changes color, each color density
changes by at most `η` on the parent support and by at most `η / δ'` on a test support of
relative size at least `δ'`. Thus `(δ, r)`-regularity transfers whenever
`δ' > 0` and `δ + η + η / δ' ≤ δ'`.

In particular, editing at most a `δ²`-fraction of a polyad preserves top regularity with the
parameter doubled, at the same rank. These estimates allow the errors of recoloring and
rebalancing to be accounted for separately from regularization. They include empty supports,
repeated vertex cells, and arbitrary top palettes.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), for the edited-approximation setting.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V]
  {S : PairSkeleton3 κ₂ V} {P : Polyad3 S} {H H' : Colored3Graph κ V}
  {δ δ' η : ℝ} {r : ℕ}

/-- Top regularity survives recoloring an `η`-fraction of the polyad support provided the new
parameter absorbs both the parent-density error `η` and the test-density error `η / δ'`.
The rank is unchanged, and edits are counted as ordered injective triples in the support. -/
theorem IsTopRegularOverPolyad.of_card_edits_le (h : H.IsTopRegularOverPolyad P δ r)
    (hη : 0 ≤ η) (hδ' : 0 < δ')
    (hbudget : δ + η + η / δ' ≤ δ')
    (hedit : (#{x ∈ P.support |
      H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
        H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) ≤ η * #P.support) :
    H'.IsTopRegularOverPolyad P δ' r := by
  classical
  have hδδ' : δ ≤ δ' := by linarith [div_nonneg hη hδ'.le]
  refine isTopRegularOverPolyad_iff.2 fun c Q hQ ↦ ?_
  have hparent : |(H.relDensityOn c P.support : ℝ) - H'.relDensityOn c P.support| ≤ η := by
    simpa using H.abs_relDensityOn_sub_le_of_subset H' c (Subset.refl P.support) hη
      zero_lt_one (by simp) hedit
  have htest : |(H'.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ) -
      H.relDensityOn c (Subpolyad3.unionSupport Q)| ≤ η / δ' := by
    rw [abs_sub_comm]
    exact H.abs_relDensityOn_sub_le_of_subset H' c (Subpolyad3.unionSupport_subset Q)
      hη hδ' hQ hedit
  have hreg := isTopRegularOverPolyad_iff.1 h c Q
    ((mul_le_mul_of_nonneg_right hδδ' (Nat.cast_nonneg _)).trans hQ)
  rw [relativeDensity_def] at hreg ⊢
  calc _ ≤ |(H'.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ) -
        H.relDensityOn c (Subpolyad3.unionSupport Q)| +
      |(H.relDensityOn c (Subpolyad3.unionSupport Q) : ℝ) - H'.relDensityOn c P.support| :=
        abs_sub_le _ _ _
    _ ≤ η / δ' + (δ + η) := add_le_add htest
      ((abs_sub_le _ (H.relDensityOn c P.support : ℝ) _).trans (add_le_add hreg hparent))
    _ ≤ δ' := by linarith

/-- Editing at most a `δ²`-fraction of a polyad's supported ordered triples preserves its top
regularity at every rank, with the tolerance doubled. No upper bound on `δ` is needed. -/
theorem IsTopRegularOverPolyad.of_card_edits_le_sq (h : H.IsTopRegularOverPolyad P δ r)
    (hδ : 0 < δ)
    (hedit : (#{x ∈ P.support |
      H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
        H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) ≤ δ ^ 2 * #P.support) :
    H'.IsTopRegularOverPolyad P (2 * δ) r := by
  by_cases hlarge : 1 ≤ 2 * δ
  · exact isTopRegularOverPolyad_of_one_le (H := H') (P := P) (r := r) hlarge
  refine h.of_card_edits_le (sq_nonneg δ) (by positivity) ?_ hedit
  have hdiv : δ ^ 2 / (2 * δ) = δ / 2 := by field_simp
  rw [hdiv]
  nlinarith

end TauCeti.Colored3Graph
