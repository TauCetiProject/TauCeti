/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Stability
public import TauCeti.Combinatorics.Hypergraph.Triadic.ExceptionalPrediction
public import TauCeti.Combinatorics.Hypergraph.Triadic.Nontransversal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Decomposing the error of induced counting over a triadic complex

Fix a triadic complex `C` on `V` whose selected polyads decompose the injective triples, a
colored three-uniform pattern `F` on `k = F.k` vertices, and a coloring `H` of the triples of `V`.
The induced count `H.inducedCopyCount F` is the sum of the placed counts over all placements and
routes, and the prediction `H.expectedInducedCount C F` is the sum of the local predictions over
the same index set. This file splits the difference of these two sums according to the kind of
placement and route, and bounds each part:

* along the top-regular routes of transversal placements, the local counting errors remain;
* along the routes of transversal placements that are not `(η, r)`-top-regular, the actual copies
  are embeddings meeting an exceptional polyad
  (`Colored3Graph.sum_lowerRouteCountAt_not_isTopRegularRoute_le`), and the predictions add up to
  the exceptional predicted mass `H.exceptionalPredictedMass3 C F η r`;
* at the nontransversal placements, the actual copies are embeddings putting two pattern
  vertices in a common cell (`Colored3Graph.sum_placedInducedCopyCount_of_not_transversal_le`),
  and the predictions add up to `H.nontransversalPredictedMass3 C F`.

The actual and predicted counts of the discarded parts are both nonnegative, so each of them is
charged once. This is `Colored3Graph.abs_inducedCopyCount_sub_expectedInducedCount_le`.

Combined with the edit transfer `Colored3Graph.inducedCopyCount_edit_transfer` from a coloring
`H` to an approximation `H'`, the lower-route counting bound for the exceptional predicted mass
(`Colored3Graph.exceptional_route_prediction_mass_le`) and the diagonal floor
(`Colored3Graph.nontransversal_actual_and_predicted_mass_le`), this reduces induced counting
in `H` against the prediction of `H'` to a uniform local counting bound along the top-regular
routes of `H'` (`Colored3Graph.abs_inducedCopyCount_sub_expectedInducedCount_le_of_placed_le`).
A local bound `e` times the cell-size product is paid once for each of the at most
`m ^ (k choose 2)` routes of a placement, where `m` is the number of pair colors, and the
cell-size products of the placements add up to `|V| ^ k`.

## Main results

* `TauCeti.Colored3Graph.abs_inducedCopyCount_sub_expectedInducedCount_le`: the induced counting
  error is at most the local errors along top-regular transversal routes plus the actual and
  predicted masses of the exceptional routes and of the nontransversal placements.
* `TauCeti.Colored3Graph.abs_inducedCopyCount_sub_expectedInducedCount_le_of_placed_le`: a local
  counting bound along the top-regular transversal routes of an approximation `H'` gives a
  global estimate of the induced count of `H` against the prediction of `H'`.

## References

* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Function

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V] {C : TriadicComplex3 V}
  {F : FiniteColored3Pattern κ}

namespace Colored3Graph

variable (H : Colored3Graph κ V)

variable [DecidableEq κ]

variable (F) in
open Classical in
/-- **Decomposing the induced counting error.** Over a polyad decomposition, the difference
between the induced count of `F` in `H` and its prediction is at most the sum of three parts:
the local counting errors along the `(η, r)`-top-regular routes of the transversal placements;
the exceptional routes, with at most `k.choose 3 * H.exceptionalPolyadMass C η r * |V| ^ k`
actual copies plus the exceptional predicted mass; and the nontransversal placements, with the
embeddings putting two pattern vertices in a common cell plus the nontransversal predicted
mass. -/
theorem abs_inducedCopyCount_sub_expectedInducedCount_le (hC : C.IsPolyadDecomposition)
    (η : ℝ) (r : ℕ) :
    |(H.inducedCopyCount F : ℝ) - H.expectedInducedCount C F| ≤
      ∑ φ : PatternPlacement3 C F with φ.Transversal,
          ∑ ψ : PairColorPlacement3 φ with ψ.IsTopRegularRoute H η r,
            |(H.placedInducedCopyCount φ ψ : ℝ) - H.expectedInducedCountAt φ ψ| +
        (F.k.choose 3 * H.exceptionalPolyadMass C η r * (Fintype.card V : ℝ) ^ F.k +
          H.exceptionalPredictedMass3 C F η r) +
        (#{f : Fin F.k ↪ V | ∃ i j, i ≠ j ∧
            ∃ A ∈ C.skeleton.vertexPart.parts, f i ∈ A ∧ f j ∈ A} +
          H.nontransversalPredictedMass3 C F) := by
  -- The actual copies along the exceptional routes of transversal placements.
  have hexc : ∑ φ : PatternPlacement3 C F with φ.Transversal,
      ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r,
        (H.placedInducedCopyCount φ ψ : ℝ) ≤
          F.k.choose 3 * H.exceptionalPolyadMass C η r * (Fintype.card V : ℝ) ^ F.k := by
    refine le_trans ?_ (H.sum_lowerRouteCountAt_not_isTopRegularRoute_le C F η r)
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun φ _ _ ↦
      sum_nonneg fun ψ _ ↦ Nat.cast_nonneg _).trans
        (sum_le_sum fun φ _ ↦ sum_le_sum fun ψ _ ↦ ?_)
    exact_mod_cast H.placedInducedCopyCount_le_lowerRouteCountAt φ ψ
  -- The actual copies at nontransversal placements.
  have hnon : ∑ φ : PatternPlacement3 C F with ¬φ.Transversal,
      ∑ ψ : PairColorPlacement3 φ, (H.placedInducedCopyCount φ ψ : ℝ) ≤
        #{f : Fin F.k ↪ V | ∃ i j, i ≠ j ∧
          ∃ A ∈ C.skeleton.vertexPart.parts, f i ∈ A ∧ f j ∈ A} := by
    exact_mod_cast H.sum_placedInducedCopyCount_of_not_transversal_le
  -- Split the error by the kind of placement, and then by the kind of route.
  have hsplit : (H.inducedCopyCount F : ℝ) - H.expectedInducedCount C F =
      ∑ φ : PatternPlacement3 C F with φ.Transversal,
          ∑ ψ : PairColorPlacement3 φ with ψ.IsTopRegularRoute H η r,
            ((H.placedInducedCopyCount φ ψ : ℝ) - H.expectedInducedCountAt φ ψ) +
        (∑ φ : PatternPlacement3 C F with φ.Transversal,
            ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r,
              (H.placedInducedCopyCount φ ψ : ℝ) -
          H.exceptionalPredictedMass3 C F η r) +
        (∑ φ : PatternPlacement3 C F with ¬φ.Transversal,
            ∑ ψ : PairColorPlacement3 φ, (H.placedInducedCopyCount φ ψ : ℝ) -
          H.nontransversalPredictedMass3 C F) := by
    rw [H.inducedCopyCount_eq_sum_placedInducedCopyCount hC, expectedInducedCount_def,
      exceptionalPredictedMass3_def, nontransversalPredictedMass3_def]
    push_cast
    simp only [← sum_sub_distrib]
    rw [← sum_filter_add_sum_filter_not univ fun φ ↦ φ.Transversal, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun φ _ ↦ (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun φ _ ↦ abs_sum_le_sum_abs _ _)
  · have := H.exceptionalPredictedMass3_nonneg C F η r
    have : 0 ≤ ∑ φ : PatternPlacement3 C F with φ.Transversal,
        ∑ ψ : PairColorPlacement3 φ with ¬ψ.IsTopRegularRoute H η r,
          (H.placedInducedCopyCount φ ψ : ℝ) :=
      sum_nonneg fun φ _ ↦ sum_nonneg fun ψ _ ↦ Nat.cast_nonneg _
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · have := H.nontransversalPredictedMass3_nonneg C F
    have : 0 ≤ ∑ φ : PatternPlacement3 C F with ¬φ.Transversal,
        ∑ ψ : PairColorPlacement3 φ, (H.placedInducedCopyCount φ ψ : ℝ) :=
      sum_nonneg fun φ _ ↦ sum_nonneg fun ψ _ ↦ Nat.cast_nonneg _
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

open Classical in
/-- **Induced counting from local counting.** Let `C` be a polyad decomposition with an
`ε`-regular lower skeleton and at least `diagonalControl3 k δ` equitable vertex cells, where `k`
is the number of pattern vertices, and let `H'` be a coloring of the triples whose placed counts
along the `(η, r)`-top-regular routes of transversal placements are within `e` times the cell-size
product of their predictions. Then the induced count of `F` in any coloring `H` differs from the
prediction of `H'` by at most
`(k.choose 3 * d + m ^ (k.choose 2) * e + 2 * k.choose 3 * μ + m ^ (k.choose 2) * k.choose 2 * ε
+ δ / 6) * |V| ^ k`, where `d` is the edit discrepancy between `H` and `H'`, `m` is the number of
pair colors and `μ` is the exceptional polyad mass of `H'`. -/
theorem abs_inducedCopyCount_sub_expectedInducedCount_le_of_placed_le {H' : Colored3Graph κ V}
    (hC : C.IsPolyadDecomposition) {ε δ e η : ℝ} {r : ℕ} (hε : 0 ≤ ε)
    (hreg : C.skeleton.IsPairColorRegular ε) (hδ : 0 < δ)
    (hcells : C.VertexCellsControlled (diagonalControl3 F.k δ)) (he : 0 ≤ e)
    (hlocal : ∀ φ : PatternPlacement3 C F, φ.Transversal → ∀ ψ : PairColorPlacement3 φ,
      ψ.IsTopRegularRoute H' η r →
        |(H'.placedInducedCopyCount φ ψ : ℝ) - H'.expectedInducedCountAt φ ψ| ≤
          e * ∏ i, (#(φ.vertexCell i) : ℝ)) :
    |(H.inducedCopyCount F : ℝ) - H'.expectedInducedCount C F| ≤
      (F.k.choose 3 * H.editDiscrepancy3 H' + C.pairColorCount ^ F.k.choose 2 * e +
        2 * F.k.choose 3 * H'.exceptionalPolyadMass C η r +
        C.pairColorCount ^ F.k.choose 2 * F.k.choose 2 * ε + δ / 6) *
        (Fintype.card V : ℝ) ^ F.k := by
  have hB (φ : PatternPlacement3 C F) : 0 ≤ e * ∏ i, (#(φ.vertexCell i) : ℝ) :=
    mul_nonneg he (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  have hsumB : ∑ φ : PatternPlacement3 C F, ∏ i, (#(φ.vertexCell i) : ℝ) =
      (Fintype.card V : ℝ) ^ F.k := by
    exact_mod_cast PatternPlacement3.sum_prod_card_vertexCell (C := C) (F := F)
  -- The local bound is paid once for each of the at most `m ^ (k choose 2)` routes of a
  -- placement, and the cell-size products of the placements add up to `|V| ^ k`.
  have hloc : ∑ φ : PatternPlacement3 C F with φ.Transversal,
      ∑ ψ : PairColorPlacement3 φ with ψ.IsTopRegularRoute H' η r,
        |(H'.placedInducedCopyCount φ ψ : ℝ) - H'.expectedInducedCountAt φ ψ| ≤
          C.pairColorCount ^ F.k.choose 2 * e * (Fintype.card V : ℝ) ^ F.k := by
    calc _ ≤ ∑ φ : PatternPlacement3 C F with φ.Transversal,
          ∑ ψ : PairColorPlacement3 φ with ψ.IsTopRegularRoute H' η r,
            e * ∏ i, (#(φ.vertexCell i) : ℝ) :=
          sum_le_sum fun φ hφ ↦ sum_le_sum fun ψ hψ ↦
            hlocal φ (mem_filter.1 hφ).2 ψ (mem_filter.1 hψ).2
      _ ≤ ∑ φ : PatternPlacement3 C F,
          (C.pairColorCount ^ F.k.choose 2 : ℝ) * (e * ∏ i, (#(φ.vertexCell i) : ℝ)) := by
          refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun φ _ _ ↦
            sum_nonneg fun _ _ ↦ hB φ).trans (sum_le_sum fun φ _ ↦ ?_)
          rw [sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (hB φ)
          exact_mod_cast (card_filter_le _ _).trans PairColorPlacement3.card_le_pairColorCount_pow
      _ = C.pairColorCount ^ F.k.choose 2 * e * (Fintype.card V : ℝ) ^ F.k := by
          rw [← mul_sum, ← mul_sum, hsumB, mul_assoc]
  have hcore := H'.abs_inducedCopyCount_sub_expectedInducedCount_le F hC η r
  have hedit := H.inducedCopyCount_edit_transfer H' F
  have hpred := exceptional_route_prediction_mass_le (H := H') (F := F) hε hreg η r
  have hnon := H'.nontransversal_actual_and_predicted_mass_le hδ hcells
  have htri := abs_sub_le (H.inducedCopyCount F : ℝ) (H'.inducedCopyCount F)
    (H'.expectedInducedCount C F)
  linear_combination htri + hedit + hcore + hloc + hpred + hnon

end Colored3Graph

end TauCeti
