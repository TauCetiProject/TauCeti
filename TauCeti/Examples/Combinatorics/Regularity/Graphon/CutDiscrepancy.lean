/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Regularity.Graphon.CutDiscrepancy
import Mathlib.Tactic.NormNum

/-!
# Regression examples: graphon cut norm of finite-graph block averages

These downstream examples compute cut norms of finite-graph graphons minus their block averages
through the public bridge `SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg`.

* Over the partition into singletons, the block averages recover the graphon, so the cut norm is
  `0`.
* The complete graph `K₂` over its one-block partition has cut norm `1 / 8`. The single block has
  density `1 / 2`, since edge densities count ordered pairs over `|A|²`; the rectangle `{0} × {1}`
  carries one edge against a prediction of `1 / 2`, and no rectangle deviates by more, so the cut
  discrepancy is `1 / 2`, divided by `m² = 4`.
-/

open Finset MeasureTheory

namespace TauCeti.DenseGraphLimits

example {m : ℕ} [NeZero m] (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] :
    cutNorm volume ((finiteGraphGraphon G).toSymmKernel - (stepGraphonAvg (μ := volume)
      (⊥ : Finpartition (univ : Finset (Fin m))).cellPartition
      (Finpartition.measurableSet_of_mem_cellPartition _) (finiteGraphGraphon G)).toSymmKernel) =
      0 := by
  rw [SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg, SimpleGraph.cutDiscrepancy_bot,
    zero_div]

example :
    cutNorm volume ((finiteGraphGraphon (⊤ : SimpleGraph (Fin 2))).toSymmKernel -
      (stepGraphonAvg (μ := volume) (⊤ : Finpartition (univ : Finset (Fin 2))).cellPartition
        (Finpartition.measurableSet_of_mem_cellPartition _)
        (finiteGraphGraphon (⊤ : SimpleGraph (Fin 2)))).toSymmKernel) = 1 / 8 := by
  rw [SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg]
  -- The one-block prediction is `d_G(V, V) * #A * #B`, with `d_G(V, V) = 2 / 4`.
  have hd : (⊤ : SimpleGraph (Fin 2)).edgeDensity univ univ = 1 / 2 := by
    rw [SimpleGraph.edgeDensity_def]
    have hedges : #((⊤ : SimpleGraph (Fin 2)).interedges univ univ) = 2 := by decide
    have hcard : #(univ : Finset (Fin 2)) = 2 := by decide
    rw [hedges, hcard]
    norm_num
  -- Every rectangle deviates by at most `1 / 2`: twice the edge count is within `1` of `#A * #B`.
  -- This is decided over the sixteen pairs of vertex sets, in the integers.
  have hdev : ∀ A B : Finset (Fin 2),
      |2 * (#((⊤ : SimpleGraph (Fin 2)).interedges A B) : ℤ) - #A * #B| ≤ 1 := by decide
  have hcut : (⊤ : SimpleGraph (Fin 2)).cutDiscrepancy ⊤ = 1 / 2 := by
    refine le_antisymm (SimpleGraph.cutDiscrepancy_le_iff.2 fun A B => ?_) ?_
    · rw [SimpleGraph.steppedCount_top, hd]
      have h := hdev A B
      rw [← Int.cast_le (R := ℝ)] at h
      push_cast at h
      rw [abs_le] at h ⊢
      constructor <;> linarith [h.1, h.2]
    · have h := (⊤ : SimpleGraph (Fin 2)).abs_card_interedges_sub_steppedCount_le_cutDiscrepancy ⊤
        {0} {1}
      have hedge : #((⊤ : SimpleGraph (Fin 2)).interedges {0} {1}) = 1 := by decide
      rw [SimpleGraph.steppedCount_top, hd, hedge] at h
      norm_num at h
      exact h
  rw [hcut]
  norm_num

end TauCeti.DenseGraphLimits
