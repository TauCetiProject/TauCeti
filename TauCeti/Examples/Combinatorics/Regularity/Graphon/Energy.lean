/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Regularity.Graphon.Energy
import Mathlib.Tactic.NormNum

/-!
# Regression examples: graphon partition energy of finite graphs

These downstream examples compute graphon partition energies of finite-graph graphons through the
public bridge `SimpleGraph.graphonPartitionEnergy_finiteGraphGraphon`.

* The complete graph `K₂` over its singleton partition has energy `1 / 2`: the two off-diagonal
  blocks have density `1` and weight `1 / 4`, the diagonal blocks density `0`.
* `K₂` over its one-block partition has energy `1 / 4`: the single diagonal block has density
  `1 / 2`, since edge densities count ordered pairs over `|A|²`.
* `K₃` over the parts `{0}` and `{1, 2}` has energy `5 / 9`, which tests the size weights
  `|A||B| / m²` on unequal parts.
* The part of the lifted partition containing a point, selected by its canonical index, is the
  union of the cells over the part of `P` containing that point's cell.
-/

open Finset MeasureTheory

namespace TauCeti.DenseGraphLimits

example : graphonPartitionEnergy volume (⊥ : Finpartition (univ : Finset (Fin 2))).cellPartition
    (Finpartition.measurableSet_of_mem_cellPartition _)
      (finiteGraphGraphon (⊤ : SimpleGraph (Fin 2))) = 1 / 2 := by
  rw [SimpleGraph.graphonPartitionEnergy_finiteGraphGraphon, SimpleGraph.weightedEnergy_def]
  simp only [Finpartition.parts_bot, sum_map, Fin.sum_univ_two, Function.Embedding.coeFn_mk,
    card_singleton, Fintype.card_fin]
  simp only [SimpleGraph.edgeDensity_def, card_singleton]
  -- The edge counts are natural numbers, decided by evaluation; the rational arithmetic that
  -- remains is left to `norm_num`, since `decide` cannot evaluate rational division.
  have h00 : #((⊤ : SimpleGraph (Fin 2)).interedges {0} {0}) = 0 := by decide
  have h01 : #((⊤ : SimpleGraph (Fin 2)).interedges {0} {1}) = 1 := by decide
  have h10 : #((⊤ : SimpleGraph (Fin 2)).interedges {1} {0}) = 1 := by decide
  have h11 : #((⊤ : SimpleGraph (Fin 2)).interedges {1} {1}) = 0 := by decide
  rw [h00, h01, h10, h11]
  norm_num

example : graphonPartitionEnergy volume
    (Finpartition.indiscrete (univ_nonempty (α := Fin 2)).ne_empty).cellPartition
    (Finpartition.measurableSet_of_mem_cellPartition _)
      (finiteGraphGraphon (⊤ : SimpleGraph (Fin 2))) = 1 / 4 := by
  rw [SimpleGraph.graphonPartitionEnergy_finiteGraphGraphon, SimpleGraph.weightedEnergy_def]
  simp only [Finpartition.indiscrete_parts, sum_singleton, SimpleGraph.edgeDensity_def,
    Fintype.card_fin]
  -- Natural-number counts by evaluation, then rational arithmetic by `norm_num`.
  have hedges : #((⊤ : SimpleGraph (Fin 2)).interedges univ univ) = 2 := by decide
  have hcard : #(univ : Finset (Fin 2)) = 2 := by decide
  rw [hedges, hcard]
  norm_num

example :
    let P : Finpartition (univ : Finset (Fin 3)) :=
      { parts := {{0}, {1, 2}}
        supIndep := (Finset.supIndep_pair (by decide)).2 (by decide)
        sup_parts := by decide
        bot_notMem := by decide }
    graphonPartitionEnergy volume P.cellPartition
      (Finpartition.measurableSet_of_mem_cellPartition _)
      (finiteGraphGraphon (⊤ : SimpleGraph (Fin 3))) = 5 / 9 := by
  intro P
  rw [SimpleGraph.graphonPartitionEnergy_finiteGraphGraphon, SimpleGraph.weightedEnergy_def]
  -- The two parts are distinct, so the sum over parts is a sum over the pair.
  have hne : ({0} : Finset (Fin 3)) ≠ {1, 2} := by decide
  simp only [P, sum_pair hne, SimpleGraph.edgeDensity_def, Fintype.card_fin]
  -- Natural-number counts by evaluation, then rational arithmetic by `norm_num`.
  have h00 : #((⊤ : SimpleGraph (Fin 3)).interedges {0} {0}) = 0 := by decide
  have h0B : #((⊤ : SimpleGraph (Fin 3)).interedges {0} {1, 2}) = 2 := by decide
  have hB0 : #((⊤ : SimpleGraph (Fin 3)).interedges {1, 2} {0}) = 2 := by decide
  have hBB : #((⊤ : SimpleGraph (Fin 3)).interedges {1, 2} {1, 2}) = 2 := by decide
  have hA : #({0} : Finset (Fin 3)) = 1 := by decide
  have hB : #({1, 2} : Finset (Fin 3)) = 2 := by decide
  rw [h00, h0B, hB0, hBB, hA, hB]
  norm_num

-- The part of the lifted partition containing a point, selected by the canonical index, is the
-- union of the cells over the part of `P` containing that point's cell.
example {m : ℕ} [NeZero m] (P : Finpartition (univ : Finset (Fin m))) (x : unitInterval) :
    (P.cellPartition.indexedPartition.index x : Set unitInterval) =
      TauCeti.unitInterval.cellFin m ⁻¹'
        (P.part (TauCeti.unitInterval.cellFin m x) : Set (Fin m)) := by
  simp

end TauCeti.DenseGraphLimits
