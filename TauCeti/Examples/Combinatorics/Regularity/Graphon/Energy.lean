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
  rw [show #((⊤ : SimpleGraph (Fin 2)).interedges {0} {0}) = 0 by decide,
    show #((⊤ : SimpleGraph (Fin 2)).interedges {0} {1}) = 1 by decide,
    show #((⊤ : SimpleGraph (Fin 2)).interedges {1} {0}) = 1 by decide,
    show #((⊤ : SimpleGraph (Fin 2)).interedges {1} {1}) = 0 by decide]
  norm_num

example : graphonPartitionEnergy volume
    (Finpartition.indiscrete (univ_nonempty (α := Fin 2)).ne_empty).cellPartition
    (Finpartition.measurableSet_of_mem_cellPartition _)
      (finiteGraphGraphon (⊤ : SimpleGraph (Fin 2))) = 1 / 4 := by
  rw [SimpleGraph.graphonPartitionEnergy_finiteGraphGraphon, SimpleGraph.weightedEnergy_def]
  simp only [Finpartition.indiscrete_parts, sum_singleton, SimpleGraph.edgeDensity_def,
    Fintype.card_fin]
  rw [show #((⊤ : SimpleGraph (Fin 2)).interedges univ univ) = 2 by decide,
    show #(univ : Finset (Fin 2)) = 2 by decide]
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
  simp only [P, sum_pair (show ({0} : Finset (Fin 3)) ≠ {1, 2} by decide),
    SimpleGraph.edgeDensity_def, Fintype.card_fin]
  rw [show #((⊤ : SimpleGraph (Fin 3)).interedges {0} {0}) = 0 by decide,
    show #((⊤ : SimpleGraph (Fin 3)).interedges {0} {1, 2}) = 2 by decide,
    show #((⊤ : SimpleGraph (Fin 3)).interedges {1, 2} {0}) = 2 by decide,
    show #((⊤ : SimpleGraph (Fin 3)).interedges {1, 2} {1, 2}) = 2 by decide,
    show #({0} : Finset (Fin 3)) = 1 by decide, show #({1, 2} : Finset (Fin 3)) = 2 by decide]
  norm_num

-- The part of the lifted partition containing a point, selected by the canonical index, is the
-- union of the cells over the part of `P` containing that point's cell.
example {m : ℕ} [NeZero m] (P : Finpartition (univ : Finset (Fin m))) (x : unitInterval) :
    (P.cellPartition.indexedPartition.index x : Set unitInterval) =
      TauCeti.unitInterval.cellFin m ⁻¹'
        (P.part (TauCeti.unitInterval.cellFin m x) : Set (Fin m)) :=
  congrArg Subtype.val (P.cellPartition.indexedPartition.mem_iff_index_eq.1
    (show x ∈ ((⟨_, P.preimage_part_cellFin_mem x⟩ : P.cellPartition.parts) : Set unitInterval)
      from P.mem_part (mem_univ _)))

end TauCeti.DenseGraphLimits
