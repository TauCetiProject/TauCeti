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
* On a nonempty finite vertex type, the canonical equivalence with `Fin (Fintype.card V)` gives the
  comparison through `SimpleGraph.graphonPartitionEnergy_finiteGraphGraphon_comap_symm`.
* Relabelling along a rotation of `Fin 3` moves the parts of a partition the expected way, which
  fixes the direction of the relabelling.
* For the empty host both energies vanish: a partition of the empty vertex set has no parts, and
  the graphon of a graph on `Fin 0` is the zero graphon.
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

-- On a nonempty finite vertex type, the canonical equivalence with `Fin (Fintype.card V)` gives
-- the comparison.
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset V)) :
    haveI : NeZero (Fintype.card V) := ⟨Fintype.card_ne_zero⟩
    graphonPartitionEnergy volume
        ((P.copy (image_univ_equiv (Fintype.equivFin V).symm).symm).comap
          (Fintype.equivFin V).symm).cellPartition
        (Finpartition.measurableSet_of_mem_cellPartition _)
        (finiteGraphGraphon (G.comap (Fintype.equivFin V).symm)) =
      G.weightedEnergy P :=
  G.graphonPartitionEnergy_finiteGraphGraphon_comap_symm _ P

-- Relabelling along the rotation `0 ↦ 1 ↦ 2 ↦ 0` carries the part `{1, 2}` of the partition
-- `{0}, {1, 2}` to the part `{2, 0}`, the part through `0`. Pulling back along the rotation instead
-- of its inverse would give `{0, 1}`.
example :
    let P : Finpartition (univ : Finset (Fin 3)) :=
      { parts := {{0}, {1, 2}}
        supIndep := (Finset.supIndep_pair (by decide)).2 (by decide)
        sup_parts := by decide
        bot_notMem := by decide }
    ((P.copy (image_univ_equiv (finRotate 3).symm).symm).comap (finRotate 3).symm).part 0 =
      {0, 2} := by
  intro P
  -- the part of `P` through `2` is `{1, 2}`
  have h2 : (P.copy (image_univ_equiv (finRotate 3).symm).symm).part 2 = {1, 2} :=
    Finpartition.part_eq_of_mem _ (by simp [P]) (by decide)
  have hrot : (finRotate 3).symm 0 = 2 := by decide
  rw [Finpartition.part_comap (mem_univ _), hrot, h2]
  decide

-- The empty host: a partition of the empty vertex set has no parts, so the weighted energy is `0`.
example (G : SimpleGraph (Fin 0)) [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin 0))) :
    G.weightedEnergy P = 0 := by
  have hP : P.parts = ∅ := Finpartition.parts_eq_empty_iff.2 (by simp)
  simp [SimpleGraph.weightedEnergy_def, hP]

-- The empty host: the graphon of a graph on `Fin 0` is the zero graphon, whose partition energy
-- vanishes over every measurable partition of the unit interval. No cell map to `Fin 0` is used.
example (G : SimpleGraph (Fin 0)) (Q : Finpartition (Set.univ : Set unitInterval))
    (hQ : ∀ p ∈ Q.parts, MeasurableSet p) :
    graphonPartitionEnergy volume Q hQ (finiteGraphGraphon G) = 0 := by
  rw [finiteGraphGraphon_eq_const_zero, graphonPartitionEnergy_eq_sum]
  simp

end TauCeti.DenseGraphLimits
