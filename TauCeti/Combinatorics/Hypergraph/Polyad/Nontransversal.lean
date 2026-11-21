/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Equipartition
public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import TauCeti.Order.Partition.Equipartition
import TauCeti.Order.Partition.Pi

/-!
# Nontransversal polyad mass

Over an equitable vertex partition into `t` nonempty cells, each cell has size at most
`2 * |V| / t`. Every injective triple in the support of a polyad lacking distinct vertex cells
(`¬P.HasDistinctCells`) lands in two common cells under `S.vertexPart`, so counting
nontransversal ordered triples via `Finpartition.card_filter_not_injective_part_le_of_card_le`
bounds the total support cardinality of repeated-cell polyads by `6 * |V|³ / t`
(`TauCeti.Polyad3.sum_card_support_not_hasDistinctCells_le`).

## Main results

* `TauCeti.Polyad3.sum_card_support_not_hasDistinctCells_le`: repeated-cell equipartition mass
  bound `6 * |V|³ / t`.
-/

public section

open Finset

namespace TauCeti

namespace Polyad3

variable {κ V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- Repeated-cell injective triples over an equipartition into `t` nonempty cells carry at most
`6 * |V|³ / t` triples. -/
theorem sum_card_support_not_hasDistinctCells_le [Fintype κ] (S : PairSkeleton3 κ V)
    (hEq : S.vertexPart.IsEquipartition) (ht : 0 < #S.vertexPart.parts) :
    ∑ P : Polyad3 S with ¬P.HasDistinctCells, (#P.support : ℝ) ≤
      6 * (Fintype.card V : ℝ) ^ 3 / #S.vertexPart.parts := by
  set t := #S.vertexPart.parts
  set s := Fintype.card V / t
  have hm : ∀ A ∈ S.vertexPart.parts, #A ≤ 2 * s := fun A hA ↦ by
    simpa only [card_univ, s, t] using hEq.card_part_le_two_mul_div hA
  have hsum_nat : ∑ P : Polyad3 S with ¬P.HasDistinctCells, #P.support ≤
      3 * (2 * s) * Fintype.card V ^ 2 := by
    rw [← card_biUnion fun P _ Q _ hne ↦ Polyad3.pairwise_disjoint_support hne]
    calc #((univ.filter fun P : Polyad3 S ↦ ¬P.HasDistinctCells).biUnion Polyad3.support)
        ≤ #{g ∈ Fintype.piFinset (fun _ : Fin 3 ↦ (univ : Finset V)) |
            ¬Function.Injective fun i ↦ S.vertexPart.part (g i)} := by
          refine card_le_card_of_injOn (fun x ↦ x.val) (fun x hx ↦ ?_)
            (fun _ _ _ _ h ↦ Subtype.ext h)
          obtain ⟨P, hP, hxP⟩ := mem_biUnion.1 hx
          rw [mem_coe, mem_filter]
          refine ⟨Fintype.mem_piFinset.2 fun _ ↦ mem_univ _, fun hinj ↦ (mem_filter.1 hP).2 ?_⟩
          rw [Polyad3.hasDistinctCells_iff_injective_cell]
          intro i j hij
          apply hinj
          dsimp only
          have hci := ((Polyad3.mem_support_iff_cell_colorAt P x).1 hxP).1
          rw [S.vertexPart.part_eq_of_mem (P.cell_mem_parts i) (hci i),
            S.vertexPart.part_eq_of_mem (P.cell_mem_parts j) (hci j), hij]
      _ ≤ (Fintype.card (Fin 3)).choose 2 * (2 * s) *
            #(univ : Finset V) ^ (Fintype.card (Fin 3) - 1) :=
          S.vertexPart.card_filter_not_injective_part_le_of_card_le hm
      _ = 3 * (2 * s) * Fintype.card V ^ 2 := by simp [card_univ]
  have hst : (s : ℝ) * t ≤ Fintype.card V := by
    exact_mod_cast Nat.div_mul_le_self (Fintype.card V) t
  rw [le_div_iff₀ (Nat.cast_pos.2 ht)]
  calc (∑ P : Polyad3 S with ¬P.HasDistinctCells, (#P.support : ℝ)) * t
      ≤ (3 * (2 * (s : ℝ)) * (Fintype.card V : ℝ) ^ 2) * t := by gcongr; exact_mod_cast hsum_nat
    _ = 6 * ((s : ℝ) * t) * (Fintype.card V : ℝ) ^ 2 := by ring
    _ ≤ 6 * (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ 2 := by gcongr
    _ = 6 * (Fintype.card V : ℝ) ^ 3 := by ring

end Polyad3

end TauCeti
