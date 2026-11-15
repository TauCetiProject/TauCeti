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
* Over `⊥`, `stepGraphonOfFinpartition` at `G.edgeDensityIcc` recovers `finiteGraphGraphon G`.
* Over the unequal parts `{0}` and `{1, 2}` of `K₃`, `stepGraphonOfFinpartition` integrates to
  `1 / 18` on the cells of `{1}` and `{2}`.
* On a nonempty finite vertex type, the canonical equivalence with `Fin (Fintype.card V)` gives the
  comparison through `SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_comap_symm`.
* For the empty host `Fin 0`, both the finite cut discrepancy and the graphon cut-norm error vanish.
-/

open Finset MeasureTheory TauCeti.unitInterval

namespace TauCeti.DenseGraphLimits

example {m : ℕ} [NeZero m] (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] :
    cutNorm volume ((finiteGraphGraphon G).toSymmKernel - (stepGraphonAvg (μ := volume)
      (⊥ : Finpartition (univ : Finset (Fin m))).cellPartition
      (Finpartition.measurableSet_of_mem_cellPartition _) (finiteGraphGraphon G)).toSymmKernel) =
      0 := by
  rw [SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg, SimpleGraph.cutDiscrepancy_bot,
    zero_div]

-- Over `⊥`, `stepGraphonOfFinpartition` at `G.edgeDensityIcc` recovers `finiteGraphGraphon G`.
example {m : ℕ} [NeZero m] (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] :
    stepGraphonOfFinpartition (⊥ : Finpartition (univ : Finset (Fin m)))
      (fun A B => G.edgeDensityIcc A.1 B.1) (fun A B => G.edgeDensityIcc_comm A.1 B.1) =
      finiteGraphGraphon G :=
  G.stepGraphonOfFinpartition_bot_edgeDensityIcc

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

-- Unequal parts `{0}` and `{1, 2}` on `K₃`: over the cells of `{1}` and `{2}`,
-- `stepGraphonOfFinpartition` integrates to `(1 / 2) / 9 = 1 / 18`.
example :
    let P : Finpartition (univ : Finset (Fin 3)) :=
      { parts := {{0}, {1, 2}}
        supIndep := (Finset.supIndep_pair (by decide)).2 (by decide)
        sup_parts := by decide
        bot_notMem := by decide }
    (stepGraphonOfFinpartition P
      (fun A B => (⊤ : SimpleGraph (Fin 3)).edgeDensityIcc A.1 B.1)
      (fun A B => (⊤ : SimpleGraph (Fin 3)).edgeDensityIcc_comm A.1 B.1)).toSymmKernel.rectIntegral
        volume (cellFin 3 ⁻¹' ({1} : Finset (Fin 3))) (cellFin 3 ⁻¹' ({2} : Finset (Fin 3))) =
      1 / 18 := by
  intro P
  rw [SimpleGraph.rectIntegral_stepGraphonOfFinpartition_edgeDensityIcc_preimage,
    SimpleGraph.steppedCount_def]
  have hne : ({0} : Finset (Fin 3)) ≠ {1, 2} := by decide
  simp only [P, sum_pair hne, SimpleGraph.edgeDensity_def]
  have h01 : ({1} ∩ {0} : Finset (Fin 3)) = ∅ := by decide
  have h02 : ({2} ∩ {0} : Finset (Fin 3)) = ∅ := by decide
  have hB1 : #({1} ∩ {1, 2} : Finset (Fin 3)) = 1 := by decide
  have hB2 : #({2} ∩ {1, 2} : Finset (Fin 3)) = 1 := by decide
  have hBB : #((⊤ : SimpleGraph (Fin 3)).interedges {1, 2} {1, 2}) = 2 := by decide
  have hB : #({1, 2} : Finset (Fin 3)) = 2 := by decide
  rw [h01, h02]
  simp only [card_empty, CharP.cast_eq_zero, mul_zero, zero_mul, add_zero, zero_add]
  rw [hB1, hB2, hBB, hB]
  norm_num

-- On a nonempty finite vertex type, `Fintype.equivFin V` transports the cut-norm comparison.
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset V)) :
    haveI : NeZero (Fintype.card V) := ⟨Fintype.card_ne_zero⟩
    cutNorm volume ((finiteGraphGraphon (G.comap (Fintype.equivFin V).symm)).toSymmKernel -
      (stepGraphonAvg (μ := volume)
        ((P.copy (image_univ_equiv (Fintype.equivFin V).symm).symm).comap
          (Fintype.equivFin V).symm).cellPartition
        (Finpartition.measurableSet_of_mem_cellPartition _)
        (finiteGraphGraphon (G.comap (Fintype.equivFin V).symm))).toSymmKernel) =
      G.cutDiscrepancy P / (Fintype.card V : ℝ) ^ 2 :=
  G.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_comap_symm _ P

-- Empty host: both the finite cut discrepancy and the graphon cut-norm error vanish on `Fin 0`.
example (G : SimpleGraph (Fin 0)) [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin 0))) :
    G.cutDiscrepancy P = 0 := by
  simp

example (G : SimpleGraph (Fin 0)) (Q : Finpartition (Set.univ : Set unitInterval))
    (hQ : ∀ p ∈ Q.parts, MeasurableSet p) :
    cutNorm volume ((finiteGraphGraphon G).toSymmKernel -
      (stepGraphonAvg Q hQ (finiteGraphGraphon G)).toSymmKernel) = 0 := by
  have havg : stepGraphonAvg Q hQ (Graphon.const volume 0) = Graphon.const volume 0 := by
    ext x y
    rw [stepGraphonAvg_apply Q hQ _ (Q.indexedPartition.mem_index x)
      (Q.indexedPartition.mem_index y)]
    simp
  rw [finiteGraphGraphon_eq_const_zero, havg, sub_self, cutNorm_zero]

end TauCeti.DenseGraphLimits
