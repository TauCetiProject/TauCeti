/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graphon.Energy
public import TauCeti.Combinatorics.Regularity.Graph.CutDiscrepancy
public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.CutNorm
-- Non-public: used only inside the proof below.
import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Pullback

/-!
# Finite cut discrepancy as graphon cut norm

For a graph `G` on `Fin m` with `0 < m` and a partition `P` of its vertices, the block-average
step graphon of `finiteGraphGraphon G` over the lifted partition `P.cellPartition` is
`stepGraphonOfFinpartition P` at `G.edgeDensityIcc`. Over the cells of two vertex sets `S` and `T`,
it integrates to `G.steppedCount P S T / m²`. Its distance in the rectangle cut norm from the
graphon of `G` is the count-scaled cut discrepancy of `P` divided by `m²`: the analytic
weak-regularity error of the lifted partition is the normalized finite one.

## Main results

* `SimpleGraph.rectIntegral_stepGraphonOfFinpartition_edgeDensityIcc_preimage` and
  `SimpleGraph.rectIntegral_stepGraphonAvg_finiteGraphGraphon_preimage`: over cell preimages, the
  step graphon integrates to `G.steppedCount P S T / m²`.
* `SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonOfFinpartition_edgeDensityIcc` and
  `SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg`: the cut norm of the graphon of `G`
  minus its block averages over `P.cellPartition` is `G.cutDiscrepancy P / m²`.
* `SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_le_iff`: bounding the normalized
  graphon cut-norm error by `ε` is equivalent to `G.cutDiscrepancy P ≤ ε * m²`.
* `SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_comap_symm` and
  `SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_comap_symm_le_iff`: the same
  comparison on any finite vertex type, relabelled along an equivalence with `Fin m`.

## Implementation

Both kernels are pulled back along the cell index `cellFin m : I → Fin m` via
`finiteGraphGraphon_eq_comap` and `stepGraphonOfFinpartition_eq_comap_ofMatrix`: the difference is
the pullback of the kernel on `Fin m`, with the uniform measure, that takes the adjacency value of
`G` minus the block density of `P` at each pair of vertices. The cut norm is invariant under this
measure-preserving pullback (`cutNorm_comap`), so no supremum over measurable subsets of the unit
interval needs to be computed. On `Fin m` every subset is a finset, and its rectangle integrals are
the rectangle deviations `#(G.interedges S T) - G.steppedCount P S T`, scaled by `1 / m²`.
-/

public section

open Finset MeasureTheory ProbabilityTheory TauCeti.unitInterval TauCeti.DenseGraphLimits
open scoped unitInterval

namespace SimpleGraph

variable {m : ℕ} [NeZero m]

/-- Over the cells of two vertex sets `S` and `T`, `stepGraphonOfFinpartition` at
`G.edgeDensityIcc` integrates to the stepped prediction `G.steppedCount P S T` divided by `m²`. -/
theorem rectIntegral_stepGraphonOfFinpartition_edgeDensityIcc_preimage (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m))) (S T : Finset (Fin m)) :
    (stepGraphonOfFinpartition P (fun A B => G.edgeDensityIcc A.val B.val)
        (fun A B => G.edgeDensityIcc_comm A.val B.val)).toSymmKernel.rectIntegral volume
        (cellFin m ⁻¹' (S : Set (Fin m))) (cellFin m ⁻¹' (T : Set (Fin m))) =
      G.steppedCount P S T / (m : ℝ) ^ 2 := by
  rw [rectIntegral_stepGraphonOfFinpartition_preimage, G.steppedCount_eq_sum_subtype]
  simp

/-- Over the cells of two vertex sets `S` and `T`, the block-average step graphon of
`finiteGraphGraphon G` over `P.cellPartition` integrates to `G.steppedCount P S T / m²`. -/
theorem rectIntegral_stepGraphonAvg_finiteGraphGraphon_preimage (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m))) (S T : Finset (Fin m)) :
    (stepGraphonAvg (μ := volume) P.cellPartition P.measurableSet_of_mem_cellPartition
        (finiteGraphGraphon G)).toSymmKernel.rectIntegral volume
        (cellFin m ⁻¹' (S : Set (Fin m))) (cellFin m ⁻¹' (T : Set (Fin m))) =
      G.steppedCount P S T / (m : ℝ) ^ 2 := by
  rw [G.stepGraphonAvg_finiteGraphGraphon_eq_stepGraphonOfFinpartition,
    G.rectIntegral_stepGraphonOfFinpartition_edgeDensityIcc_preimage]

/-- **Finite cut discrepancy as cut norm against `stepGraphonOfFinpartition`.** The rectangle cut
norm of `finiteGraphGraphon G` minus `stepGraphonOfFinpartition P` at `G.edgeDensityIcc` is
`G.cutDiscrepancy P / m²`. -/
theorem cutNorm_finiteGraphGraphon_sub_stepGraphonOfFinpartition_edgeDensityIcc
    (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m))) :
    cutNorm volume ((finiteGraphGraphon G).toSymmKernel -
      (stepGraphonOfFinpartition P (fun A B => G.edgeDensityIcc A.val B.val)
        (fun A B => G.edgeDensityIcc_comm A.val B.val)).toSymmKernel) =
      G.cutDiscrepancy P / (m : ℝ) ^ 2 := by
  let B : Graphon (Fin m) (uniformOn Set.univ) := Graphon.ofMatrix (uniformOn Set.univ)
    (fun i j => G.edgeDensityIcc (P.part i) (P.part j))
    (fun i j => G.edgeDensityIcc_comm (P.part i) (P.part j))
  let K : SymmKernel (Fin m) (uniformOn Set.univ) :=
    (finiteGraphGraphonOnFin G).toSymmKernel - B.toSymmKernel
  have hK : (finiteGraphGraphon G).toSymmKernel -
      (stepGraphonOfFinpartition P (fun A B => G.edgeDensityIcc A.val B.val)
        (fun A B => G.edgeDensityIcc_comm A.val B.val)).toSymmKernel =
      K.comap (cellFin m) measurable_cellFin volume := by
    rw [finiteGraphGraphon_eq_comap, stepGraphonOfFinpartition_eq_comap_ofMatrix]
    ext x y
    simp [K, B]
  rw [hK, cutNorm_comap measurePreserving_cellFin K]
  -- On `Fin m`, a rectangle integral of `K` is a rectangle deviation scaled by `1 / m²`.
  have hrect (S T : Finset (Fin m)) : K.rectIntegral (uniformOn Set.univ) S T =
      ((#(G.interedges S T) : ℝ) - G.steppedCount P S T) / (m : ℝ) ^ 2 := by
    rw [SymmKernel.rectIntegral_uniformOn_univ, Fintype.card_fin,
      steppedCount_eq_sum_edgeDensity_part]
    congr 1
    have hcount : (#(G.interedges S T) : ℝ) =
        ∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then (1 : ℝ) else 0 := by
      rw [interedges_def, card_filter, sum_product]
      simp
    rw [hcount, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun y _ => ?_
    simp [K, B]
  have hm : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (NeZero.pos m)) 2
  -- Both sides are suprema of the same rectangle deviations; compare their bounds.
  apply le_antisymm
  · refine (cutNorm_le_iff _).2 fun S _ T _ => ?_
    have h := hrect S.toFinite.toFinset T.toFinite.toFinset
    rw [Set.Finite.coe_toFinset, Set.Finite.coe_toFinset] at h
    rw [h, abs_div, abs_of_pos hm]
    exact div_le_div_of_nonneg_right
      (G.abs_card_interedges_sub_steppedCount_le_cutDiscrepancy P _ _) hm.le
  · rw [div_le_iff₀ hm]
    refine cutDiscrepancy_le_iff.2 fun S T => ?_
    have h := abs_rectIntegral_le_cutNorm _ K S T
    rwa [hrect, abs_div, abs_of_pos hm, div_le_iff₀ hm] at h

/-- **Finite cut discrepancy is graphon cut norm.** For a graph `G` on `Fin m` with `0 < m` and a
partition `P` of its vertices, the rectangle cut norm of the graphon of `G` minus its block
averages over the partition `P.cellPartition` of the unit interval is the cut discrepancy of `P`
divided by `m²`. -/
theorem cutNorm_finiteGraphGraphon_sub_stepGraphonAvg (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m))) :
    cutNorm volume ((finiteGraphGraphon G).toSymmKernel - (stepGraphonAvg (μ := volume)
      P.cellPartition P.measurableSet_of_mem_cellPartition (finiteGraphGraphon G)).toSymmKernel) =
      G.cutDiscrepancy P / (m : ℝ) ^ 2 := by
  rw [G.stepGraphonAvg_finiteGraphGraphon_eq_stepGraphonOfFinpartition,
    G.cutNorm_finiteGraphGraphon_sub_stepGraphonOfFinpartition_edgeDensityIcc]

/-- **Scaling equivalence between graphon cut norm and finite cut discrepancy.** The normalized
graphon cut-norm error over `P.cellPartition` is at most `ε` if and only if the count-scaled cut
discrepancy `G.cutDiscrepancy P` is at most `ε * m²`. -/
theorem cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_le_iff (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m))) {ε : ℝ} :
    cutNorm volume ((finiteGraphGraphon G).toSymmKernel - (stepGraphonAvg (μ := volume)
      P.cellPartition P.measurableSet_of_mem_cellPartition
      (finiteGraphGraphon G)).toSymmKernel) ≤ ε ↔
      G.cutDiscrepancy P ≤ ε * (m : ℝ) ^ 2 := by
  have hm : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (NeZero.pos m)) 2
  rw [G.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg P, div_le_iff₀ hm]

/-- **Finite cut discrepancy as graphon cut norm, on any finite vertex type.** Relabel the vertices
of `G` along an equivalence `e : V ≃ Fin m` with `0 < m`. The rectangle cut norm of the relabelled
graphon minus its block averages over the cell partition of the relabelled `P` is
`G.cutDiscrepancy P / (card V)²`. For a nonempty finite `V`, take `e := Fintype.equivFin V`. -/
theorem cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_comap_symm {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : V ≃ Fin m)
    (P : Finpartition (univ : Finset V)) :
    cutNorm volume ((finiteGraphGraphon (G.comap e.symm)).toSymmKernel -
      (stepGraphonAvg (μ := volume)
        ((P.copy (image_univ_equiv e.symm).symm).comap e.symm).cellPartition
        (Finpartition.measurableSet_of_mem_cellPartition _)
        (finiteGraphGraphon (G.comap e.symm))).toSymmKernel) =
      G.cutDiscrepancy P / (Fintype.card V : ℝ) ^ 2 := by
  rw [cutNorm_finiteGraphGraphon_sub_stepGraphonAvg, cutDiscrepancy_comap_symm,
    Fintype.card_congr e, Fintype.card_fin]

/-- **Scaling equivalence on any finite vertex type.** Along `e : V ≃ Fin m` with `0 < m`, the
graphon cut-norm error over the cell partition of the relabelled `P` is at most `ε` if and only if
`G.cutDiscrepancy P ≤ ε * (card V)²`. -/
theorem cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_comap_symm_le_iff {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : V ≃ Fin m)
    (P : Finpartition (univ : Finset V)) {ε : ℝ} :
    cutNorm volume ((finiteGraphGraphon (G.comap e.symm)).toSymmKernel -
      (stepGraphonAvg (μ := volume)
        ((P.copy (image_univ_equiv e.symm).symm).comap e.symm).cellPartition
        (Finpartition.measurableSet_of_mem_cellPartition _)
        (finiteGraphGraphon (G.comap e.symm))).toSymmKernel) ≤ ε ↔
      G.cutDiscrepancy P ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  rw [cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_le_iff, cutDiscrepancy_comap_symm,
    Fintype.card_congr e, Fintype.card_fin]

end SimpleGraph
