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
step graphon of `finiteGraphGraphon G` over the lifted partition `P.cellPartition` takes the value
`d_G(P.part i, P.part j)` on the cells of `i` and `j`. Its distance in the rectangle cut norm from
the graphon of `G` is the count-scaled cut discrepancy of `P` divided by `m²`: the analytic
weak-regularity error of the lifted partition is the finite one.

## Main results

* `SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg`: the cut norm of the graphon of `G`
  minus its block averages over `P.cellPartition` is `G.cutDiscrepancy P / m²`.

## Implementation

Both kernels are pulled back along the cell index `cellFin m : I → Fin m`: the difference is the
pullback of the kernel on `Fin m`, with the uniform measure, that takes the adjacency value of `G`
minus the block density of `P` at each pair of vertices. The cut norm is invariant under this
measure-preserving pullback (`cutNorm_comap`), so no supremum over measurable subsets of the unit
interval needs to be computed. On `Fin m` every subset is a finset, and its rectangle integrals are
the rectangle deviations `#(G.interedges S T) - G.steppedCount P S T`, scaled by `1 / m²`.
-/

public section

open Finset MeasureTheory ProbabilityTheory TauCeti.unitInterval TauCeti.DenseGraphLimits
open scoped unitInterval

namespace SimpleGraph

variable {m : ℕ} [NeZero m]

/-- **Finite cut discrepancy is graphon cut norm.** For a graph `G` on `Fin m` with `0 < m` and a
partition `P` of its vertices, the rectangle cut norm of the graphon of `G` minus its block
averages over the partition `P.cellPartition` of the unit interval is the cut discrepancy of `P`
divided by `m²`. -/
theorem cutNorm_finiteGraphGraphon_sub_stepGraphonAvg (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m))) :
    cutNorm volume ((finiteGraphGraphon G).toSymmKernel - (stepGraphonAvg (μ := volume)
      P.cellPartition P.measurableSet_of_mem_cellPartition (finiteGraphGraphon G)).toSymmKernel) =
      G.cutDiscrepancy P / (m : ℝ) ^ 2 := by
  -- The block densities of `P`, as a graphon on `Fin m` with the uniform measure.
  let B : Graphon (Fin m) (uniformOn Set.univ) := Graphon.ofMatrix (uniformOn Set.univ)
    (fun i j => ⟨G.edgeDensity (P.part i) (P.part j),
      mod_cast G.edgeDensity_nonneg _ _, mod_cast G.edgeDensity_le_one _ _⟩)
    (fun i j => Subtype.ext (by simp only [G.edgeDensity_comm]))
  let K : SymmKernel (Fin m) (uniformOn Set.univ) :=
    (finiteGraphGraphonOnFin G).toSymmKernel - B.toSymmKernel
  have hW (x y : I) :
      finiteGraphGraphon G x y = finiteGraphGraphonOnFin G (cellFin m x) (cellFin m y) := by
    rw [finiteGraphGraphon_eq_comap, Graphon.comap_apply]
  have hK : (finiteGraphGraphon G).toSymmKernel - (stepGraphonAvg (μ := volume)
      P.cellPartition P.measurableSet_of_mem_cellPartition (finiteGraphGraphon G)).toSymmKernel =
      K.comap (cellFin m) measurable_cellFin volume := by
    ext x y
    simp [K, B, hW, stepGraphonAvg_finiteGraphGraphon_cellPartition_apply, Graphon.ofMatrix_apply]
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
    simp [K, B, Graphon.ofMatrix_apply]
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
    have h := abs_rectIntegral_le_cutNorm _ K S.measurableSet T.measurableSet
    rwa [hrect, abs_div, abs_of_pos hm, div_le_iff₀ hm] at h

end SimpleGraph
