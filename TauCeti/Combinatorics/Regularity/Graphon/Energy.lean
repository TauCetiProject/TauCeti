/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Partition.Energy
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Finpartition
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic

/-!
# Finite partition energy as graphon partition energy

For a graph `G` on `Fin m` with `0 < m`, the graphon `finiteGraphGraphon G` takes the adjacency
value of `G` on the products of the `m` equal cells of the unit interval. A partition `P` of the
vertices lifts to the partition `P.cellPartition` of the unit interval whose parts are the unions
of the cells over each part of `P`. Over the cells of two vertex sets `A` and `B`, the graphon
averages to the edge density `d_G(A, B)`, so the block-average step graphon of `G` over
`P.cellPartition` is `stepGraphonOfFinpartition P` at `G.edgeDensityIcc`, taking the value
`d_G(P.part i, P.part j)` on the cells of `i` and `j`. Its `L²` norm squared is therefore the
size-weighted finite energy, diagonal blocks included.

This module depends on both the finite regularity energy and the graphon energy; neither theory
imports the other.

The lifted partition `Finpartition.cellPartition` is defined with the other unit-interval cell
infrastructure, in `TauCeti.MeasureTheory.Constructions.UnitInterval.CellPartition`.

## Main results

* `SimpleGraph.setAverage_finiteGraphGraphon_preimage` and
  `SimpleGraph.blockAverage_cellPartition_finiteGraphGraphon`: block averages of the graphon of a
  finite graph are edge densities.
* `SimpleGraph.stepGraphonAvg_finiteGraphGraphon_eq_stepGraphonOfFinpartition`: the block-average
  step graphon over `P.cellPartition` is `stepGraphonOfFinpartition P` with block matrix
  `G.edgeDensityIcc`.
* `SimpleGraph.stepGraphonOfFinpartition_bot_edgeDensityIcc`: over the singleton partition `⊥`,
  `stepGraphonOfFinpartition` at `G.edgeDensityIcc` recovers `finiteGraphGraphon G`.
* `SimpleGraph.stepGraphonAvg_finiteGraphGraphon_cellPartition_apply`: the block-average step
  graphon over `P.cellPartition` takes the value `d_G(P.part i, P.part j)` on the cells of `i`
  and `j`.
* `SimpleGraph.graphonPartitionEnergy_finiteGraphGraphon`: the size-weighted energy of `P` is the
  graphon partition energy over `P.cellPartition`.
* `SimpleGraph.graphonPartitionEnergy_finiteGraphGraphon_comap_symm`: the same comparison for
  graphs on any finite vertex type, relabelled along an equivalence with `Fin m`.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.unitInterval TauCeti.DenseGraphLimits Finset
open scoped unitInterval


namespace SimpleGraph

variable {m : ℕ} [NeZero m]

/-- **Block averages of the graphon of a finite graph.** Over the cells of two vertex sets `A`
and `B`, the graphon of `G` averages to the edge density `d_G(A, B)`. When either set is empty,
both sides are `0`. -/
theorem setAverage_finiteGraphGraphon_preimage (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (A B : Finset (Fin m)) :
    ⨍ z in (cellFin m ⁻¹' (A : Set (Fin m))) ×ˢ (cellFin m ⁻¹' (B : Set (Fin m))),
        finiteGraphGraphon G z.1 z.2 ∂(volume.prod volume) = (G.edgeDensity A B : ℝ) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hint : ∫ z in (cellFin m ⁻¹' (A : Set (Fin m))) ×ˢ (cellFin m ⁻¹' (B : Set (Fin m))),
      finiteGraphGraphon G z.1 z.2 ∂(volume.prod volume) =
        (∑ i ∈ A, ∑ j ∈ B, if G.Adj i j then (1 : ℝ) else 0) / (m : ℝ) ^ 2 := by
    have h := SymmKernel.rectIntegral_comap_preimage _ measurePreserving_cellFin
      (finiteGraphGraphonOnFin G).toSymmKernel A.measurableSet B.measurableSet
    rw [SymmKernel.rectIntegral_uniformOn_univ, SymmKernel.rectIntegral_def,
      ← Graphon.toSymmKernel_comap, ← finiteGraphGraphon_eq_comap] at h
    simp only [Graphon.coe_toSymmKernel, finiteGraphGraphonOnFin_apply, Fintype.card_fin] at h
    -- the two sides differ only in the decidability instance of the adjacency test
    convert h
  have hvol : (volume.prod volume).real
      ((cellFin m ⁻¹' (A : Set (Fin m))) ×ˢ (cellFin m ⁻¹' (B : Set (Fin m)))) =
        #A / m * (#B / m) := by
    rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul, ← measureReal_def,
      ← measureReal_def, volume_real_preimage_cellFin, volume_real_preimage_cellFin]
  have hcount : (∑ i ∈ A, ∑ j ∈ B, if G.Adj i j then (1 : ℝ) else 0) = #(G.interedges A B) := by
    rw [SimpleGraph.interedges_def, card_filter, sum_product]
    simp
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hA' : (#A : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hA.card_pos.ne'
  have hB' : (#B : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hB.card_pos.ne'
  rw [setAverage_eq, hint, hvol, hcount, smul_eq_mul, SimpleGraph.edgeDensity_def]
  push_cast
  field_simp

/-- The bundled rectangle average of `finiteGraphGraphon G` over the lifted parts corresponding to
`A` and `B` is the bundled edge density `G.edgeDensityIcc A.1 B.1`. -/
@[simp]
theorem blockAverage_cellPartition_finiteGraphGraphon (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m))) (A B : P.parts) :
    blockAverage P.cellPartition (finiteGraphGraphon G)
        (P.partsCellPartitionEquiv A) (P.partsCellPartitionEquiv B) =
      G.edgeDensityIcc A.val B.val := by
  apply Subtype.ext
  rw [coe_blockAverage, coe_edgeDensityIcc, P.partsCellPartitionEquiv_apply_coe,
    P.partsCellPartitionEquiv_apply_coe]
  exact G.setAverage_finiteGraphGraphon_preimage A.val B.val

/-- **Compatibility of `stepGraphonAvg` and `stepGraphonOfFinpartition` on finite graphs.** Over
`P.cellPartition`, the block-average step graphon of `finiteGraphGraphon G` is
`stepGraphonOfFinpartition P` with block matrix `G.edgeDensityIcc`. -/
theorem stepGraphonAvg_finiteGraphGraphon_eq_stepGraphonOfFinpartition (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m)))
    {hP : ∀ p ∈ P.cellPartition.parts, MeasurableSet p} :
    stepGraphonAvg (μ := volume) P.cellPartition hP (finiteGraphGraphon G) =
      stepGraphonOfFinpartition P (fun A B => G.edgeDensityIcc A.val B.val)
        (fun A B => G.edgeDensityIcc_comm A.val B.val) := by
  rw [stepGraphonAvg_cellPartition_eq_stepGraphonOfFinpartition]
  exact (stepGraphonOfFinpartition_inj P _ _ _ _).2
    (funext fun A => funext fun B => G.blockAverage_cellPartition_finiteGraphGraphon P A B)

/-- Over the singleton partition `⊥` of `Fin m`, `stepGraphonOfFinpartition` at `G.edgeDensityIcc`
recovers `finiteGraphGraphon G`. -/
theorem stepGraphonOfFinpartition_bot_edgeDensityIcc (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] :
    stepGraphonOfFinpartition (⊥ : Finpartition (univ : Finset (Fin m)))
        (fun A B => G.edgeDensityIcc A.val B.val) (fun A B => G.edgeDensityIcc_comm A.val B.val) =
      finiteGraphGraphon G := by
  ext x y
  have hcell (z : I) : (⟨cellIdx m z, cellIdx_lt (NeZero.pos m) z⟩ : Fin m) = cellFin m z :=
    Fin.ext (coe_cellFin z).symm
  simp only [stepGraphonOfFinpartition_apply_part, coe_edgeDensityIcc]
  rw [Finpartition.part_bot (mem_univ _), Finpartition.part_bot (mem_univ _),
    G.edgeDensity_singleton, finiteGraphGraphon_apply_fin G (NeZero.pos m), hcell, hcell]
  split_ifs <;> simp

/-- **The block averages of the graphon of a finite graph.** Over the lifted partition
`P.cellPartition`, the block-average step graphon of `G` takes at `(x, y)` the edge density between
the parts of `P` containing the cells of `x` and `y`. -/
theorem stepGraphonAvg_finiteGraphGraphon_cellPartition_apply (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset (Fin m))) (x y : I) :
    stepGraphonAvg (μ := volume) P.cellPartition P.measurableSet_of_mem_cellPartition
        (finiteGraphGraphon G) x y =
      (G.edgeDensity (P.part (cellFin m x)) (P.part (cellFin m y)) : ℝ) := by
  rw [G.stepGraphonAvg_finiteGraphGraphon_eq_stepGraphonOfFinpartition P]
  simp

/-- **Finite partition energy is graphon partition energy.** For a graph `G` on `Fin m` with
`0 < m` and a partition `P` of its vertices, the size-weighted energy of `P` is the partition
energy of the graphon of `G` over the partition of the unit interval grouping the vertex cells by
the parts of `P`. -/
theorem graphonPartitionEnergy_finiteGraphGraphon (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset (Fin m))) :
    graphonPartitionEnergy volume P.cellPartition P.measurableSet_of_mem_cellPartition
      (finiteGraphGraphon G) = G.weightedEnergy P := by
  rw [graphonPartitionEnergy_eq,
    G.stepGraphonAvg_finiteGraphGraphon_eq_stepGraphonOfFinpartition P,
    l2sq_stepGraphonOfFinpartition, G.weightedEnergy_def, ← sum_coe_sort P.parts]
  exact sum_congr rfl fun A _ => by
    rw [← sum_coe_sort P.parts]
    simp

/-- **Finite partition energy as graphon partition energy, on any finite vertex type.** Relabel
the vertices of `G` along an equivalence `e : V ≃ Fin m` with `0 < m`. The size-weighted energy
of `P` is then the graphon partition energy of the relabelled graph over the cell partition of the
relabelled `P`. For a nonempty finite `V`, take `e := Fintype.equivFin V`. -/
theorem graphonPartitionEnergy_finiteGraphGraphon_comap_symm {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : V ≃ Fin m)
    (P : Finpartition (univ : Finset V)) :
    graphonPartitionEnergy volume
        ((P.copy (image_univ_equiv e.symm).symm).comap e.symm).cellPartition
        (Finpartition.measurableSet_of_mem_cellPartition _)
        (finiteGraphGraphon (G.comap e.symm)) =
      G.weightedEnergy P := by
  rw [graphonPartitionEnergy_finiteGraphGraphon, weightedEnergy_comap_symm]

end SimpleGraph
