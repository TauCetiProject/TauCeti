/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Partition.Energy
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Energy
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic

/-!
# Finite partition energy as graphon partition energy

For a graph `G` on `Fin m` with `0 < m`, the graphon `finiteGraphGraphon G` takes the adjacency
value of `G` on the products of the `m` equal cells of the unit interval. A partition `P` of the
vertices lifts to the partition `cellPartition P` of the unit interval whose parts are the unions
of the cells over each part of `P`. Over the cells of two vertex sets `A` and `B`, the graphon
averages to the edge density `d_G(A, B)`, so the block-average step graphon of `G` over
`cellPartition P` takes the value `d_G(P.part i, P.part j)` on the cells of `i` and `j`. Its
`L²` norm squared is therefore the size-weighted finite energy, diagonal blocks included.

This module depends on both the finite regularity energy and the graphon energy; neither theory
imports the other.

## Main definitions

* `TauCeti.DenseGraphLimits.cellPartition`: the partition of the unit interval induced by a
  partition of `Fin m`.

## Main results

* `TauCeti.DenseGraphLimits.setAverage_finiteGraphGraphon_preimage`: block averages of the graphon
  of a finite graph are edge densities.
* `TauCeti.DenseGraphLimits.graphonPartitionEnergy_finiteGraphGraphon`: the size-weighted energy
  of `P` is the graphon partition energy over `cellPartition P`.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.unitInterval Finset
open scoped unitInterval

namespace TauCeti.DenseGraphLimits

variable {m : ℕ} [NeZero m]

/-- The partition of the unit interval obtained from a partition `P` of `Fin m` by grouping the
`m` equal cells of `I` according to the parts of `P`. -/
noncomputable def cellPartition (P : Finpartition (univ : Finset (Fin m))) :
    Finpartition (Set.univ : Set I) :=
  Finpartition.ofFibers fun x => P.part (cellFin m x)

/-- The part of `P` containing the cell of a point depends measurably on the point. -/
theorem measurable_part_cellFin (P : Finpartition (univ : Finset (Fin m))) :
    Measurable fun x : I => P.part (cellFin m x) :=
  (measurable_from_top (f := fun i : Fin m => P.part i)).comp measurable_cellFin

/-- The parts of `cellPartition P` are measurable. -/
theorem measurableSet_of_mem_cellPartition (P : Finpartition (univ : Finset (Fin m))) :
    ∀ p ∈ (cellPartition P).parts, MeasurableSet p :=
  fun _ hp => Finpartition.measurableSet_of_mem_ofFibers (measurable_part_cellFin P) hp

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
  -- the cells of a vertex set have total volume the proportion of vertices it contains
  have hcell (C : Finset (Fin m)) : volume.real (cellFin m ⁻¹' (C : Set (Fin m))) = #C / m := by
    rw [measureReal_def, measurePreserving_cellFin.measure_preimage
      C.measurableSet.nullMeasurableSet, ProbabilityTheory.uniformOn_univ]
    simp [ENNReal.toReal_div]
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
      ← measureReal_def, hcell, hcell]
  have hcount : (∑ i ∈ A, ∑ j ∈ B, if G.Adj i j then (1 : ℝ) else 0) = #(G.interedges A B) := by
    rw [SimpleGraph.interedges_def, card_filter, sum_product]
    push_cast
    -- both sides now index the same indicator by the pair `(i, j)` and by its components
    rfl
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hA' : (#A : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hA.card_pos.ne'
  have hB' : (#B : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hB.card_pos.ne'
  rw [setAverage_eq, hint, hvol, hcount, smul_eq_mul, SimpleGraph.edgeDensity_def]
  push_cast
  field_simp

/-- The cells of the part of `P` containing the cell of `x` form the part of `cellPartition P`
containing `x`. -/
theorem preimage_part_cellFin_mem (P : Finpartition (univ : Finset (Fin m))) (x : I) :
    cellFin m ⁻¹' (P.part (cellFin m x) : Set (Fin m)) ∈ (cellPartition P).parts := by
  refine Finpartition.mem_ofFibers_parts.2 ⟨x, Set.ext fun z => ?_⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
  exact (P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).symm

/-- **Finite partition energy is graphon partition energy.** For a graph `G` on `Fin m` with
`0 < m` and a partition `P` of its vertices, the size-weighted energy of `P` is the partition
energy of the graphon of `G` over the partition of the unit interval grouping the vertex cells by
the parts of `P`. -/
theorem graphonPartitionEnergy_finiteGraphGraphon (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset (Fin m))) :
    graphonPartitionEnergy volume (cellPartition P) (measurableSet_of_mem_cellPartition P)
      (finiteGraphGraphon G) = G.weightedEnergy P := by
  -- The block average at `(x, y)` is the edge density between the parts of their cells.
  have hpt (x y : I) : stepGraphonAvg (μ := volume) (cellPartition P)
      (measurableSet_of_mem_cellPartition P) (finiteGraphGraphon G) x y =
        (G.edgeDensity (P.part (cellFin m x)) (P.part (cellFin m y)) : ℝ) := by
    rw [stepGraphonAvg_apply (cellPartition P) (measurableSet_of_mem_cellPartition P) _
      (p := ⟨_, preimage_part_cellFin_mem P x⟩) (q := ⟨_, preimage_part_cellFin_mem P y⟩)
      (P.mem_part (mem_univ _)) (P.mem_part (mem_univ _))]
    exact setAverage_finiteGraphGraphon_preimage G _ _
  -- Its mean square over `I × I` is the mean square over pairs of vertices.
  let h : Fin m × Fin m → ℝ := fun ij => (G.edgeDensity (P.part ij.1) (P.part ij.2) : ℝ) ^ 2
  have hmp := (measurePreserving_cellFin (m := m)).prod (measurePreserving_cellFin (m := m))
  rw [graphonPartitionEnergy_eq, l2sq_def]
  simp only [Graphon.coe_toSymmKernel, hpt]
  -- the integrand is `h` read through the two cell indices
  change ∫ z, h (Prod.map (cellFin m) (cellFin m) z) ∂(volume.prod volume) = _
  rw [← integral_map hmp.measurable.aemeasurable (measurable_of_countable h).aestronglyMeasurable,
    hmp.map_eq, integral_fintype (Integrable.of_finite), SimpleGraph.weightedEnergy_eq_sum_part,
    Fintype.sum_prod_type, sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [← Set.singleton_prod_singleton, measureReal_prod_prod, measureReal_def, measureReal_def,
    ProbabilityTheory.uniformOn_univ, ProbabilityTheory.uniformOn_univ]
  simp [h]
  ring

end TauCeti.DenseGraphLimits
