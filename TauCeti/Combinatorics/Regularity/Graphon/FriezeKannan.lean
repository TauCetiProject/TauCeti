/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graphon.CutDiscrepancy
public import TauCeti.Combinatorics.Regularity.Graph.FriezeKannan
public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Distance

/-!
# Finite Frieze–Kannan weak regularity as graphon weak regularity

For a graph `G` on `Fin m` with `0 < m`, lifting a vertex partition `P` to the unit-interval cell
partition `P.cellPartition` preserves the part count (`#P.cellPartition.parts = #P.parts`),
preserves and reflects refinement, identifies the size-weighted energy `G.weightedEnergy P` with
`graphonPartitionEnergy`, and divides the count-scaled cut discrepancy `G.cutDiscrepancy P` by `m²`
to give the normalized graphon cut-norm error against `stepGraphonAvg`.

Consequently, a vertex partition `P` satisfies the finite Frieze–Kannan weak-regularity bound
`#P.parts ≤ k` and `G.cutDiscrepancy P ≤ ε * m²` if and only if `P.cellPartition` satisfies the
analytic weak-regularity bound `#P.cellPartition.parts ≤ k` and
`cutNorm volume ((finiteGraphGraphon G).toSymmKernel - (stepGraphonAvg ...).toSymmKernel) ≤ ε`
(`Finpartition.card_parts_cellPartition`,
`SimpleGraph.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_le_iff`).

Transporting the finite theorems `SimpleGraph.exists_refinement_weightedEnergy_add_sq_lt`,
`SimpleGraph.frieze_kannan_refining`, and `SimpleGraph.frieze_kannan_cutDiscrepancy` along
`Finpartition.cellPartition` yields the analytic weak-regularity statements for
`finiteGraphGraphon G` (`SimpleGraph.frieze_kannan_cellPartition`,
`SimpleGraph.frieze_kannan_stepGraphonOfFinpartition`), with the additional guarantee that the
approximating measurable partition of the unit interval is induced by a partition of the vertices
rather than splitting individual vertex cells.

## Main results

* `SimpleGraph.exists_cellPartition_refinement_energy_add_sq_lt`: a cut-norm defect above `ε` over
  `P.cellPartition` yields a refining vertex partition `Q ≤ P` whose lifted cell partition has at
  most `4 * #P.cellPartition.parts` parts and raises `graphonPartitionEnergy` by more than `ε²`.
* `SimpleGraph.frieze_kannan_cellPartition_refining`: for `ε > 0`, every vertex partition `P₀` of
  `Fin m` (`0 < m`) has a refinement `P ≤ P₀` whose lifted partition `P.cellPartition` refines
  `P₀.cellPartition`, has `#P.cellPartition.parts ≤ 4 ^ ⌈1 / ε²⌉ * #P₀.cellPartition.parts`, and
  approximates `finiteGraphGraphon G` within `ε` in cut norm.
* `SimpleGraph.frieze_kannan_cellPartition`: analytic Frieze–Kannan weak regularity for
  `finiteGraphGraphon G` (`ε > 0`, `0 < m`), witnessed by `P.cellPartition` with
  `#P.cellPartition.parts ≤ 4 ^ ⌈1 / ε²⌉`.
* `SimpleGraph.frieze_kannan_stepGraphonOfFinpartition`: approximation of `finiteGraphGraphon G`
  within `ε` in both `cutNorm` and `cutDist` by `stepGraphonOfFinpartition P` at
  `G.edgeDensityIcc`.
* `SimpleGraph.frieze_kannan_cellPartition_comap_symm`: the same comparison on any finite vertex
  type, relabelled along an equivalence with `Fin m`.

## References

* A. Frieze, R. Kannan, *Quick approximation to matrices and applications*, Combinatorica 19
  (1999), 175–220.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
-/

public section

open Finset MeasureTheory TauCeti.DenseGraphLimits
open scoped unitInterval

namespace SimpleGraph

variable {m : ℕ} [NeZero m]

/-- **Cell-preserving analytic energy increment.** If the block average of `finiteGraphGraphon G`
over `P.cellPartition` fails to approximate `finiteGraphGraphon G` within `ε` in cut norm (`0 ≤ ε`),
there is a vertex refinement `Q ≤ P` whose lifted partition `Q.cellPartition` has at most four times
as many parts and increases `graphonPartitionEnergy` by strictly more than `ε²`. -/
theorem exists_cellPartition_refinement_energy_add_sq_lt (G : SimpleGraph (Fin m))
    (P : Finpartition (univ : Finset (Fin m))) {ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ε < cutNorm volume ((finiteGraphGraphon G).toSymmKernel -
      (stepGraphonAvg (μ := volume) P.cellPartition P.measurableSet_of_mem_cellPartition
        (finiteGraphGraphon G)).toSymmKernel)) :
    ∃ Q : Finpartition (univ : Finset (Fin m)),
      Q.cellPartition ≤ P.cellPartition ∧
        #Q.cellPartition.parts ≤ 4 * #P.cellPartition.parts ∧
        graphonPartitionEnergy volume P.cellPartition P.measurableSet_of_mem_cellPartition
            (finiteGraphGraphon G) + ε ^ 2 <
          graphonPartitionEnergy volume Q.cellPartition Q.measurableSet_of_mem_cellPartition
            (finiteGraphGraphon G) := by
  classical
  have hm : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (NeZero.pos m)) 2
  rw [G.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg P, lt_div_iff₀ hm] at hbad
  have hbad' : ε * (Fintype.card (Fin m) : ℝ) ^ 2 < G.cutDiscrepancy P := by simpa using hbad
  obtain ⟨Q, hQP, hcard, henergy⟩ := G.exists_refinement_weightedEnergy_add_sq_lt P hε hbad'
  refine ⟨Q, Finpartition.cellPartition_mono hQP, ?_, ?_⟩
  · simpa only [Finpartition.card_parts_cellPartition] using hcard
  · simpa only [G.graphonPartitionEnergy_finiteGraphGraphon] using henergy

/-- **Frieze–Kannan weak regularity for `finiteGraphGraphon`, refining cell-partition form.** For
`ε > 0`, every vertex partition `P₀` of `Fin m` (`0 < m`) has a refinement `P ≤ P₀` whose lifted
partition `P.cellPartition` refines `P₀.cellPartition`, has at most
`4 ^ ⌈1 / ε²⌉ * #P₀.cellPartition.parts` parts, and approximates `finiteGraphGraphon G` within `ε`
in cut norm. -/
theorem frieze_kannan_cellPartition_refining (G : SimpleGraph (Fin m))
    (P₀ : Finpartition (univ : Finset (Fin m))) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset (Fin m)),
      P.cellPartition ≤ P₀.cellPartition ∧
        #P.cellPartition.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ * #P₀.cellPartition.parts ∧
        cutNorm volume ((finiteGraphGraphon G).toSymmKernel -
          (stepGraphonAvg (μ := volume) P.cellPartition P.measurableSet_of_mem_cellPartition
            (finiteGraphGraphon G)).toSymmKernel) ≤ ε := by
  classical
  obtain ⟨P, hP, hcard, hcut⟩ := G.frieze_kannan_refining P₀ hε
  rw [Fintype.card_fin] at hcut
  refine ⟨P, Finpartition.cellPartition_mono hP, ?_,
    (G.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_le_iff P).2 hcut⟩
  simpa only [Finpartition.card_parts_cellPartition] using hcard

/-- **Analytic Frieze–Kannan weak regularity specialized to `finiteGraphGraphon`.** For `ε > 0` and
`0 < m`, `finiteGraphGraphon G` admits a weak-regular measurable partition of `(I, volume)` of the
form `P.cellPartition`, with `#P.cellPartition.parts ≤ 4 ^ ⌈1 / ε²⌉` and cut-norm defect at most
`ε`. -/
theorem frieze_kannan_cellPartition (G : SimpleGraph (Fin m)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset (Fin m)),
      #P.cellPartition.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧
        cutNorm volume ((finiteGraphGraphon G).toSymmKernel -
          (stepGraphonAvg (μ := volume) P.cellPartition P.measurableSet_of_mem_cellPartition
            (finiteGraphGraphon G)).toSymmKernel) ≤ ε := by
  classical
  obtain ⟨P, hcard, hcut⟩ := G.frieze_kannan_cutDiscrepancy hε
  rw [Fintype.card_fin] at hcut
  exact ⟨P, P.card_parts_cellPartition.trans_le hcard,
    (G.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_le_iff P).2 hcut⟩

/-- **Step-graphon approximation of `finiteGraphGraphon` via `stepGraphonOfFinpartition`.** For
`ε > 0` and `0 < m`, there is a vertex partition `P` of `Fin m` into at most `4 ^ ⌈1 / ε²⌉` parts
such that `stepGraphonOfFinpartition P` at `G.edgeDensityIcc` approximates `finiteGraphGraphon G`
within `ε` in both rectangle cut norm and graphon cut distance. -/
theorem frieze_kannan_stepGraphonOfFinpartition (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset (Fin m)),
      #P.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧
        cutNorm volume ((finiteGraphGraphon G).toSymmKernel -
          (stepGraphonOfFinpartition P (fun A B => G.edgeDensityIcc A.val B.val)
            (fun A B => G.edgeDensityIcc_comm A.val B.val)).toSymmKernel) ≤ ε ∧
        cutDist (finiteGraphGraphon G)
          (stepGraphonOfFinpartition P (fun A B => G.edgeDensityIcc A.val B.val)
            (fun A B => G.edgeDensityIcc_comm A.val B.val)) ≤ ε := by
  obtain ⟨P, hcard, hcut⟩ := G.frieze_kannan_cellPartition hε
  rw [P.card_parts_cellPartition] at hcard
  rw [G.stepGraphonAvg_finiteGraphGraphon_eq_stepGraphonOfFinpartition P] at hcut
  exact ⟨P, hcard, hcut, (cutDist_le_cutNorm_sub (finiteGraphGraphon G) _).trans hcut⟩

/-- **Analytic Frieze–Kannan comparison on any finite vertex type.** For `ε > 0`, along
`e : V ≃ Fin m` with `0 < m`, `G` has a vertex partition `P` into at most `4 ^ ⌈1 / ε²⌉` parts
whose relabelled cell partition approximates `finiteGraphGraphon (G.comap e.symm)` within `ε` in cut
norm. -/
theorem frieze_kannan_cellPartition_comap_symm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : V ≃ Fin m) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset V),
      #P.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧
        cutNorm volume ((finiteGraphGraphon (G.comap e.symm)).toSymmKernel -
          (stepGraphonAvg (μ := volume)
            ((P.copy (image_univ_equiv e.symm).symm).comap e.symm).cellPartition
            (Finpartition.measurableSet_of_mem_cellPartition _)
            (finiteGraphGraphon (G.comap e.symm))).toSymmKernel) ≤ ε := by
  classical
  obtain ⟨P, hcard, hcut⟩ := G.frieze_kannan_cutDiscrepancy hε
  exact ⟨P, hcard, (G.cutNorm_finiteGraphGraphon_sub_stepGraphonAvg_comap_symm_le_iff e P).2 hcut⟩

end SimpleGraph
