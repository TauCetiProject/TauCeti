/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Regularity.Graphon.FriezeKannan
import Mathlib.Tactic.NormNum

/-!
# Regression examples: finite and analytic Frieze–Kannan weak regularity

These downstream examples exercise the public comparison between finite `cutDiscrepancy` weak
regularity and analytic `cutNorm` / `cutDist` weak regularity for `finiteGraphGraphon`:

* At `ε = 3 / 4`, `1 / ε² = 16 / 9` is non-integral with ceiling `2`, so every graph on `Fin m`
  (`0 < m`) admits a `stepGraphonOfFinpartition` approximation with at most `4 ^ 2 = 16` parts and
  cut distance at most `3 / 4`.
* Refining an initial vertex partition `P₀` preserves cell boundaries on the unit interval through
  `SimpleGraph.frieze_kannan_cellPartition_refining`.
* On a nonempty finite vertex type `V`, `Fintype.equivFin V` transports the weak-regularity bound
  through `SimpleGraph.frieze_kannan_cellPartition_comap_symm`, without `[DecidableRel G.Adj]`.
* On the empty host `Fin 0`, `SimpleGraph.frieze_kannan_cutDiscrepancy` still applies directly for
  every `ε > 0`.
-/

open Finset MeasureTheory

namespace TauCeti.DenseGraphLimits

-- Non-integral `1 / ε² = 16 / 9` (`⌈16 / 9⌉₊ = 2`, `4 ^ 2 = 16`): step-graphon approximation in
-- `cutDist`.
example {m : ℕ} [NeZero m] (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] :
    ∃ P : Finpartition (univ : Finset (Fin m)),
      #P.parts ≤ 16 ∧
        cutDist (finiteGraphGraphon G)
          (stepGraphonOfFinpartition P (fun A B => G.edgeDensityIcc A.val B.val)
            (fun A B => G.edgeDensityIcc_comm A.val B.val)) ≤ 3 / 4 := by
  obtain ⟨P, hcard, -, hdist⟩ :=
    G.frieze_kannan_stepGraphonOfFinpartition (ε := 3 / 4) (by norm_num)
  have hceil : ⌈(1 : ℝ) / (3 / 4) ^ 2⌉₊ = 2 := by
    refine Nat.ceil_eq_iff (by decide) |>.2 ⟨by norm_num, by norm_num⟩
  rw [hceil] at hcard
  exact ⟨P, by omega, hdist⟩

-- Refining an initial vertex partition `P₀` without requiring `[DecidableRel G.Adj]`.
example {m : ℕ} [NeZero m] (G : SimpleGraph (Fin m)) (P₀ : Finpartition (univ : Finset (Fin m))) :
    ∃ P : Finpartition (univ : Finset (Fin m)),
      P.cellPartition ≤ P₀.cellPartition ∧
        #P.cellPartition.parts ≤ 16 * #P₀.cellPartition.parts ∧
        cutNorm volume ((finiteGraphGraphon G).toSymmKernel -
          (stepGraphonAvg (μ := volume) P.cellPartition P.measurableSet_of_mem_cellPartition
            (finiteGraphGraphon G)).toSymmKernel) ≤ 3 / 4 := by
  obtain ⟨P, hle, hcard, hcut⟩ :=
    G.frieze_kannan_cellPartition_refining P₀ (ε := 3 / 4) (by norm_num)
  have hceil : ⌈(1 : ℝ) / (3 / 4) ^ 2⌉₊ = 2 := by
    refine Nat.ceil_eq_iff (by decide) |>.2 ⟨by norm_num, by norm_num⟩
  rw [hceil] at hcard
  exact ⟨P, hle, by omega, hcut⟩

-- On any nonempty finite vertex type `V`, `Fintype.equivFin V` transports the comparison.
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) {ε : ℝ}
    (hε : 0 < ε) :
    haveI : NeZero (Fintype.card V) := ⟨Fintype.card_ne_zero⟩
    ∃ P : Finpartition (univ : Finset V),
      #P.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧
        cutNorm volume ((finiteGraphGraphon (G.comap (Fintype.equivFin V).symm)).toSymmKernel -
          (stepGraphonAvg (μ := volume)
            ((P.copy (image_univ_equiv (Fintype.equivFin V).symm).symm).comap
              (Fintype.equivFin V).symm).cellPartition
            (Finpartition.measurableSet_of_mem_cellPartition _)
            (finiteGraphGraphon (G.comap (Fintype.equivFin V).symm))).toSymmKernel) ≤ ε :=
  G.frieze_kannan_cellPartition_comap_symm (Fintype.equivFin V) hε

-- Empty host `Fin 0`: the finite `cutDiscrepancy` Frieze–Kannan bound applies without `[NeZero m]`.
example (G : SimpleGraph (Fin 0)) [DecidableRel G.Adj] {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset (Fin 0)),
      #P.parts ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧
        G.cutDiscrepancy P ≤ ε * (Fintype.card (Fin 0) : ℝ) ^ 2 :=
  G.frieze_kannan_cutDiscrepancy hε

end TauCeti.DenseGraphLimits
