/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graph.InducedCount
public import TauCeti.Combinatorics.Regularity.Partition.Energy
import TauCeti.Algebra.Order.BigOperators.ProdSubProd
import TauCeti.Data.Fintype.BigOperators

/-!
# The stepped prediction of labelled induced three-vertex counts

For a graph `J` on `Fin 3`, a finite graph `G` and a partition `R` of its vertices,
`J.steppedInducedGraphCount3 G R` is the number of labelled induced copies of `J` predicted by the
`R`-stepped graph, the weighted graph whose weight on a pair of vertices is the edge density of
`G` between their parts. Each assignment `φ` of the three vertices of `J` to parts of `R`, repeated
parts included, contributes the volume `∏ i, #(φ i)` times, for each pair `i < j`, the edge density
`d(φ i, φ j)` if `J.Adj i j` and the nonedge density `1 - d(φ i, φ j)` otherwise. Equivalently, it
sums over all maps `g : Fin 3 → V` the product of these densities between the parts containing the
images (`SimpleGraph.steppedInducedGraphCount3_eq_sum_part`).

Unlike the coarse prediction `SimpleGraph.coarseInducedGraphEstimate3`, which only sums over
assignments to three distinct parts, the stepped prediction behaves well under refinement: for a
refinement `Q ≤ P` whose size-weighted energy exceeds that of `P` by at most `ε`, the stepped
predictions of `Q` and `P` differ by at most `3 √ε (card V) ^ 3`. Each of the three density factors
changes by the deviation of a fine density from its coarse parent density, and the weighted mean of
these deviations is at most `√ε` (`SimpleGraph.weightedDensityDeviation_abs_le`). For a single
partition `R`, the stepped prediction and the coarse prediction differ only by the assignments with
a repeated part, which contribute at most `3 * m * (card V) ^ 2` when every part of `R` has at most
`m` vertices.

These are the energy-transfer and repeated-cell steps of the induced counting lemma for strong
graph regularity, which compares the actual count with the coarse prediction of the coarse
partition through the stepped predictions of the fine and coarse partitions.

## Main definitions

* `SimpleGraph.steppedInducedGraphCount3 J G R`: the stepped prediction of the induced count.

## Main results

* `SimpleGraph.steppedInducedGraphCount3_eq_sum_part`: the stepped prediction as a sum over all
  maps `Fin 3 → V`.
* `SimpleGraph.abs_steppedInducedGraphCount3_sub_le`: the energy-transfer bound
  `|T_Q - T_P| ≤ 3 √ε (card V) ^ 3` for a refinement with energy gap at most `ε`.
* `SimpleGraph.coarseInducedGraphEstimate3_le_steppedInducedGraphCount3` and
  `SimpleGraph.steppedInducedGraphCount3_le_coarseInducedGraphEstimate3_add`: the stepped
  prediction exceeds the coarse prediction by at most `3 * m * (card V) ^ 2`.

## References

* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 2 (the graph regularity method: the graph counting lemma and strong regularity).
-/

public section

open Finset
open Function (Injective)

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The stepped prediction of `J.inducedGraphCount3 G` from a partition `R` of the vertices: the
number of labelled induced copies of `J` in the `R`-stepped graph. Each assignment `φ` of the
vertices of `J` to parts of `R`, repeated parts included, contributes the volume `∏ i, #(φ i)`
times, for each pair `i < j`, the edge density `d(φ i, φ j)` if `J.Adj i j` and the nonedge
density `1 - d(φ i, φ j)` otherwise. -/
noncomputable def steppedInducedGraphCount3 (R : Finpartition (univ : Finset V)) : ℝ :=
  ∑ φ : Fin 3 → R.parts, (∏ i, (#(φ i : Finset V) : ℝ)) *
    ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2}, G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2)

theorem steppedInducedGraphCount3_def (R : Finpartition (univ : Finset V)) :
    J.steppedInducedGraphCount3 G R =
      ∑ φ : Fin 3 → R.parts, (∏ i, (#(φ i : Finset V) : ℝ)) *
        ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2) := (rfl)

/-- The stepped prediction sums, over all maps `g : Fin 3 → V`, the product of the edge or
nonedge densities between the parts of `R` containing the images. -/
theorem steppedInducedGraphCount3_eq_sum_part (R : Finpartition (univ : Finset V)) :
    J.steppedInducedGraphCount3 G R = ∑ g : Fin 3 → V,
      ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        G.patternDensity (J.Adj p.1.1 p.1.2) (R.part (g p.1.1)) (R.part (g p.1.2)) := by
  have := R.sum_piFinset_apply_part (ι := Fin 3) fun A ↦
    ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      (G.patternDensity (J.Adj p.1.1 p.1.2) (A p.1.1) (A p.1.2) : ℝ)
  rw [steppedInducedGraphCount3_def]
  simpa only [Fintype.piFinset_univ, nsmul_eq_mul, Nat.cast_prod] using this.symm

/-- The stepped prediction is nonnegative. -/
theorem steppedInducedGraphCount3_nonneg (R : Finpartition (univ : Finset V)) :
    0 ≤ J.steppedInducedGraphCount3 G R := by
  rw [steppedInducedGraphCount3_eq_sum_part]
  exact sum_nonneg fun g _ ↦ prod_nonneg fun p _ ↦ G.patternDensity_nonneg _ _ _

/-- The stepped prediction splits into the coarse prediction, over the assignments to distinct
parts, and the contribution of the assignments with a repeated part. -/
private lemma steppedInducedGraphCount3_eq_add (R : Finpartition (univ : Finset V)) :
    J.steppedInducedGraphCount3 G R = J.coarseInducedGraphEstimate3 G R +
      ∑ φ : Fin 3 → R.parts with ¬Injective φ, (∏ i, (#(φ i : Finset V) : ℝ)) *
        ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2) := by
  rw [steppedInducedGraphCount3_def, coarseInducedGraphEstimate3_def,
    sum_filter_add_sum_filter_not]

/-- The coarse prediction, which omits the assignments with a repeated part, is at most the
stepped prediction. -/
theorem coarseInducedGraphEstimate3_le_steppedInducedGraphCount3
    (R : Finpartition (univ : Finset V)) :
    J.coarseInducedGraphEstimate3 G R ≤ J.steppedInducedGraphCount3 G R := by
  rw [steppedInducedGraphCount3_eq_add]
  exact le_add_of_nonneg_right (sum_nonneg fun φ _ ↦ mul_nonneg (by positivity)
    (prod_nonneg fun p _ ↦ G.patternDensity_nonneg _ _ _))

/-- If every part of `R` has at most `m` vertices, the assignments with a repeated part add at
most `3 * m * (card V) ^ 2` to the coarse prediction. -/
theorem steppedInducedGraphCount3_le_coarseInducedGraphEstimate3_add
    (R : Finpartition (univ : Finset V)) {m : ℕ} (hm : ∀ A ∈ R.parts, #A ≤ m) :
    J.steppedInducedGraphCount3 G R ≤
      J.coarseInducedGraphEstimate3 G R + 3 * m * (Fintype.card V : ℝ) ^ 2 := by
  rw [steppedInducedGraphCount3_eq_add]
  gcongr
  calc _ ≤ ∑ φ : Fin 3 → R.parts with ¬Injective φ, ∏ i, (#(φ i : Finset V) : ℝ) := by
        refine sum_le_sum fun φ _ ↦ mul_le_of_le_one_right (by positivity) ?_
        exact prod_le_one₀ (fun p _ ↦ G.patternDensity_nonneg _ _ _)
          fun p _ ↦ G.patternDensity_le_one _ _ _
    _ ≤ 3 * m * (Fintype.card V : ℝ) ^ 2 := by
        have := R.sum_prod_card_of_not_injective_le_of_card_le (ι := Fin 3) hm
        simp only [Fintype.card_fin, card_univ] at this
        exact_mod_cast this

/-- **Energy transfer.** For a refinement `Q ≤ P` whose size-weighted energy exceeds that of `P` by
at most `ε`, the stepped predictions of `Q` and `P` differ by at most `3 √ε (card V) ^ 3`. No
equitability or regularity is assumed. -/
theorem abs_steppedInducedGraphCount3_sub_le {P Q : Finpartition (univ : Finset V)} (h : Q ≤ P)
    {ε : ℝ} (hgap : G.weightedEnergy Q - G.weightedEnergy P ≤ ε) :
    |J.steppedInducedGraphCount3 G Q - J.steppedInducedGraphCount3 G P| ≤
      3 * √ε * (Fintype.card V : ℝ) ^ 3 := by
  set D : V → V → ℝ := fun x y ↦
    |(G.edgeDensity (Q.part x) (Q.part y) : ℝ) - G.edgeDensity (P.part x) (P.part y)|
  have habs (e : Prop) [Decidable e] (s t : Finset V) : |(G.patternDensity e s t : ℝ)| ≤ 1 :=
    abs_le.2 ⟨by linarith [G.patternDensity_nonneg (𝕜 := ℝ) e s t], G.patternDensity_le_one e s t⟩
  rw [steppedInducedGraphCount3_eq_sum_part, steppedInducedGraphCount3_eq_sum_part,
    ← sum_sub_distrib]
  -- Telescope the three factors at each map, then sum each pair over the third vertex.
  calc _ ≤ ∑ g : Fin 3 → V, ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2}, D (g p.1.1) (g p.1.2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun g _ ↦ ?_)
        exact (TauCeti.abs_prod_sub_prod_le_sum_abs_sub _ (fun p _ ↦ habs _ _ _)
          (fun p _ ↦ habs _ _ _)).trans_eq
            (sum_congr rfl fun p _ ↦ G.abs_patternDensity_sub _ _ _ _ _)
    _ = ∑ _p : {p : Fin 3 × Fin 3 // p.1 < p.2}, Fintype.card V • ∑ x, ∑ y, D x y := by
        rw [sum_comm]
        exact sum_congr rfl fun p _ ↦ by
          simpa [card_sdiff, ne_of_lt p.2, Nat.sub_sub] using
            Fintype.sum_piFinset_apply_apply (ne_of_lt p.2) (fun _ ↦ univ) D
    _ = 3 * Fintype.card V * ∑ x, ∑ y, D x y := by
        have hpairs : Fintype.card {p : Fin 3 × Fin 3 // p.1 < p.2} = 3 := by decide
        rw [sum_const, card_univ, hpairs, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc]
        norm_num
    _ ≤ 3 * Fintype.card V * (√ε * Fintype.card V ^ 2) := by
        grw [G.sum_sum_abs_edgeDensity_part_sub_le h hgap]
    _ = 3 * √ε * (Fintype.card V : ℝ) ^ 3 := by ring

end SimpleGraph
