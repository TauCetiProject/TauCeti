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
these deviations is at most `√ε` (`SimpleGraph.weightedDensityDeviation_abs_le`). The two
predictions themselves differ only by the assignments with a repeated part, which contribute at
most `3 * m * (card V) ^ 2` when every part has at most `m` vertices.

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
open Finpartition (refinementParent)

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
    ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      if J.Adj p.1.1 p.1.2 then (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ)
      else 1 - (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ)

theorem steppedInducedGraphCount3_def (R : Finpartition (univ : Finset V)) :
    J.steppedInducedGraphCount3 G R =
      ∑ φ : Fin 3 → R.parts, (∏ i, (#(φ i : Finset V) : ℝ)) *
        ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          if J.Adj p.1.1 p.1.2 then (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ)
          else 1 - (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ) := (rfl)

omit [Fintype V] [DecidableEq V] in
/-- An edge or nonedge density factor is nonnegative. -/
private lemma ite_edgeDensity_nonneg (e : Prop) [Decidable e] (s t : Finset V) :
    0 ≤ if e then (G.edgeDensity s t : ℝ) else 1 - (G.edgeDensity s t : ℝ) := by
  have h₀ : (0 : ℝ) ≤ G.edgeDensity s t := mod_cast G.edgeDensity_nonneg s t
  have h₁ : (G.edgeDensity s t : ℝ) ≤ 1 := mod_cast G.edgeDensity_le_one s t
  split_ifs <;> linarith

omit [Fintype V] [DecidableEq V] in
/-- An edge or nonedge density factor is at most one. -/
private lemma ite_edgeDensity_le_one (e : Prop) [Decidable e] (s t : Finset V) :
    (if e then (G.edgeDensity s t : ℝ) else 1 - (G.edgeDensity s t : ℝ)) ≤ 1 := by
  have h₀ : (0 : ℝ) ≤ G.edgeDensity s t := mod_cast G.edgeDensity_nonneg s t
  have h₁ : (G.edgeDensity s t : ℝ) ≤ 1 := mod_cast G.edgeDensity_le_one s t
  split_ifs <;> linarith

/-- The stepped prediction sums, over all maps `g : Fin 3 → V`, the product of the edge or
nonedge densities between the parts of `R` containing the images. -/
theorem steppedInducedGraphCount3_eq_sum_part (R : Finpartition (univ : Finset V)) :
    J.steppedInducedGraphCount3 G R = ∑ g : Fin 3 → V,
      ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        if J.Adj p.1.1 p.1.2 then (G.edgeDensity (R.part (g p.1.1)) (R.part (g p.1.2)) : ℝ)
        else 1 - (G.edgeDensity (R.part (g p.1.1)) (R.part (g p.1.2)) : ℝ) := by
  have := R.sum_piFinset_apply_part (ι := Fin 3) fun A ↦
    ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      if J.Adj p.1.1 p.1.2 then (G.edgeDensity (A p.1.1) (A p.1.2) : ℝ)
      else 1 - (G.edgeDensity (A p.1.1) (A p.1.2) : ℝ)
  rw [steppedInducedGraphCount3_def]
  simpa only [Fintype.piFinset_univ, nsmul_eq_mul, Nat.cast_prod] using this.symm

/-- The stepped prediction is nonnegative. -/
theorem steppedInducedGraphCount3_nonneg (R : Finpartition (univ : Finset V)) :
    0 ≤ J.steppedInducedGraphCount3 G R := by
  rw [steppedInducedGraphCount3_eq_sum_part]
  exact sum_nonneg fun g _ ↦ prod_nonneg fun p _ ↦ ite_edgeDensity_nonneg G _ _ _

/-- The stepped prediction splits into the coarse prediction, over the assignments to distinct
parts, and the contribution of the assignments with a repeated part. -/
private lemma steppedInducedGraphCount3_eq_add (R : Finpartition (univ : Finset V)) :
    J.steppedInducedGraphCount3 G R = J.coarseInducedGraphEstimate3 G R +
      ∑ φ : Fin 3 → R.parts with ¬Injective φ, (∏ i, (#(φ i : Finset V) : ℝ)) *
        ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          if J.Adj p.1.1 p.1.2 then (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ)
          else 1 - (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ) := by
  rw [steppedInducedGraphCount3_def, coarseInducedGraphEstimate3_def,
    sum_filter_add_sum_filter_not]

/-- The coarse prediction, which omits the assignments with a repeated part, is at most the
stepped prediction. -/
theorem coarseInducedGraphEstimate3_le_steppedInducedGraphCount3
    (R : Finpartition (univ : Finset V)) :
    J.coarseInducedGraphEstimate3 G R ≤ J.steppedInducedGraphCount3 G R := by
  rw [steppedInducedGraphCount3_eq_add]
  exact le_add_of_nonneg_right (sum_nonneg fun φ _ ↦ mul_nonneg (by positivity)
    (prod_nonneg fun p _ ↦ ite_edgeDensity_nonneg G _ _ _))

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
        exact prod_le_one₀ (fun p _ ↦ ite_edgeDensity_nonneg G _ _ _)
          fun p _ ↦ ite_edgeDensity_le_one G _ _ _
    _ ≤ 3 * m * (Fintype.card V : ℝ) ^ 2 := by
        have := R.sum_prod_card_of_not_injective_le_of_card_le (ι := Fin 3) hm
        simp only [Fintype.card_fin, card_univ] at this
        exact_mod_cast this

omit [Fintype V] [DecidableEq V] in
/-- An edge or nonedge density factor changes by exactly as much as the edge density. -/
private lemma abs_ite_edgeDensity_sub (e : Prop) [Decidable e] (s t s' t' : Finset V) :
    |(if e then (G.edgeDensity s t : ℝ) else 1 - (G.edgeDensity s t : ℝ)) -
      (if e then (G.edgeDensity s' t' : ℝ) else 1 - (G.edgeDensity s' t' : ℝ))| =
      |(G.edgeDensity s t : ℝ) - G.edgeDensity s' t'| := by
  split_ifs
  · rfl
  · rw [abs_sub_comm (G.edgeDensity s t : ℝ)]
    congr 1
    ring

/-- Summed over all ordered pairs of vertices, the edge densities between the parts through them
change by at most `√ε * (card V) ^ 2` from a refinement `Q ≤ P` to `P` whose energy gap is at
most `ε`. -/
private lemma sum_sum_abs_edgeDensity_part_sub_le {P Q : Finpartition (univ : Finset V)}
    (h : Q ≤ P) {ε : ℝ} (hgap : G.weightedEnergy Q - G.weightedEnergy P ≤ ε) :
    ∑ x, ∑ y, |(G.edgeDensity (Q.part x) (Q.part y) : ℝ) -
      G.edgeDensity (P.part x) (P.part y)| ≤ √ε * Fintype.card V ^ 2 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- Group both vertices by their fine parts, each paired with its coarse parent.
  calc ∑ x, ∑ y, |(G.edgeDensity (Q.part x) (Q.part y) : ℝ) -
        G.edgeDensity (P.part x) (P.part y)|
      = ∑ x, ∑ D : Q.parts, #D.1 • |(G.edgeDensity (Q.part x) D.1 : ℝ) -
          G.edgeDensity (P.part x) (refinementParent h D).1| :=
        sum_congr rfl fun x _ ↦ Finpartition.sum_apply_part_part h fun B A ↦
          |(G.edgeDensity (Q.part x) B : ℝ) - G.edgeDensity (P.part x) A|
    _ = ∑ D : Q.parts, ∑ B : Q.parts, #B.1 • (#D.1 • |(G.edgeDensity B.1 D.1 : ℝ) -
          G.edgeDensity (refinementParent h B).1 (refinementParent h D).1|) := by
        rw [sum_comm]
        exact sum_congr rfl fun D _ ↦ Finpartition.sum_apply_part_part h fun B A ↦
          #D.1 • |(G.edgeDensity B D.1 : ℝ) - G.edgeDensity A (refinementParent h D).1|
    _ = (Fintype.card V : ℝ) ^ 2 * ∑ B : Q.parts, ∑ D : Q.parts,
          (#B.1 * #D.1 / (Fintype.card V : ℝ) ^ 2) * |(G.edgeDensity B.1 D.1 : ℝ) -
            G.edgeDensity (refinementParent h B).1 (refinementParent h D).1| := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun B _ ↦ ?_
        rw [mul_sum]
        refine sum_congr rfl fun D _ ↦ ?_
        rw [nsmul_eq_mul, nsmul_eq_mul]
        field_simp
    _ ≤ (Fintype.card V : ℝ) ^ 2 * √ε := by grw [G.weightedDensityDeviation_abs_le h hgap]
    _ = √ε * Fintype.card V ^ 2 := mul_comm _ _

/-- **Energy transfer.** For a refinement `Q ≤ P` whose size-weighted energy exceeds that of `P` by
at most `ε`, the stepped predictions of `Q` and `P` differ by at most `3 √ε (card V) ^ 3`. No
equitability or regularity is assumed. -/
theorem abs_steppedInducedGraphCount3_sub_le {P Q : Finpartition (univ : Finset V)} (h : Q ≤ P)
    {ε : ℝ} (hgap : G.weightedEnergy Q - G.weightedEnergy P ≤ ε) :
    |J.steppedInducedGraphCount3 G Q - J.steppedInducedGraphCount3 G P| ≤
      3 * √ε * (Fintype.card V : ℝ) ^ 3 := by
  set D : V → V → ℝ := fun x y ↦
    |(G.edgeDensity (Q.part x) (Q.part y) : ℝ) - G.edgeDensity (P.part x) (P.part y)|
  have habs (e : Prop) [Decidable e] (s t : Finset V) :
      |if e then (G.edgeDensity s t : ℝ) else 1 - (G.edgeDensity s t : ℝ)| ≤ 1 :=
    abs_le.2 ⟨by linarith [ite_edgeDensity_nonneg G e s t], ite_edgeDensity_le_one G e s t⟩
  rw [steppedInducedGraphCount3_eq_sum_part, steppedInducedGraphCount3_eq_sum_part,
    ← sum_sub_distrib]
  -- Telescope the three factors at each map, then sum each pair over the third vertex.
  calc _ ≤ ∑ g : Fin 3 → V, ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2}, D (g p.1.1) (g p.1.2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun g _ ↦ ?_)
        exact (TauCeti.abs_prod_sub_prod_le_sum_abs_sub _ (fun p _ ↦ habs _ _ _)
          (fun p _ ↦ habs _ _ _)).trans_eq
            (sum_congr rfl fun p _ ↦ abs_ite_edgeDensity_sub G _ _ _ _ _)
    _ = ∑ _p : {p : Fin 3 × Fin 3 // p.1 < p.2}, Fintype.card V • ∑ x, ∑ y, D x y := by
        rw [sum_comm]
        exact sum_congr rfl fun p _ ↦ by
          simpa using Fintype.sum_piFinset_apply_apply (ne_of_lt p.2) univ D
    _ = 3 * Fintype.card V * ∑ x, ∑ y, D x y := by
        have hpairs : Fintype.card {p : Fin 3 × Fin 3 // p.1 < p.2} = 3 := by decide
        rw [sum_const, card_univ, hpairs, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc]
        norm_num
    _ ≤ 3 * Fintype.card V * (√ε * Fintype.card V ^ 2) := by
        grw [sum_sum_abs_edgeDensity_part_sub_le G h hgap]
    _ = 3 * √ε * (Fintype.card V : ℝ) ^ 3 := by ring

end SimpleGraph
