/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graph.InducedCount
public import TauCeti.Combinatorics.Regularity.Partition.Energy
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Order.BigOperators.ProdSubProd
import TauCeti.Algebra.Order.Group.Abs
import TauCeti.Data.Fintype.BigOperators

/-!
# Stepped induced three-vertex counts and energy transfer

For a graph `J` on `Fin 3`, a finite graph `G` and a partition `R` of its vertices,
`J.steppedInducedGraphCount3 G R` is the number of labelled induced copies of `J` predicted by the
densities between the parts of `R`, summed over **all** assignments `φ` of the three vertices of
`J` to parts of `R`, repeated parts included. Each assignment contributes the volume
`∏ i, #(φ i)` times, for each pair `i < j`, the edge density `d(φ i, φ j)` if `J.Adj i j` and the
nonedge density `1 - d(φ i, φ j)` otherwise. Equivalently
(`SimpleGraph.steppedInducedGraphCount3_eq_sum_part`), it is the induced weight of `J` in the
step function `(x, y) ↦ d(R.part x, R.part y)`, summed over all maps `Fin 3 → V`.

Unlike `SimpleGraph.coarseInducedGraphEstimate3`, which discards the assignments with a repeated
part, this prediction is stable under refinement: if `Q ≤ P` and the size-weighted energy rises
by at most `ε` from `P` to `Q`, the two predictions differ by at most `3 √ε |V|³`
(`SimpleGraph.abs_steppedInducedGraphCount3_sub_le`). Each of the three factors changes by the
difference of two step functions, whose `ℓ¹` distance is controlled by the energy gap
(`SimpleGraph.sum_sum_abs_edgeDensity_part_sub_le`). Dropping the repeated-part assignments
recovers the coarse prediction up to `3 m |V|²` when all parts have size at most `m`.

In the counting lemma for strong regularity, these estimates carry the prediction from the fine
partition, where regularity holds, to the coarse partition.

## Main definitions

* `SimpleGraph.steppedInducedGraphCount3 J G R`: the prediction of the induced count of `J` from
  the densities of `R`, over all assignments of vertices to parts.

## Main results

* `SimpleGraph.steppedInducedGraphCount3_eq_sum_part`: the prediction as a sum over all maps
  `Fin 3 → V`.
* `SimpleGraph.abs_steppedInducedGraphCount3_sub_le`: energy transfer between nested partitions.
* `SimpleGraph.coarseInducedGraphEstimate3_le_steppedInducedGraphCount3` and
  `SimpleGraph.steppedInducedGraphCount3_le_coarseInducedGraphEstimate3_add`: the coarse
  prediction falls short of this one by at most `3 * m * (card V) ^ 2`.

## References

* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 2 (the graph regularity method: the graph counting lemma and strong regularity).
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
-/

public section

open Finset
open Function (Injective)

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The prediction of `J.inducedGraphCount3 G` from the densities between the parts of `R`, over
all assignments `φ` of the vertices of `J` to parts of `R`, repeated parts included. Each
assignment contributes the volume `∏ i, #(φ i)` times, for each pair `i < j`, the edge density
`d(φ i, φ j)` if `J.Adj i j` and the nonedge density `1 - d(φ i, φ j)` otherwise. -/
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

/-- The stepped prediction is the induced weight of `J` in the step function
`(x, y) ↦ d(R.part x, R.part y)`, summed over all maps `g : Fin 3 → V`. -/
theorem steppedInducedGraphCount3_eq_sum_part (R : Finpartition (univ : Finset V)) :
    J.steppedInducedGraphCount3 G R = ∑ g : Fin 3 → V, ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      if J.Adj p.1.1 p.1.2 then (G.edgeDensity (R.part (g p.1.1)) (R.part (g p.1.2)) : ℝ)
      else 1 - (G.edgeDensity (R.part (g p.1.1)) (R.part (g p.1.2)) : ℝ) := by
  rw [← Fintype.piFinset_univ, ← R.sum_sum_piFinset_parts, steppedInducedGraphCount3_def]
  refine sum_congr rfl fun φ _ ↦ ?_
  -- On the box of `φ`, `R.part (g i) = φ i`, so the summand no longer depends on `g`; the
  -- closing `rfl` only instantiates the summand metavariable left by `sum_congr` to that constant.
  rw [sum_congr rfl fun g hg ↦ by simp_rw [R.part_eq_of_mem_piFinset_parts hg]; rfl, sum_const,
    Fintype.card_piFinset, nsmul_eq_mul, Nat.cast_prod]

/-- **Energy transfer.** If `Q` refines `P` and the size-weighted energy of `Q` exceeds that of
`P` by at most `ε`, then the stepped predictions of the induced count of `J` from `Q` and from `P`
differ by at most `3 √ε (card V) ^ 3`. No equitability or regularity is assumed. -/
theorem abs_steppedInducedGraphCount3_sub_le {P Q : Finpartition (univ : Finset V)} (h : Q ≤ P)
    {ε : ℝ} (hgap : G.weightedEnergy Q - G.weightedEnergy P ≤ ε) :
    |J.steppedInducedGraphCount3 G Q - J.steppedInducedGraphCount3 G P| ≤
      3 * √ε * (Fintype.card V : ℝ) ^ 3 := by
  set D : V → V → ℝ := fun x y ↦
    |(G.edgeDensity (Q.part x) (Q.part y) : ℝ) - G.edgeDensity (P.part x) (P.part y)|
  -- Each pair of coordinates sees the step-function distance once for every value of the third.
  have hpair (p : {p : Fin 3 × Fin 3 // p.1 < p.2}) :
      ∑ g : Fin 3 → V, D (g p.1.1) (g p.1.2) ≤ √ε * (Fintype.card V : ℝ) ^ 3 := by
    rw [Fintype.sum_apply_apply_of_ne p.2.ne, Fintype.card_fin, nsmul_eq_mul]
    grw [G.sum_sum_abs_edgeDensity_part_sub_le h hgap]
    exact le_of_eq (by push_cast; ring)
  have hcard : Fintype.card {p : Fin 3 × Fin 3 // p.1 < p.2} = 3 := by decide
  rw [steppedInducedGraphCount3_eq_sum_part, steppedInducedGraphCount3_eq_sum_part,
    ← sum_sub_distrib]
  calc _ ≤ ∑ g : Fin 3 → V, ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2}, D (g p.1.1) (g p.1.2) := by
        refine (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun g _ ↦ ?_
        refine (TauCeti.abs_prod_sub_prod_le_sum_abs_sub _ (fun p _ ↦ ?_) fun p _ ↦ ?_).trans_eq
          (sum_congr rfl fun p _ ↦ TauCeti.abs_ite_sub_ite _ _ _ _)
        all_goals
          obtain ⟨h₀, h₁⟩ := ite_edgeDensity_mem_Icc G (J.Adj p.1.1 p.1.2) _ _
          exact abs_le.2 ⟨by linarith, h₁⟩
    _ = ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2}, ∑ g : Fin 3 → V, D (g p.1.1) (g p.1.2) := sum_comm
    _ ≤ ∑ _p : {p : Fin 3 × Fin 3 // p.1 < p.2}, √ε * (Fintype.card V : ℝ) ^ 3 :=
        sum_le_sum fun p _ ↦ hpair p
    _ = 3 * √ε * (Fintype.card V : ℝ) ^ 3 := by
        rw [sum_const, card_univ, hcard, nsmul_eq_mul, Nat.cast_ofNat, mul_assoc]

/-- Each assignment contributes a nonnegative amount, at most its volume. -/
private theorem mem_Icc_assignment_term (R : Finpartition (univ : Finset V))
    (φ : Fin 3 → R.parts) :
    (∏ i, (#(φ i : Finset V) : ℝ)) * (∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        if J.Adj p.1.1 p.1.2 then (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ)
        else 1 - (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ)) ∈
      Set.Icc 0 (∏ i, (#(φ i : Finset V) : ℝ)) := by
  have hfac (p : {p : Fin 3 × Fin 3 // p.1 < p.2}) :=
    ite_edgeDensity_mem_Icc G (J.Adj p.1.1 p.1.2) (φ p.1.1 : Finset V) (φ p.1.2)
  exact ⟨mul_nonneg (by positivity) (prod_nonneg fun p _ ↦ (hfac p).1),
    mul_le_of_le_one_right (by positivity)
      (prod_le_one₀ (fun p _ ↦ (hfac p).1) fun p _ ↦ (hfac p).2)⟩

/-- The coarse prediction, which discards the assignments with a repeated part, is at most the
stepped prediction. -/
theorem coarseInducedGraphEstimate3_le_steppedInducedGraphCount3
    (R : Finpartition (univ : Finset V)) :
    J.coarseInducedGraphEstimate3 G R ≤ J.steppedInducedGraphCount3 G R := by
  rw [coarseInducedGraphEstimate3_def, steppedInducedGraphCount3_def,
    ← sum_filter_add_sum_filter_not univ fun φ ↦ Injective φ]
  exact le_add_of_nonneg_right (sum_nonneg fun φ _ ↦ (mem_Icc_assignment_term J G R φ).1)

/-- The stepped prediction is nonnegative. -/
theorem steppedInducedGraphCount3_nonneg (R : Finpartition (univ : Finset V)) :
    0 ≤ J.steppedInducedGraphCount3 G R :=
  (J.coarseInducedGraphEstimate3_nonneg G R).trans
    (J.coarseInducedGraphEstimate3_le_steppedInducedGraphCount3 G R)

/-- **Repeated-part bound for predictions.** If every part of `R` has at most `m` vertices, the
stepped prediction exceeds the coarse prediction by at most `3 * m * (card V) ^ 2`. -/
theorem steppedInducedGraphCount3_le_coarseInducedGraphEstimate3_add
    (R : Finpartition (univ : Finset V)) {m : ℕ} (hm : ∀ A ∈ R.parts, #A ≤ m) :
    J.steppedInducedGraphCount3 G R ≤
      J.coarseInducedGraphEstimate3 G R + 3 * m * (Fintype.card V : ℝ) ^ 2 := by
  rw [coarseInducedGraphEstimate3_def, steppedInducedGraphCount3_def,
    ← sum_filter_add_sum_filter_not univ fun φ ↦ Injective φ]
  -- The assignments with a repeated part have small total volume.
  have hvol : ∑ φ : Fin 3 → R.parts with ¬Injective φ, ∏ i, #(φ i : Finset V) ≤
      3 * m * Fintype.card V ^ 2 := by
    simpa using R.sum_prod_card_of_not_injective_le_of_card_le (ι := Fin 3) hm
  have hvol' : ∑ φ : Fin 3 → R.parts with ¬Injective φ, ∏ i, (#(φ i : Finset V) : ℝ) ≤
      3 * m * (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast hvol
  exact add_le_add le_rfl
    ((sum_le_sum fun φ _ ↦ (mem_Icc_assignment_term J G R φ).2).trans hvol')

end SimpleGraph
