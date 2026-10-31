/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.Placement
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import TauCeti.Order.Partition.Pi
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nontransversal placements of colored patterns

Fix a triadic complex `C` on `V` and a colored three-uniform pattern `F` on `k = F.k` vertices. A
placement of `F` into the vertex cells of `C` is *nontransversal* when it assigns two pattern
vertices to a common cell. An induced counting lemma for `F` treats these placements separately:
the local counting argument applies only to transversal placements, and the nontransversal ones
are discarded at a cost controlled by the sizes of the vertex cells. This file bounds that cost,
both for the actual embeddings and for the prediction.

On the predicted side, summing the local predictions `H.expectedInducedCountAt φ ψ` over all routes
`ψ` of a placement `φ` gives at most the injection count of `φ`: the pair-color densities of the
routes multiply out to a product of palette sums, each at most one. The injection counts of the
nontransversal placements add up to at most `k.choose 2 * m * |V| ^ (k - 1)` when every cell has
at most `m` vertices. The same bound holds for the embeddings `Fin k ↪ V` putting two pattern
vertices in a common cell.

When the vertex cells form an equipartition into at least `t₀` cells, each cell has at most about
`|V| / t₀` vertices, so `t₀` times the actual and predicted nontransversal mass is at most
`4 * k.choose 2 * |V| ^ k`. The floor `diagonalControl3 k ε = ⌈24 * k.choose 2 / ε⌉₊` therefore
makes this mass at most `ε / 6 * |V| ^ k`.

## Main definitions

* `TauCeti.diagonalControl3`: the number of vertex cells making the nontransversal mass small.
* `TauCeti.Colored3Graph.nontransversalPredictedMass3`: the total prediction of the nontransversal
  placements.

## Main results

* `TauCeti.sum_placementInjectionCount_of_not_transversal_le_of_card_le`: the injection counts of
  the nontransversal placements are small when the cells are small.
* `TauCeti.Colored3Graph.nontransversal_actual_and_predicted_mass_mul_le`: with an equipartition
  into at least `t₀` cells, `t₀` times the actual and predicted nontransversal mass is at most
  `4 * k.choose 2 * |V| ^ k`.
* `TauCeti.Colored3Graph.nontransversal_actual_and_predicted_mass_le`: with at least
  `diagonalControl3 k ε` cells, the actual and predicted nontransversal mass is at most
  `ε / 6 * |V| ^ k`.

## References

* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Function

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V] {C : TriadicComplex3 V}
  {F : FiniteColored3Pattern κ}

/-- The floor on the number of vertex cells that makes the nontransversal mass of a pattern on `k`
vertices at most `ε / 6 * |V| ^ k`. -/
noncomputable def diagonalControl3 (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈24 * k.choose 2 / ε⌉₊

theorem diagonalControl3_def (k : ℕ) (ε : ℝ) : diagonalControl3 k ε = ⌈24 * k.choose 2 / ε⌉₊ :=
  (rfl)

theorem le_diagonalControl3 (k : ℕ) (ε : ℝ) : 24 * k.choose 2 / ε ≤ diagonalControl3 k ε :=
  Nat.le_ceil _

/-- If every vertex cell has at most `m` vertices, the injection counts of the nontransversal
placements of a pattern on `k` vertices add up to at most `k.choose 2 * m * |V| ^ (k - 1)`. -/
theorem sum_placementInjectionCount_of_not_transversal_le_of_card_le
    [DecidablePred fun φ : PatternPlacement3 C F ↦ φ.Transversal] {m : ℕ}
    (hm : ∀ A ∈ C.skeleton.vertexPart.parts, #A ≤ m) :
    ∑ φ : PatternPlacement3 C F with ¬φ.Transversal, placementInjectionCount φ ≤
      F.k.choose 2 * m * Fintype.card V ^ (F.k - 1) := by
  classical
  -- A placement is a map from the pattern vertices to the vertex cells.
  let e : PatternPlacement3 C F ≃ (Fin F.k → C.skeleton.vertexPart.parts) :=
    { toFun φ i := ⟨φ.vertexCell i, φ.vertexCell_mem i⟩
      invFun c := ⟨fun i ↦ c i, fun i ↦ (c i).2⟩ }
  calc ∑ φ : PatternPlacement3 C F with ¬φ.Transversal, placementInjectionCount φ
      ≤ ∑ φ : PatternPlacement3 C F with ¬φ.Transversal, ∏ i, #(φ.vertexCell i) :=
        sum_le_sum fun φ _ ↦ placementInjectionCount_le_prod φ
    _ = ∑ c : Fin F.k → C.skeleton.vertexPart.parts with ¬Injective c,
          ∏ i, #(c i : Finset V) := by
        -- The cells of `e φ` are, by construction, the cells of `φ`.
        refine sum_equiv e (fun φ ↦ ?_) fun φ _ ↦ rfl
        simp only [mem_filter, mem_univ, true_and, PatternPlacement3.transversal_iff]
        exact not_congr (Subtype.val_injective.of_comp_iff (e φ))
    _ ≤ F.k.choose 2 * m * Fintype.card V ^ (F.k - 1) := by
        simpa using C.skeleton.vertexPart.sum_prod_card_of_not_injective_le_of_card_le
          (ι := Fin F.k) hm

namespace Colored3Graph

variable [DecidableEq κ] (H : Colored3Graph κ V)

variable (C F) in
open Classical in
/-- The predicted mass of the nontransversal placements of `F` over `C`: the sum of the local
predictions over the placements assigning two pattern vertices to a common cell and all their
routes. -/
noncomputable def nontransversalPredictedMass3 : ℝ :=
  ∑ φ : PatternPlacement3 C F with ¬φ.Transversal,
    ∑ ψ : PairColorPlacement3 φ, H.expectedInducedCountAt φ ψ

variable (C F) in
open Classical in
theorem nontransversalPredictedMass3_def :
    H.nontransversalPredictedMass3 C F =
      ∑ φ : PatternPlacement3 C F with ¬φ.Transversal,
        ∑ ψ : PairColorPlacement3 φ, H.expectedInducedCountAt φ ψ :=
  (rfl)

variable (C F) in
/-- The predicted nontransversal mass is nonnegative. -/
theorem nontransversalPredictedMass3_nonneg : 0 ≤ H.nontransversalPredictedMass3 C F :=
  sum_nonneg fun φ _ ↦ sum_nonneg fun ψ _ ↦ H.expectedInducedCountAt_nonneg φ ψ

/-- If every vertex cell has at most `m` vertices, the predicted nontransversal mass of a pattern
on `k` vertices is at most `k.choose 2 * m * |V| ^ (k - 1)`. -/
theorem nontransversalPredictedMass3_le_of_card_le {m : ℕ}
    (hm : ∀ A ∈ C.skeleton.vertexPart.parts, #A ≤ m) :
    H.nontransversalPredictedMass3 C F ≤ F.k.choose 2 * m * Fintype.card V ^ (F.k - 1) := by
  classical
  rw [nontransversalPredictedMass3_def]
  refine (sum_le_sum fun φ _ ↦ H.sum_expectedInducedCountAt_le_placementInjectionCount φ).trans ?_
  exact_mod_cast sum_placementInjectionCount_of_not_transversal_le_of_card_le hm

/-- **Nontransversal mass.** If the vertex cells of `C` form an equipartition into at least `t₀`
cells, then `t₀` times the number of embeddings of the pattern vertices putting two of them in a
common cell, plus `t₀` times the predicted nontransversal mass, is at most
`4 * k.choose 2 * |V| ^ k`. -/
theorem nontransversal_actual_and_predicted_mass_mul_le {t₀ : ℕ}
    (hC : C.VertexCellsControlled t₀) :
    (t₀ : ℝ) * (#{f : Fin F.k ↪ V | ∃ i j, i ≠ j ∧
          ∃ A ∈ C.skeleton.vertexPart.parts, f i ∈ A ∧ f j ∈ A} +
        H.nontransversalPredictedMass3 C F) ≤
      4 * F.k.choose 2 * (Fintype.card V : ℝ) ^ F.k := by
  rcases Nat.eq_zero_or_pos t₀ with rfl | ht₀
  · simp only [Nat.cast_zero, zero_mul]
    positivity
  -- Every cell has at most `m = |V| / t₀ + 1` vertices, and `t₀ * m ≤ 2 * |V|`.
  set m := Fintype.card V / t₀ + 1
  have hm (A) (hA : A ∈ C.skeleton.vertexPart.parts) : #A ≤ m := hC.card_le ht₀ hA
  have htm : t₀ * m ≤ 2 * Fintype.card V := by
    have hparts := (TriadicComplex3.vertexCellsControlled_iff.1 hC).2.trans
      (C.skeleton.vertexPart.card_parts_le_card.trans_eq card_univ)
    have := Nat.mul_div_le (Fintype.card V) t₀
    rw [mul_add, mul_one]
    omega
  -- Both the actual and the predicted mass are at most `k.choose 2 * m * |V| ^ (k - 1)`.
  have hA : (#{f : Fin F.k ↪ V | ∃ i j, i ≠ j ∧
      ∃ A ∈ C.skeleton.vertexPart.parts, f i ∈ A ∧ f j ∈ A} : ℝ) ≤
        F.k.choose 2 * m * (Fintype.card V : ℝ) ^ (F.k - 1) := by
    exact_mod_cast by
      simpa using C.skeleton.vertexPart.card_embedding_exists_mem_part_le_of_card_le
        (ι := Fin F.k) hm
  have hP := H.nontransversalPredictedMass3_le_of_card_le (F := F) hm
  have hX : t₀ * (2 * (F.k.choose 2 * m * Fintype.card V ^ (F.k - 1))) ≤
      4 * F.k.choose 2 * Fintype.card V ^ F.k := by
    rcases Nat.eq_zero_or_pos F.k with hk | hk
    · simp [hk]
    calc t₀ * (2 * (F.k.choose 2 * m * Fintype.card V ^ (F.k - 1)))
        = 2 * F.k.choose 2 * (t₀ * m) * Fintype.card V ^ (F.k - 1) := by ring
      _ ≤ 2 * F.k.choose 2 * (2 * Fintype.card V) * Fintype.card V ^ (F.k - 1) := by gcongr
      _ = 4 * F.k.choose 2 * Fintype.card V ^ (F.k - 1 + 1) := by ring
      _ = 4 * F.k.choose 2 * Fintype.card V ^ F.k := by rw [Nat.sub_add_cancel hk]
  calc (t₀ : ℝ) * (#{f : Fin F.k ↪ V | ∃ i j, i ≠ j ∧
          ∃ A ∈ C.skeleton.vertexPart.parts, f i ∈ A ∧ f j ∈ A} +
        H.nontransversalPredictedMass3 C F)
      ≤ t₀ * (2 * (F.k.choose 2 * m * (Fintype.card V : ℝ) ^ (F.k - 1))) := by
        gcongr
        linarith
    _ ≤ 4 * F.k.choose 2 * (Fintype.card V : ℝ) ^ F.k := by exact_mod_cast hX

/-- **Nontransversal mass at the diagonal floor.** If the vertex cells of `C` form an equipartition
into at least `diagonalControl3 k ε` cells, then the number of embeddings of the pattern vertices
putting two of them in a common cell, plus the predicted nontransversal mass, is at most
`ε / 6 * |V| ^ k`. -/
theorem nontransversal_actual_and_predicted_mass_le {ε : ℝ} (hε : 0 < ε)
    (hC : C.VertexCellsControlled (diagonalControl3 F.k ε)) :
    #{f : Fin F.k ↪ V | ∃ i j, i ≠ j ∧ ∃ A ∈ C.skeleton.vertexPart.parts, f i ∈ A ∧ f j ∈ A} +
        H.nontransversalPredictedMass3 C F ≤
      ε / 6 * (Fintype.card V : ℝ) ^ F.k := by
  rcases Nat.eq_zero_or_pos (F.k.choose 2) with hk | hk
  · -- Without two distinct pattern vertices, there is no nontransversal mass.
    have hA : (#{f : Fin F.k ↪ V | ∃ i j, i ≠ j ∧
        ∃ A ∈ C.skeleton.vertexPart.parts, f i ∈ A ∧ f j ∈ A} : ℝ) ≤ 0 := by
      exact_mod_cast by
        simpa [hk] using C.skeleton.vertexPart.card_embedding_exists_mem_part_le_of_card_le
          (ι := Fin F.k) (m := Fintype.card V) fun A _ ↦ card_le_univ A
    have hP := H.nontransversalPredictedMass3_le_of_card_le (C := C) (F := F)
      (m := Fintype.card V) fun A _ ↦ card_le_univ A
    rw [hk, Nat.cast_zero, zero_mul, zero_mul] at hP
    have : 0 ≤ ε / 6 * (Fintype.card V : ℝ) ^ F.k := by positivity
    linarith
  -- Otherwise the floor `t₀ = diagonalControl3 k ε` is positive and `24 * k.choose 2 ≤ t₀ * ε`.
  have hD := le_diagonalControl3 F.k ε
  rw [div_le_iff₀ hε] at hD
  have hk' : (0 : ℝ) < 24 * F.k.choose 2 := by exact_mod_cast Nat.mul_pos (by norm_num) hk
  have hDpos : (0 : ℝ) < diagonalControl3 F.k ε := by nlinarith
  refine le_of_mul_le_mul_left ?_ hDpos
  calc _ ≤ 4 * F.k.choose 2 * (Fintype.card V : ℝ) ^ F.k :=
        H.nontransversal_actual_and_predicted_mass_mul_le hC
    _ = 24 * F.k.choose 2 * ((Fintype.card V : ℝ) ^ F.k / 6) := by ring
    _ ≤ diagonalControl3 F.k ε * ε * ((Fintype.card V : ℝ) ^ F.k / 6) := by gcongr
    _ = diagonalControl3 F.k ε * (ε / 6 * (Fintype.card V : ℝ) ^ F.k) := by ring

end Colored3Graph

end TauCeti
