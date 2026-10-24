/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graph.SteppedInducedCount
import TauCeti.Combinatorics.Regularity.Graph.Counting
public import TauCeti.Combinatorics.Regularity.Graph.UniformPartition
import Mathlib.Algebra.BigOperators.Fin

/-!
# Induced counting from uniform equipartitions

An equitable uniform partition predicts labelled induced three-vertex counts through its stepped
prediction. Local counting handles regular transversal boxes, a union bound charges irregular
pairs, and repeated-cell boxes cost their volume once.

## References

* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 2 (strong regularity and induced counting).
-/

public section

open Finset Function SimpleGraph

namespace TauCeti.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]

/-- The error on one box: regular transversal boxes use counting; all other boxes cost volume. -/
private lemma abs_card_induced_box_sub_le (P : Finpartition (univ : Finset V))
    {τ : ℝ} (hτ : 0 ≤ τ) (φ : Fin 3 → P.parts) :
    |(#{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
        Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} : ℝ) -
      (∏ i, (#(φ i : Finset V) : ℝ)) *
        ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2)| ≤
      3 * τ * (∏ i, (#(φ i : Finset V) : ℝ)) +
        (if Injective φ then 0 else ∏ i, (#(φ i : Finset V) : ℝ)) +
        ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ P.nonUniforms G τ then
            ∏ i, (#(φ i : Finset V) : ℝ) else 0 := by
  classical
  let W : ℝ := ∏ i, (#(φ i : Finset V) : ℝ)
  have hW : 0 ≤ W := by positivity
  -- Both the actual and predicted counts lie in the interval from zero to the box volume.
  have hrough : |(#{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
      Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} : ℝ) -
      W * ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2)| ≤ W := by
    have hcount : (#{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
        Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} : ℝ) ≤ W := by
      simpa only [W, ← Nat.cast_prod, ← Fintype.card_piFinset, Nat.cast_le] using
        card_filter_le (Fintype.piFinset fun i ↦ (φ i : Finset V))
          (fun g ↦ Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j))
    have hp₀ : (0 : ℝ) ≤ ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2) :=
      prod_nonneg fun p _ ↦ G.patternDensity_nonneg _ _ _
    have hp₁ : (∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2) : ℝ) ≤ 1 :=
      prod_le_one₀ (fun p _ ↦ G.patternDensity_nonneg _ _ _)
        fun p _ ↦ G.patternDensity_le_one _ _ _
    have hc₀ : (0 : ℝ) ≤ #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
        Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} := Nat.cast_nonneg _
    exact abs_sub_le_iff.2 ⟨by nlinarith, by nlinarith⟩
  have hsum₀ : (0 : ℝ) ≤ ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ P.nonUniforms G τ then W else 0 :=
    sum_nonneg fun _ _ ↦ by positivity
  by_cases hφ : Injective φ
  · simp only [ite_eq_left hφ, add_zero]
    -- Transversal regular boxes satisfy the local induced counting lemma.
    by_cases hreg : ∀ i j, i < j → G.IsUniform τ (φ i) (φ j)
    · have hc : {g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
          Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} =
        {g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
          ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} :=
        filter_congr fun g hg ↦ and_iff_right (P.injective_of_mem_piFinset_parts hφ hg)
      rw [hc]
      exact (abs_card_induced_fin_three_sub_le J hreg).trans (le_add_of_nonneg_right hsum₀)
    · -- An irregular pair charges the whole box once in the pair sum.
      push Not at hreg
      obtain ⟨i, j, hij, hnu⟩ := hreg
      have hbad : ((φ i : Finset V), (φ j : Finset V)) ∈ P.nonUniforms G τ :=
        (P.mk_mem_nonUniforms G).2 ⟨(φ i).2, (φ j).2,
          Subtype.coe_ne_coe.2 (hφ.ne (ne_of_lt hij)), hnu⟩
      have hsingle := single_le_sum (s := (univ : Finset {p : Fin 3 × Fin 3 // p.1 < p.2}))
        (f := fun p ↦ if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈
          P.nonUniforms G τ then W else 0)
        (fun _ _ ↦ by positivity) (mem_univ ⟨(i, j), hij⟩)
      simp only [hbad, ite_true] at hsingle
      exact hrough.trans (by nlinarith)
  · -- Nontransversal boxes are covered by the repeated-cell charge.
    simp only [ite_eq_right hφ]
    exact hrough.trans (by nlinarith)

/-- An equitable `τ`-uniform partition predicts every labelled induced three-vertex count,
with error at most `15 τ n³ + 3 m n²`, where `n = card V`. When every part has at most `m`
vertices, `3 m n²` bounds the volume of triples meeting a cell twice. -/
theorem abs_inducedGraphCount3_sub_steppedInducedGraphCount3_le
    (P : Finpartition (univ : Finset V)) {τ : ℝ} (hτ : 0 < τ)
    (hP : P.IsEquipartition) (hG : P.IsUniform G τ) {m : ℕ}
    (hm : ∀ A ∈ P.parts, #A ≤ m) :
    |(J.inducedGraphCount3 G : ℝ) - J.steppedInducedGraphCount3 G P| ≤
      15 * τ * (Fintype.card V : ℝ) ^ 3 + 3 * m * (Fintype.card V : ℝ) ^ 2 := by
  classical
  let W (φ : Fin 3 → P.parts) : ℝ := ∏ i, (#(φ i : Finset V) : ℝ)
  have hvol : ∑ φ : Fin 3 → P.parts, W φ = (Fintype.card V : ℝ) ^ 3 := by
    rw [← Fintype.prod_sum (fun _ : Fin 3 ↦ fun A : P.parts ↦ (#(A : Finset V) : ℝ))]
    simp only [P.sum_card_subtype, card_univ, Fin.prod_univ_three]; ring
  have hrepeated : (∑ φ : Fin 3 → P.parts, if Injective φ then 0 else W φ) ≤
      3 * m * (Fintype.card V : ℝ) ^ 2 := by
    have h := P.sum_prod_card_of_not_injective_le_of_card_le (ι := Fin 3) hm
    simp only [Fintype.card_fin, card_univ] at h
    have heq : (∑ φ : Fin 3 → P.parts, if Injective φ then 0 else W φ) =
        ∑ φ : Fin 3 → P.parts with ¬Injective φ, W φ := by
      simp only [sum_filter, ite_not]
    rw [heq]
    dsimp only [W]
    exact_mod_cast h
  have hbad : (∑ φ : Fin 3 → P.parts,
      ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ P.nonUniforms G τ then
          W φ else 0) ≤ 12 * τ * (Fintype.card V : ℝ) ^ 3 := by
    rw [sum_comm]
    calc
      _ ≤ ∑ _p : {p : Fin 3 × Fin 3 // p.1 < p.2},
            4 * τ * (Fintype.card V : ℝ) ^ 3 := by
        refine sum_le_sum fun p _ ↦ ?_
        simpa only [mul_ite, mul_one, mul_zero, Fintype.card_fin] using
          sum_volume_nonUniform_pair_le G P hτ hP hG (ne_of_lt p.2)
      _ = _ := by
        have hpairs : Fintype.card {p : Fin 3 × Fin 3 // p.1 < p.2} = 3 := by decide
        simp only [sum_const, card_univ, hpairs, nsmul_eq_mul]
        ring
  -- Sum the boxwise errors, charging irregular pairs and repeated cells separately.
  rw [J.inducedGraphCount3_eq_sum G P, Nat.cast_sum, steppedInducedGraphCount3_def,
    ← sum_sub_distrib]
  calc _ ≤ ∑ φ : Fin 3 → P.parts,
        |(#{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
            Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} : ℝ) -
          W φ * ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
            G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ φ : Fin 3 → P.parts, (3 * τ * W φ + (if Injective φ then 0 else W φ) +
        ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ P.nonUniforms G τ then
            W φ else 0) := sum_le_sum fun φ _ ↦ abs_card_induced_box_sub_le G J P hτ.le φ
    _ ≤ _ := by
      simp only [sum_add_distrib, ← mul_sum, hvol]
      linarith

end TauCeti.SimpleGraph
