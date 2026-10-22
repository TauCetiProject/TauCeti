/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graph.StrongRegularity
public import TauCeti.Combinatorics.Regularity.Graph.SteppedInducedCount
import TauCeti.Combinatorics.Regularity.Graph.Counting
import TauCeti.Data.Fintype.BigOperators

/-!
# Induced counting from strong graph regularity

A strong regularity witness controls the labelled induced count of every three-vertex graph
by the density prediction on its coarse partition. The error consists of fine-pair irregularity,
the square root of the weighted-energy gap, and triples meeting a cell twice. Both edges and
nonedges enter the prediction, and counts are not divided by automorphisms.

The intermediate estimate compares the actual count with the stepped prediction of an equitable
uniform partition. An irregular pair occupies at most four times the uniformity parameter of the
vertex-pair space. A union bound over the three pattern pairs and the counting lemma on regular
cell triples then control the transversal error. Repeated-cell contributions cost their volume
only once, since both actual and predicted counts lie between zero and that volume.

## References

* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 2 (strong regularity and induced counting).
-/

public section

open Finset Function

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The volume charged to one irregular pair of roles in a triple of cells. -/
private lemma sum_volume_nonUniform_pair_le (P : Finpartition (univ : Finset V))
    {τ : ℝ} (hτ : 0 < τ) (hP : P.IsEquipartition) (hG : P.IsUniform G τ)
    {i j : Fin 3} (hij : i ≠ j) :
    (∑ φ : Fin 3 → P.parts, (∏ k, (#(φ k : Finset V) : ℝ)) *
      if ((φ i : Finset V), (φ j : Finset V)) ∈ P.nonUniforms G τ then 1 else 0) ≤
        4 * τ * (Fintype.card V : ℝ) ^ 3 := by
  classical
  let B := (P.nonUniforms G τ).biUnion fun q ↦ q.1 ×ˢ q.2
  have hmem (x y : V) :
      (P.part x, P.part y) ∈ P.nonUniforms G τ ↔ (x, y) ∈ B := by
    constructor
    · intro h
      exact mem_biUnion.2 ⟨_, h, mem_product.2 ⟨P.mem_part (mem_univ _), P.mem_part (mem_univ _)⟩⟩
    · intro h
      obtain ⟨⟨A, C⟩, hAC, hxy⟩ := mem_biUnion.1 h
      obtain ⟨hA, hC, _, _⟩ := (P.mk_mem_nonUniforms G).1 hAC
      rw [mem_product] at hxy
      rwa [P.part_eq_of_mem hA hxy.1, P.part_eq_of_mem hC hxy.2]
  have hsum : (∑ x : V, ∑ y : V,
      if (P.part x, P.part y) ∈ P.nonUniforms G τ then (1 : ℝ) else 0) = #B := by
    simp_rw [hmem]
    rw [← Fintype.sum_prod_type (fun q : V × V ↦ if q ∈ B then (1 : ℝ) else 0)]
    simp
  have htransfer := P.sum_piFinset_apply_part (ι := Fin 3)
    (fun A ↦ if (A i, A j) ∈ P.nonUniforms G τ then (1 : ℝ) else 0)
  simp only [Fintype.piFinset_univ, nsmul_eq_mul, Nat.cast_prod] at htransfer
  rw [← htransfer]
  have hpairs := Fintype.sum_piFinset_apply_apply hij (univ : Finset V)
    (fun x y ↦ if (P.part x, P.part y) ∈ P.nonUniforms G τ then (1 : ℝ) else 0)
  simp only [Fintype.piFinset_univ, card_univ, Fintype.card_fin, Nat.reduceSub, pow_one,
    nsmul_eq_mul, hsum] at hpairs
  rw [hpairs]
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  · have hB := hP.sum_nonUniforms_lt (G := G) (univ_nonempty : (univ : Finset V).Nonempty) hτ hG
    simp only [card_univ] at hB
    calc (Fintype.card V : ℝ) * #B ≤ Fintype.card V * (4 * τ * Fintype.card V ^ 2) :=
          mul_le_mul_of_nonneg_left hB.le (Nat.cast_nonneg _)
      _ = _ := by ring

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
with error at most `15 τ n³` plus the volume of triples meeting a cell twice. -/
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
    norm_num at h
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
        simpa only [mul_ite, mul_one, mul_zero] using
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

variable {G} in
/-- **Strong regularity induced counting.** The densities on the coarse partition of a strong
regularity witness predict every labelled induced three-vertex pattern. No automorphism factor
is removed. The error includes irregular fine pairs, the energy gap, and repeated-cell triples. -/
theorem StrongRegular.inducedGraphCount3_estimate
    {P Q : Finpartition (univ : Finset V)} {ε : ℝ} {F : ℕ → ℝ} {l₀ : ℕ}
    (h : G.StrongRegular P Q ε F l₀) (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]
    (hF : 0 < F #P.parts) {m : ℕ} (hm : ∀ A ∈ P.parts, #A ≤ m) :
    |(J.inducedGraphCount3 G : ℝ) - J.coarseInducedGraphEstimate3 G P| ≤
      (16 * F #P.parts + 3 * √ε) * (Fintype.card V : ℝ) ^ 3 +
        6 * m * (Fintype.card V : ℝ) ^ 2 := by
  have hmQ (B : Finset V) (hB : B ∈ Q.parts) : #B ≤ m :=
    (card_le_card (Finpartition.le_refinementParent h.refines ⟨B, hB⟩)).trans
      (hm _ (Finpartition.refinementParent h.refines ⟨B, hB⟩).2)
  have hcount :=
    abs_inducedGraphCount3_sub_steppedInducedGraphCount3_le G J Q hF h.equitQ h.regQ hmQ
  have henergy := J.abs_steppedInducedGraphCount3_sub_le G h.refines h.energyClose
  have hdiag := J.steppedInducedGraphCount3_le_coarseInducedGraphEstimate3_add G P hm
  have hdiag₀ := J.coarseInducedGraphEstimate3_le_steppedInducedGraphCount3 G P
  have hdiag' : |J.steppedInducedGraphCount3 G P - J.coarseInducedGraphEstimate3 G P| ≤
      3 * m * (Fintype.card V : ℝ) ^ 2 := by
    rw [abs_of_nonneg (sub_nonneg.2 hdiag₀)]
    linarith
  have htriangle := (abs_sub_le (J.inducedGraphCount3 G : ℝ)
    (J.steppedInducedGraphCount3 G Q) (J.coarseInducedGraphEstimate3 G P)).trans
      (add_le_add_right (abs_sub_le (J.steppedInducedGraphCount3 G Q)
        (J.steppedInducedGraphCount3 G P) (J.coarseInducedGraphEstimate3 G P)) _)
  have hslack : 0 ≤ F #P.parts * (Fintype.card V : ℝ) ^ 3 := by positivity
  linarith

end SimpleGraph
