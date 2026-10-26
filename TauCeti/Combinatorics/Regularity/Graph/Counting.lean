/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Data.Fintype.Pi
public import TauCeti.Combinatorics.SimpleGraph.Density
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
import TauCeti.Combinatorics.SimpleGraph.Regularity.Uniform

/-!
# Counting induced three-vertex patterns in uniform triples of cells

If three cells `A 0`, `A 1`, `A 2` of a graph `G` are pairwise `ε`-uniform, then for every graph
`J` on `Fin 3` the number of maps `g` with `g i ∈ A i` that induce `J` (edges of `J` go to edges of
`G` and nonedges to nonedges) is the count predicted by independence,
`|A 0| |A 1| |A 2| ∏_{i < j} d_{ij}`, up to an error `3 ε |A 0| |A 1| |A 2|`. Here `d_{ij}` is the
edge density of `(A i, A j)` when `i` and `j` are adjacent in `J` and the nonedge density
`1 - d(A i, A j)` otherwise. Since nonedges are counted too, this predicts every *induced*
pattern, not only edge-preserving copies.

The argument has two steps.

* A `ε`-uniform pair `(s, t)` has small *rectangle discrepancy*: the number of edges between
  `s' ⊆ s` and `t' ⊆ t` is within `ε |s| |t|` of `d(s, t) |s'| |t'|`. Large rectangles are
  controlled by uniformity itself, and small ones because both counts are then at most
  `|s'| |t'| ≤ ε |s| |t|`. Testing against functions with values in `[0, 1]` instead of
  indicator functions does not increase the discrepancy
  (`SimpleGraph.IsUniform.abs_sum_sum_mul_sub_le`).
* Replacing the three pair indicators by their densities one at a time, every step is a test of
  one pair against two functions with values in `[0, 1]`, summed over the third vertex.

The cells may overlap and need not be distinct; when they are pairwise disjoint, every counted
map is injective. Summed over the triples of distinct parts of a uniform partition, this gives the
contribution of transversal maps in counting lemmas for regular partitions, such as the induced
counting lemma for strong graph regularity.

## Main results

* `SimpleGraph.abs_card_induced_fin_three_sub_le`: the induced counting lemma for pairwise uniform
  triples of cells.

## References

* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 4 (the graph counting lemma).
-/

public section

open Finset

namespace SimpleGraph

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGraph α}
  [DecidableRel G.Adj] {ε : 𝕜} {s t : Finset α}

/-- The indicator that `x` and `y` are adjacent exactly when `e` holds. -/
private def patternWeight (G : SimpleGraph α) [DecidableRel G.Adj] (e : Prop) [Decidable e]
    (x y : α) : 𝕜 :=
  if (e ↔ G.Adj x y) then 1 else 0

private lemma patternWeight_nonneg (e : Prop) [Decidable e] (x y : α) :
    0 ≤ (patternWeight G e x y : 𝕜) := by
  unfold patternWeight; split_ifs <;> norm_num

private lemma patternWeight_le_one (e : Prop) [Decidable e] (x y : α) :
    (patternWeight G e x y : 𝕜) ≤ 1 := by
  unfold patternWeight; split_ifs <;> norm_num

/-- The test-function discrepancy bound, for the indicator of adjacency or of nonadjacency. -/
private lemma IsUniform.abs_sum_sum_mul_patternWeight_sub_le (h : G.IsUniform ε s t) (e : Prop)
    [Decidable e] {f g : α → 𝕜} (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hf₁ : ∀ x ∈ s, f x ≤ 1)
    (hg₀ : ∀ y ∈ t, 0 ≤ g y) (hg₁ : ∀ y ∈ t, g y ≤ 1) :
    |∑ x ∈ s, ∑ y ∈ t, f x * g y * (patternWeight G e x y - patternDensity G e s t)| ≤
      ε * #s * #t := by
  have key := h.abs_sum_sum_mul_sub_le hf₀ hf₁ hg₀ hg₁
  by_cases he : e
  · simpa [patternWeight, he] using key
  · rw [← abs_neg] at key
    convert key using 2
    simp only [← sum_neg_distrib]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
    by_cases hxy : G.Adj x y
    · simp [patternWeight, he, hxy]
      ring
    · simp [patternWeight, he, hxy]

/-- The counting lemma for a triple of cells, with the three pattern conditions explicit. -/
private lemma abs_sum_patternWeight_sub_le (e₀₁ e₀₂ e₁₂ : Prop) [Decidable e₀₁] [Decidable e₀₂]
    [Decidable e₁₂] {s₀ s₁ s₂ : Finset α} (h₀₁ : G.IsUniform ε s₀ s₁)
    (h₀₂ : G.IsUniform ε s₀ s₂) (h₁₂ : G.IsUniform ε s₁ s₂) :
    |∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂,
        (patternWeight G e₀₁ x y : 𝕜) * patternWeight G e₀₂ x z * patternWeight G e₁₂ y z -
      (#s₀ * #s₁ * #s₂ : 𝕜) * (patternDensity G e₀₁ s₀ s₁ * patternDensity G e₀₂ s₀ s₂ *
        patternDensity G e₁₂ s₁ s₂)| ≤ 3 * ε * (#s₀ * #s₁ * #s₂) := by
  set a : α → α → 𝕜 := patternWeight G e₀₁
  set b : α → α → 𝕜 := patternWeight G e₀₂
  set c : α → α → 𝕜 := patternWeight G e₁₂
  set p : 𝕜 := patternDensity G e₀₁ s₀ s₁
  set q : 𝕜 := patternDensity G e₀₂ s₀ s₂
  set r : 𝕜 := patternDensity G e₁₂ s₁ s₂
  have hp₀ : 0 ≤ p := G.patternDensity_nonneg _ _ _
  have hp₁ : p ≤ 1 := G.patternDensity_le_one _ _ _
  have hq₀ : 0 ≤ q := G.patternDensity_nonneg _ _ _
  have hq₁ : q ≤ 1 := G.patternDensity_le_one _ _ _
  have hpq₀ : 0 ≤ p * q := mul_nonneg hp₀ hq₀
  have hpq₁ : p * q ≤ 1 := (mul_le_of_le_one_left hq₀ hp₁).trans hq₁
  have ha₀ := patternWeight_nonneg (G := G) (𝕜 := 𝕜) e₀₁
  have hb₀ := patternWeight_nonneg (G := G) (𝕜 := 𝕜) e₀₂
  have hc₀ := patternWeight_nonneg (G := G) (𝕜 := 𝕜) e₁₂
  have ha₁ := patternWeight_le_one (G := G) (𝕜 := 𝕜) e₀₁
  have hb₁ := patternWeight_le_one (G := G) (𝕜 := 𝕜) e₀₂
  have hc₁ := patternWeight_le_one (G := G) (𝕜 := 𝕜) e₁₂
  -- Replace the three indicators by their densities one at a time: each difference is a test of
  -- one pair against functions with values in `[0, 1]`, summed over the remaining vertex.
  have hsplit : ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, a x y * b x z * c y z -
      (#s₀ * #s₁ * #s₂ : 𝕜) * (p * q * r) =
      ∑ z ∈ s₂, ∑ x ∈ s₀, ∑ y ∈ s₁, b x z * c y z * (a x y - p) +
        p * ∑ y ∈ s₁, ∑ x ∈ s₀, ∑ z ∈ s₂, 1 * c y z * (b x z - q) +
        p * q * ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, 1 * 1 * (c y z - r) := by
    have e₁ : ∑ z ∈ s₂, ∑ x ∈ s₀, ∑ y ∈ s₁, b x z * c y z * (a x y - p) =
        ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, b x z * c y z * (a x y - p) := by
      rw [sum_comm]
      exact sum_congr rfl fun _ _ ↦ sum_comm
    have e₃ : (#s₀ * #s₁ * #s₂ : 𝕜) * (p * q * r) =
        ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, p * q * r := by
      simp only [sum_const, nsmul_eq_mul]
      ring
    rw [e₁, sum_comm (s := s₁), e₃]
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ sum_congr rfl fun z _ ↦ ?_
    ring
  have h₁ : |∑ z ∈ s₂, ∑ x ∈ s₀, ∑ y ∈ s₁, b x z * c y z * (a x y - p)| ≤
      ε * (#s₀ * #s₁ * #s₂) :=
    (abs_sum_le_card_nsmul fun z _ ↦
      h₀₁.abs_sum_sum_mul_patternWeight_sub_le e₀₁ (fun x _ ↦ hb₀ x z) (fun x _ ↦ hb₁ x z)
        (fun y _ ↦ hc₀ y z) (fun y _ ↦ hc₁ y z)).trans_eq (by rw [nsmul_eq_mul]; ring)
  have h₂ : |p * ∑ y ∈ s₁, ∑ x ∈ s₀, ∑ z ∈ s₂, 1 * c y z * (b x z - q)| ≤
      ε * (#s₀ * #s₁ * #s₂) := by
    rw [abs_mul, abs_of_nonneg hp₀]
    refine (mul_le_of_le_one_left (abs_nonneg _) hp₁).trans <|
      (abs_sum_le_card_nsmul fun y _ ↦
        h₀₂.abs_sum_sum_mul_patternWeight_sub_le e₀₂ (fun _ _ ↦ zero_le_one) (fun _ _ ↦ le_rfl)
          (fun z _ ↦ hc₀ y z) (fun z _ ↦ hc₁ y z)).trans_eq (by rw [nsmul_eq_mul]; ring)
  have h₃ : |p * q * ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, 1 * 1 * (c y z - r)| ≤
      ε * (#s₀ * #s₁ * #s₂) := by
    rw [abs_mul, abs_of_nonneg hpq₀]
    refine (mul_le_of_le_one_left (abs_nonneg _) hpq₁).trans <|
      (abs_sum_le_card_nsmul fun x _ ↦
        h₁₂.abs_sum_sum_mul_patternWeight_sub_le e₁₂ (fun _ _ ↦ zero_le_one) (fun _ _ ↦ le_rfl)
          (fun _ _ ↦ zero_le_one) (fun _ _ ↦ le_rfl)).trans_eq (by rw [nsmul_eq_mul]; ring)
  rw [hsplit]
  refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
  linarith

/-- **Induced counting lemma for three cells.** Let `A 0`, `A 1`, `A 2` be pairwise `ε`-uniform
cells of `G`, and `J` a graph on `Fin 3`. Then the number of maps `g` with `g i ∈ A i` such that
`g i` and `g j` are adjacent in `G` exactly when `i` and `j` are adjacent in `J` differs from
`|A 0| |A 1| |A 2|` times the product, over the pairs `i < j`, of the edge density of
`(A i, A j)` (if `i` and `j` are adjacent in `J`) or of its nonedge density `1 - d(A i, A j)`
(otherwise), that is `SimpleGraph.patternDensity`, by at most `3 ε |A 0| |A 1| |A 2|`. -/
theorem abs_card_induced_fin_three_sub_le (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]
    {A : Fin 3 → Finset α} (hA : ∀ i j, i < j → G.IsUniform ε (A i) (A j)) :
    |(#{g ∈ Fintype.piFinset A | ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} : 𝕜) -
        (∏ i, (#(A i) : 𝕜)) * ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          G.patternDensity (J.Adj p.1.1 p.1.2) (A p.1.1) (A p.1.2)| ≤
      3 * ε * ∏ i, (#(A i) : 𝕜) := by
  have hiff (g : Fin 3 → α) : (∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)) ↔
      (J.Adj 0 1 ↔ G.Adj (g 0) (g 1)) ∧ (J.Adj 0 2 ↔ G.Adj (g 0) (g 2)) ∧
        (J.Adj 1 2 ↔ G.Adj (g 1) (g 2)) := by
    refine ⟨fun h ↦ ⟨h 0 1, h 0 2, h 1 2⟩, fun h i j ↦ ?_⟩
    fin_cases i <;> fin_cases j <;> simp [h, J.adj_comm 1 0, J.adj_comm 2 0, J.adj_comm 2 1,
      G.adj_comm (g 1) (g 0), G.adj_comm (g 2) (g 0), G.adj_comm (g 2) (g 1)]
  have hcard : #{g ∈ Fintype.piFinset A | ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} =
      #{q ∈ A 0 ×ˢ A 1 ×ˢ A 2 | (J.Adj 0 1 ↔ G.Adj q.1 q.2.1) ∧
        (J.Adj 0 2 ↔ G.Adj q.1 q.2.2) ∧ (J.Adj 1 2 ↔ G.Adj q.2.1 q.2.2)} := by
    refine card_nbij' (fun g ↦ (g 0, g 1, g 2)) (fun q ↦ ![q.1, q.2.1, q.2.2]) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq, hiff] at hg
      simp [hg.1 0, hg.1 1, hg.1 2, hg.2]
    · rintro ⟨x, y, z⟩ hq
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hq
      simp only [coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq, hiff]
      refine ⟨fun i ↦ ?_, by simpa using hq.2⟩
      fin_cases i <;> simp [hq.1]
    · intro g _
      ext i
      fin_cases i <;> rfl
    · intro q _
      rfl
  have hprod : (∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      (G.patternDensity (J.Adj p.1.1 p.1.2) (A p.1.1) (A p.1.2) : 𝕜)) =
      patternDensity G (J.Adj 0 1) (A 0) (A 1) * patternDensity G (J.Adj 0 2) (A 0) (A 2) *
        patternDensity G (J.Adj 1 2) (A 1) (A 2) := by
    rw [← prod_subtype ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)) (by decide)
      (fun p ↦ (G.patternDensity (J.Adj p.1 p.2) (A p.1) (A p.2) : 𝕜))]
    simp [mul_assoc]
  have hsum : (#{q ∈ A 0 ×ˢ A 1 ×ˢ A 2 | (J.Adj 0 1 ↔ G.Adj q.1 q.2.1) ∧
      (J.Adj 0 2 ↔ G.Adj q.1 q.2.2) ∧ (J.Adj 1 2 ↔ G.Adj q.2.1 q.2.2)} : 𝕜) =
      ∑ x ∈ A 0, ∑ y ∈ A 1, ∑ z ∈ A 2, patternWeight G (J.Adj 0 1) x y *
        patternWeight G (J.Adj 0 2) x z * patternWeight G (J.Adj 1 2) y z := by
    rw [← sum_boole, sum_product]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [sum_product]
    simp only [patternWeight, ite_zero_mul_ite_zero, mul_one, and_assoc]
  rw [hcard, hsum, hprod, Fin.prod_univ_three]
  exact abs_sum_patternWeight_sub_le _ _ _ (hA 0 1 (by decide)) (hA 0 2 (by decide))
    (hA 1 2 (by decide))

end SimpleGraph
