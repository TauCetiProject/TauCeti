/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import TauCeti.Combinatorics.SimpleGraph.Density
public import TauCeti.Order.Partition.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import TauCeti.Combinatorics.Regularity.Graph.Counting
import TauCeti.Data.Fintype.BigOperators
import TauCeti.Order.Partition.Finpartition

/-!
# Labelled induced three-vertex counts and their coarse prediction

For a graph `J` on `Fin 3` and a finite graph `G`, `J.inducedGraphCount3 G` counts the labelled
induced copies of `J` in `G`: the injective maps `g : Fin 3 → V` with
`J.Adj i j ↔ G.Adj (g i) (g j)` for all `i, j`. Nonedges of `J` must go to nonedges of `G`, and
there is no division by automorphisms of `J`. This is the number of graph embeddings `J ↪g G`.

Given a partition `P` of the vertices, `J.coarseInducedGraphEstimate3 G P` predicts this count from
the edge densities between parts. Each assignment `φ` of the three vertices of `J` to three
distinct parts contributes the volume `∏ i, #(φ i)` times, for each pair `i < j`, the edge density
`d(φ i, φ j)` if `J.Adj i j` and the nonedge density `1 - d(φ i, φ j)` otherwise. Assignments with
a repeated part are not predicted.

The counting lemma for a regular partition compares the two part by part. The actual count splits
the same way: the induced copies with vertices in three distinct parts are counted separately for
each assignment, and at most `3 * m * (card V) ^ 2` induced copies meet some part twice when all
parts have size at most `m`.

For a `τ`-uniform equipartition, the coarse prediction counts the induced copies with vertices in
three distinct parts up to an error of `15 τ (card V) ^ 3`. An assignment whose three pairs of
parts are `τ`-uniform contributes an error of at most `3 τ` times its volume, by the counting
lemma for three cells. Each other assignment contributes an error of at most its volume, and
Mathlib's `Finpartition.IsEquipartition.sum_nonUniforms_lt` bounds the total volume of these by
`3 * 4 τ (card V) ^ 3`, one term for each of the three pairs that may fail to be uniform.

## Main definitions

* `SimpleGraph.inducedGraphCount3 J G`: the number of labelled induced copies of `J` in `G`.
* `SimpleGraph.coarseInducedGraphEstimate3 J G P`: its prediction from the densities of `P`.

## Main results

* `SimpleGraph.inducedGraphCount3_eq_card_embedding`: the count is the number of embeddings
  `J ↪g G`.
* `SimpleGraph.inducedGraphCount3_eq_sum`: the count splits along the parts containing the three
  vertices.
* `SimpleGraph.sum_card_induced_le_inducedGraphCount3` and
  `SimpleGraph.inducedGraphCount3_le_sum_card_induced_add`: the induced copies with vertices in
  three distinct parts account for all but at most `3 * m * (card V) ^ 2` induced copies.
* `SimpleGraph.abs_sum_card_induced_sub_coarseInducedGraphEstimate3_le`: for a `τ`-uniform
  equipartition, the coarse prediction counts the induced copies with vertices in three distinct
  parts up to an error of `15 τ (card V) ^ 3`.
* `SimpleGraph.inducedGraphCount3_le_coarseInducedGraphEstimate3_add` and
  `SimpleGraph.coarseInducedGraphEstimate3_sub_le_inducedGraphCount3`: the induced counting lemma
  for a `τ`-uniform equipartition whose parts have at most `m` vertices.

## References

* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 2 (the graph regularity method: the graph counting lemma and strong regularity).
* A comparable repeated-cell bound, for real weights dominated by the volume of cell triples, is
  `sum_nontransversal_weight_le` in `RegularityLemmata/Relational/DiagonalGate.lean` of
  `cameronfreer/regularity-lemmata` at commit `315ef979f55f31cc43cd791302519d9a34cc2dc0`.
-/

public section

open Finset
open Function (Injective)

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of labelled induced copies of a graph `J` on `Fin 3` in `G`: the injective maps
`g : Fin 3 → V` such that `g i` and `g j` are adjacent in `G` exactly when `i` and `j` are adjacent
in `J`. Nonedges of `J` must go to nonedges of `G`, and there is no division by automorphisms
of `J`. -/
def inducedGraphCount3 : ℕ :=
  #{g : Fin 3 → V | Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)}

theorem inducedGraphCount3_def : J.inducedGraphCount3 G =
    #{g : Fin 3 → V | Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} := (rfl)

/-- The labelled induced copies of `J` in `G` are the graph embeddings `J ↪g G`. -/
theorem inducedGraphCount3_eq_card_embedding :
    J.inducedGraphCount3 G = Fintype.card (J ↪g G) := by
  rw [inducedGraphCount3_def, ← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun g := ⟨⟨g.1, g.2.1⟩, fun {i j} ↦ (g.2.2 i j).symm⟩
      invFun f := ⟨f, f.injective, fun _ _ ↦ f.map_adj_iff.symm⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- Splitting the labelled induced copies of `J` along the parts of `P` containing the images of
the three vertices. -/
theorem inducedGraphCount3_eq_sum (P : Finpartition (univ : Finset V)) :
    J.inducedGraphCount3 G = ∑ φ : Fin 3 → P.parts,
      #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
        Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} := by
  rw [P.sum_card_filter_piFinset_parts, Fintype.piFinset_univ, inducedGraphCount3_def]

/-- For an assignment `φ` of the vertices of `J` to distinct parts, the maps `g` with `g i ∈ φ i`
are automatically injective. -/
private theorem card_filter_injective_and_eq {P : Finpartition (univ : Finset V)}
    {φ : Fin 3 → P.parts} (hφ : Injective φ) :
    #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
        Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} =
      #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) | ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} :=
  congrArg card <| filter_congr fun _ hg ↦
    and_iff_right (P.injective_of_mem_piFinset_parts hφ hg)

/-- Summing, over the assignments `φ` of the vertices of `J` to three distinct parts of `P`, the
induced copies of `J` in the box of `φ` gives at most `J.inducedGraphCount3 G`. -/
theorem sum_card_induced_le_inducedGraphCount3 (P : Finpartition (univ : Finset V)) :
    ∑ φ : Fin 3 → P.parts with Injective φ,
        #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) | ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} ≤
      J.inducedGraphCount3 G := by
  rw [J.inducedGraphCount3_eq_sum G P, ← sum_filter_add_sum_filter_not univ fun φ ↦ Injective φ]
  refine le_of_eq_of_le (sum_congr rfl fun φ hφ ↦ ?_) le_self_add
  exact (card_filter_injective_and_eq J G (mem_filter.1 hφ).2).symm

/-- **Repeated-cell bound.** If every part of `P` has at most `m` vertices, then all but at most
`3 * m * (card V) ^ 2` labelled induced copies of `J` have their three vertices in three distinct
parts of `P`. -/
theorem inducedGraphCount3_le_sum_card_induced_add (P : Finpartition (univ : Finset V)) {m : ℕ}
    (hm : ∀ A ∈ P.parts, #A ≤ m) :
    J.inducedGraphCount3 G ≤ ∑ φ : Fin 3 → P.parts with Injective φ,
        #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) | ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} +
      3 * m * Fintype.card V ^ 2 := by
  rw [J.inducedGraphCount3_eq_sum G P, ← sum_filter_add_sum_filter_not univ fun φ ↦ Injective φ]
  refine add_le_add (le_of_eq (sum_congr rfl fun φ hφ ↦
    card_filter_injective_and_eq J G (mem_filter.1 hφ).2)) ?_
  -- An induced copy whose vertices meet some part twice lies in the box of a non-injective
  -- assignment, and these boxes are small.
  calc ∑ φ : Fin 3 → P.parts with ¬Injective φ,
        #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
          Injective g ∧ ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)}
      ≤ ∑ φ : Fin 3 → P.parts with ¬Injective φ, ∏ i, #(φ i : Finset V) :=
        sum_le_sum fun φ _ ↦ (card_filter_le _ _).trans_eq (Fintype.card_piFinset _)
    _ ≤ 3 * m * Fintype.card V ^ 2 := by
        simpa using P.sum_prod_card_of_not_injective_le_of_card_le (ι := Fin 3) hm

/-- The coarse prediction of `J.inducedGraphCount3 G` from a partition `P` of the vertices. Each
assignment `φ` of the vertices of `J` to three distinct parts of `P` contributes the volume
`∏ i, #(φ i)` times, for each pair `i < j`, the edge density `d(φ i, φ j)` if `J.Adj i j` and the
nonedge density `1 - d(φ i, φ j)` otherwise (`SimpleGraph.patternDensity`). -/
noncomputable def coarseInducedGraphEstimate3 (P : Finpartition (univ : Finset V)) : ℝ :=
  ∑ φ : Fin 3 → P.parts with Injective φ, (∏ i, (#(φ i : Finset V) : ℝ)) *
    ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2}, G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2)

theorem coarseInducedGraphEstimate3_def (P : Finpartition (univ : Finset V)) :
    J.coarseInducedGraphEstimate3 G P =
      ∑ φ : Fin 3 → P.parts with Injective φ, (∏ i, (#(φ i : Finset V) : ℝ)) *
        ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
          G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2) := (rfl)

/-- The coarse prediction is nonnegative: edge and nonedge densities lie in `[0, 1]`. -/
theorem coarseInducedGraphEstimate3_nonneg (P : Finpartition (univ : Finset V)) :
    0 ≤ J.coarseInducedGraphEstimate3 G P := by
  rw [coarseInducedGraphEstimate3_def]
  exact sum_nonneg fun φ _ ↦ mul_nonneg (by positivity)
    (prod_nonneg fun p _ ↦ G.patternDensity_nonneg _ _ _)

/-- For an assignment `φ` of the vertices of `J` to parts of `P`, the induced copies of `J` in the
box of `φ` number at most the volume `∏ i, #(φ i)` of the box. -/
private lemma card_induced_le_prod_card (P : Finpartition (univ : Finset V)) (φ : Fin 3 → P.parts) :
    (#{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) | ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} :
      ℝ) ≤ ∏ i, (#(φ i : Finset V) : ℝ) := by
  rw [← Nat.cast_prod, Nat.cast_le, ← Fintype.card_piFinset]
  exact card_filter_le _ _

/-- In a `τ`-uniform equipartition, at most `4 τ (card V) ^ 2` ordered pairs of vertices lie in a
pair of parts that is not `τ`-uniform. -/
private lemma sum_sum_nonUniforms_le {Q : Finpartition (univ : Finset V)}
    (hQ : Q.IsEquipartition) {τ : ℝ} (hτ : 0 < τ) (hQG : Q.IsUniform G τ) :
    ∑ x, ∑ y, (if (Q.part x, Q.part y) ∈ Q.nonUniforms G τ then 1 else 0 : ℝ) ≤
      4 * τ * Fintype.card V ^ 2 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  set T := (Q.nonUniforms G τ).biUnion fun (U, W) ↦ U ×ˢ W
  calc _ ≤ ∑ x, ∑ y, (if (x, y) ∈ T then 1 else 0 : ℝ) := by
        refine sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ ?_
        split_ifs with h h'
        · exact le_rfl
        · exact absurd (mem_biUnion.2 ⟨_, h, mem_product.2
            ⟨Q.mem_part (mem_univ x), Q.mem_part (mem_univ y)⟩⟩) h'
        · exact zero_le_one
        · exact le_rfl
    _ = #T := by
        rw [← Fintype.sum_prod_type' (f := fun x y ↦ (if (x, y) ∈ T then 1 else 0 : ℝ)),
          sum_boole]
        simp
    _ ≤ 4 * τ * Fintype.card V ^ 2 := by
        simpa using (hQ.sum_nonUniforms_lt univ_nonempty hτ hQG).le

/-- For an assignment `φ` of the vertices of `J` to three distinct parts of a partition `Q`, the
number of induced copies of `J` in the box of `φ` differs from its predicted count by at most
`3 τ` times the volume of the box if the three pairs of parts are `τ`-uniform, and by at most the
volume otherwise. Either way, the error is at most `3 τ` times the volume plus the volume once for
each pair of parts that is not `τ`-uniform. -/
private lemma abs_card_induced_sub_le {Q : Finpartition (univ : Finset V)} {τ : ℝ} (hτ : 0 ≤ τ)
    {φ : Fin 3 → Q.parts} (hφ : Injective φ) :
    |(#{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
        ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} : ℝ) -
      (∏ i, (#(φ i : Finset V) : ℝ)) * ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2)| ≤
      3 * τ * ∏ i, (#(φ i : Finset V) : ℝ) + ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
        if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ Q.nonUniforms G τ then
          ∏ i, (#(φ i : Finset V) : ℝ) else 0 := by
  have hvol₀ : 0 ≤ ∏ i, (#(φ i : Finset V) : ℝ) := by positivity
  have hterm₀ (p : {p : Fin 3 × Fin 3 // p.1 < p.2}) :
      0 ≤ if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ Q.nonUniforms G τ then
        ∏ i, (#(φ i : Finset V) : ℝ) else 0 := by
    split_ifs
    · exact hvol₀
    · exact le_rfl
  by_cases hgood : ∀ i j, i < j → G.IsUniform τ (φ i : Finset V) (φ j)
  · exact (abs_card_induced_fin_three_sub_le J hgood).trans
      (le_add_of_nonneg_right (sum_nonneg fun p _ ↦ hterm₀ p))
  simp only [not_forall, exists_prop] at hgood
  obtain ⟨i, j, hij, hnot⟩ := hgood
  have hmem : ((φ i : Finset V), (φ j : Finset V)) ∈ Q.nonUniforms G τ :=
    (Q.mk_mem_nonUniforms G).2 ⟨(φ i).2, (φ j).2, Subtype.coe_injective.ne (hφ.ne hij.ne), hnot⟩
  have hbad : ∏ i, (#(φ i : Finset V) : ℝ) ≤ ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ Q.nonUniforms G τ then
        ∏ i, (#(φ i : Finset V) : ℝ) else 0 :=
    le_of_eq_of_le (ite_eq_left hmem).symm
      (single_le_sum (fun p _ ↦ hterm₀ p) (mem_univ ⟨(i, j), hij⟩))
  have hpred₀ : 0 ≤ ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      (G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2) : ℝ) :=
    prod_nonneg fun p _ ↦ G.patternDensity_nonneg _ _ _
  have hpred₁ : ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      (G.patternDensity (J.Adj p.1.1 p.1.2) (φ p.1.1) (φ p.1.2) : ℝ) ≤ 1 :=
    prod_le_one₀ (fun p _ ↦ G.patternDensity_nonneg _ _ _) fun p _ ↦ G.patternDensity_le_one _ _ _
  -- Both the count and the prediction lie between `0` and the volume.
  have hcount := card_induced_le_prod_card J G Q φ
  have hpred := mul_le_of_le_one_right hvol₀ hpred₁
  have hτvol : 0 ≤ 3 * τ * ∏ i, (#(φ i : Finset V) : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith [mul_nonneg hvol₀ hpred₀]

/-- For a pair `p` of coordinates and a `τ`-uniform equipartition `Q`, the assignments sending `p`
to a pair of parts that is not `τ`-uniform have total volume at most `4 τ (card V) ^ 3`. -/
private lemma sum_prod_card_nonUniforms_le {Q : Finpartition (univ : Finset V)}
    (hQ : Q.IsEquipartition) {τ : ℝ} (hτ : 0 < τ) (hQG : Q.IsUniform G τ)
    (p : {p : Fin 3 × Fin 3 // p.1 < p.2}) :
    ∑ φ : Fin 3 → Q.parts,
        (if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ Q.nonUniforms G τ then
          ∏ i, (#(φ i : Finset V) : ℝ) else 0) ≤
      4 * τ * Fintype.card V ^ 3 := by
  have h₁ := Q.sum_piFinset_apply_part (ι := Fin 3) fun A ↦
    (if (A p.1.1, A p.1.2) ∈ Q.nonUniforms G τ then 1 else 0 : ℝ)
  have h₂ := Fintype.sum_piFinset_apply_apply (ne_of_lt p.2) (fun _ ↦ (univ : Finset V))
    fun x y ↦ (if (Q.part x, Q.part y) ∈ Q.nonUniforms G τ then 1 else 0 : ℝ)
  have h₃ : ∏ k ∈ univ \ {p.1.1, p.1.2}, #(univ : Finset V) = Fintype.card V := by
    simp [card_sdiff, ne_of_lt p.2]
  rw [h₃, nsmul_eq_mul] at h₂
  rw [Fintype.piFinset_univ] at h₁ h₂
  calc _ = ∑ φ : Fin 3 → Q.parts, (∏ i, #(φ i : Finset V)) •
        (if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ Q.nonUniforms G τ then 1 else 0 :
          ℝ) := by
        refine sum_congr rfl fun φ _ ↦ ?_
        split_ifs <;> simp
    _ = Fintype.card V *
        ∑ x, ∑ y, (if (Q.part x, Q.part y) ∈ Q.nonUniforms G τ then 1 else 0 : ℝ) := by
        rw [← h₁, h₂]
    _ ≤ Fintype.card V * (4 * τ * Fintype.card V ^ 2) := by
        gcongr
        exact sum_sum_nonUniforms_le G hQ hτ hQG
    _ = 4 * τ * Fintype.card V ^ 3 := by ring

/-- **Induced counting lemma for a uniform equipartition, transversal part.** If `Q` is a
`τ`-uniform equipartition with `τ > 0`, then summing, over the assignments `φ` of the vertices of
`J` to three distinct parts of `Q`, the induced copies of `J` in the box of `φ` gives the coarse
prediction `J.coarseInducedGraphEstimate3 G Q` up to an error of at most `15 τ (card V) ^ 3`. -/
theorem abs_sum_card_induced_sub_coarseInducedGraphEstimate3_le
    {Q : Finpartition (univ : Finset V)} (hQ : Q.IsEquipartition) {τ : ℝ} (hτ : 0 < τ)
    (hQG : Q.IsUniform G τ) :
    |(∑ φ : Fin 3 → Q.parts with Injective φ,
        #{g ∈ Fintype.piFinset (fun i ↦ (φ i : Finset V)) |
          ∀ i j, J.Adj i j ↔ G.Adj (g i) (g j)} : ℝ) - J.coarseInducedGraphEstimate3 G Q| ≤
      15 * τ * Fintype.card V ^ 3 := by
  -- The volumes of all assignments add up to `(card V) ^ 3`.
  have hvol : ∑ φ : Fin 3 → Q.parts, ∏ i, (#(φ i : Finset V) : ℝ) = Fintype.card V ^ 3 := by
    have := Q.sum_piFinset_apply_part (ι := Fin 3) fun _ ↦ (1 : ℝ)
    simp only [Fintype.piFinset_univ, sum_const, card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_pi, prod_const, Fintype.card_fin] at this
    exact_mod_cast this.symm
  -- The error at an assignment is at most `3 τ` times its volume plus its volume once for each
  -- of its pairs of parts that is not uniform, and the latter add up to `12 τ (card V) ^ 3`.
  have hbad : ∑ φ : Fin 3 → Q.parts, ∑ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      (if ((φ p.1.1 : Finset V), (φ p.1.2 : Finset V)) ∈ Q.nonUniforms G τ then
        ∏ i, (#(φ i : Finset V) : ℝ) else 0) ≤ 12 * τ * Fintype.card V ^ 3 := by
    have hpairs : Fintype.card {p : Fin 3 × Fin 3 // p.1 < p.2} = 3 := by decide
    rw [sum_comm]
    refine (sum_le_sum fun p _ ↦ sum_prod_card_nonUniforms_le G hQ hτ hQG p).trans_eq ?_
    rw [sum_const, card_univ, hpairs, nsmul_eq_mul]
    ring
  rw [coarseInducedGraphEstimate3_def, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans <| (sum_le_sum fun φ hφ ↦
    abs_card_induced_sub_le J G hτ.le (mem_filter.1 hφ).2).trans <|
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun φ _ _ ↦ add_nonneg (by positivity)
      (sum_nonneg fun p _ ↦ by split_ifs <;> positivity)).trans ?_
  rw [sum_add_distrib, ← mul_sum, hvol]
  linarith

/-- **Induced counting lemma for a uniform equipartition, upper bound.** If `Q` is a `τ`-uniform
equipartition with `τ > 0` whose parts have at most `m` vertices, then `J.inducedGraphCount3 G`
exceeds the coarse prediction from `Q` by at most `15 τ (card V) ^ 3 + 3 m (card V) ^ 2`. -/
theorem inducedGraphCount3_le_coarseInducedGraphEstimate3_add
    {Q : Finpartition (univ : Finset V)} (hQ : Q.IsEquipartition) {τ : ℝ} (hτ : 0 < τ)
    (hQG : Q.IsUniform G τ) {m : ℕ} (hm : ∀ A ∈ Q.parts, #A ≤ m) :
    (J.inducedGraphCount3 G : ℝ) ≤ J.coarseInducedGraphEstimate3 G Q +
      15 * τ * Fintype.card V ^ 3 + 3 * m * Fintype.card V ^ 2 := by
  have h₁ : (J.inducedGraphCount3 G : ℝ) ≤ _ := Nat.cast_le.2
    (J.inducedGraphCount3_le_sum_card_induced_add G Q hm)
  have h₂ := (abs_le.1 (J.abs_sum_card_induced_sub_coarseInducedGraphEstimate3_le G hQ hτ hQG)).2
  push_cast at h₁
  linarith

/-- **Induced counting lemma for a uniform equipartition, lower bound.** If `Q` is a `τ`-uniform
equipartition with `τ > 0`, then `J.inducedGraphCount3 G` falls short of the coarse prediction
from `Q` by at most `15 τ (card V) ^ 3`. -/
theorem coarseInducedGraphEstimate3_sub_le_inducedGraphCount3
    {Q : Finpartition (univ : Finset V)} (hQ : Q.IsEquipartition) {τ : ℝ} (hτ : 0 < τ)
    (hQG : Q.IsUniform G τ) :
    J.coarseInducedGraphEstimate3 G Q - 15 * τ * Fintype.card V ^ 3 ≤ J.inducedGraphCount3 G := by
  have h₁ : _ ≤ (J.inducedGraphCount3 G : ℝ) := Nat.cast_le.2
    (J.sum_card_induced_le_inducedGraphCount3 G Q)
  have h₂ := (abs_le.1 (J.abs_sum_card_induced_sub_coarseInducedGraphEstimate3_le G hQ hτ hQG)).1
  push_cast at h₁
  linarith

end SimpleGraph
