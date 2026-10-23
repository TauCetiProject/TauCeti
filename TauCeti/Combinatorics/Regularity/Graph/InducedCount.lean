/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import TauCeti.Combinatorics.SimpleGraph.Density
public import TauCeti.Order.Partition.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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

end SimpleGraph
