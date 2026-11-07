/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.SupportStability
import TauCeti.Data.Fintype.CardEmbedding
import Mathlib.Tactic.Positivity

/-!
# Top regularity after moving vertices between cells

Rebalancing a vertex partition need not refine it. A correspondence between the old and new
cells nevertheless transports polyad data, keeping the three pair colors unchanged. If every
vertex outside a set `B` stays in its corresponding cell, at most `3 |B| |V|²` injective triples
change their polyad. This bound has no factor depending on the number of cells or pair colors.

For an injective cell correspondence, the support-stability theorem then controls the total
support of the new irregular polyads. The pair coloring is unchanged, the vertex cells may
repeat, and neither partition needs to be equitable. In particular this accounts for the
top-regularity error incurred when rebalancing cells after removing padding vertices.

## Main results

* `Polyad3.repartition`: transport polyad data along a map of vertex cells.
* `Polyad3.card_filter_ofTriple_ne_repartition_le`: the moved-triple bound.
* `Colored3Graph.sum_card_support_not_isTopRegularOverPolyad_le_of_repartition`:
  the exceptional-support bound after repartitioning.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the padding-and-rebalancing setting.
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V]
  {S T U : PairSkeleton3 κ V}

namespace Polyad3

/-- Transport the three vertex cells along `f`, leaving the pair colors unchanged. No
refinement relation between the partitions is required. -/
def repartition (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) : Polyad3 T :=
  ofData (f ⟨P.c₀, P.hc₀⟩) (f ⟨P.c₁, P.hc₁⟩) (f ⟨P.c₂, P.hc₂⟩)
    (f ⟨P.c₀, P.hc₀⟩).property (f ⟨P.c₁, P.hc₁⟩).property (f ⟨P.c₂, P.hc₂⟩).property
    P.color₀₁ P.color₀₂ P.color₁₂

/-- The role-zero cell is transported by the cell map. -/
@[simp]
theorem repartition_c₀ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.repartition f).c₀ = (f ⟨P.c₀, P.hc₀⟩).val := by simp [repartition]

/-- The role-one cell is transported by the cell map. -/
@[simp]
theorem repartition_c₁ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.repartition f).c₁ = (f ⟨P.c₁, P.hc₁⟩).val := by simp [repartition]

/-- The role-two cell is transported by the cell map. -/
@[simp]
theorem repartition_c₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.repartition f).c₂ = (f ⟨P.c₂, P.hc₂⟩).val := by simp [repartition]

/-- Repartitioning preserves the color on roles zero and one. -/
@[simp]
theorem repartition_color₀₁ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.repartition f).color₀₁ = P.color₀₁ := by simp [repartition]

/-- Repartitioning preserves the color on roles zero and two. -/
@[simp]
theorem repartition_color₀₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.repartition f).color₀₂ = P.color₀₂ := by simp [repartition]

/-- Repartitioning preserves the color on roles one and two. -/
@[simp]
theorem repartition_color₁₂ (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) :
    (P.repartition f).color₁₂ = P.color₁₂ := by simp [repartition]

/-- The identity cell map leaves a polyad unchanged. -/
@[simp]
theorem repartition_id (P : Polyad3 S) : P.repartition id = P := by
  ext <;> simp

/-- Successive changes of vertex cells compose. -/
@[simp]
theorem repartition_repartition (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts)
    (g : T.vertexPart.parts → U.vertexPart.parts) :
    (P.repartition f).repartition g = P.repartition (g ∘ f) := by
  ext <;> simp

/-- An injective cell correspondence determines the original polyad from its transport. -/
theorem repartition_injective {f : S.vertexPart.parts → T.vertexPart.parts}
    (hf : Function.Injective f) : Function.Injective fun P : Polyad3 S ↦ P.repartition f := by
  intro P Q h
  have hcell (A B : S.vertexPart.parts) (h : (f A).val = (f B).val) : A.val = B.val :=
    congrArg Subtype.val (hf (Subtype.ext h))
  exact ext_data
    (hcell ⟨P.c₀, P.hc₀⟩ ⟨Q.c₀, Q.hc₀⟩ (by simpa using congrArg c₀ h))
    (hcell ⟨P.c₁, P.hc₁⟩ ⟨Q.c₁, Q.hc₁⟩ (by simpa using congrArg c₁ h))
    (hcell ⟨P.c₂, P.hc₂⟩ ⟨Q.c₂, Q.hc₂⟩ (by simpa using congrArg c₂ h))
    (by simpa using congrArg color₀₁ h) (by simpa using congrArg color₀₂ h)
    (by simpa using congrArg color₁₂ h)

/-- A triple keeps its polyad when each coordinate lies in the corresponding new cell and the
pair coloring is unchanged. -/
theorem repartition_ofTriple (f : S.vertexPart.parts → T.vertexPart.parts)
    (hcolor : ∀ p, T.pairColors.color p = S.pairColors.color p)
    (x : {x : Fin 3 → V // Function.Injective x})
    (hcell : ∀ A (hA : A ∈ S.vertexPart.parts), ∀ i, x.1 i ∈ A → x.1 i ∈ (f ⟨A, hA⟩).val) :
    (ofTriple S x).repartition f = ofTriple T x := by
  obtain ⟨h₀, h₁, h₂, -⟩ := ((ofTriple S x).mem_support x).1 (mem_support_ofTriple x)
  apply mem_support_iff_eq_ofTriple.1
  apply (mem_support _ x).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [repartition_c₀] using hcell _ (ofTriple S x).hc₀ 0 h₀
  · simpa only [repartition_c₁] using hcell _ (ofTriple S x).hc₁ 1 h₁
  · simpa only [repartition_c₂] using hcell _ (ofTriple S x).hc₂ 2 h₂
  · simpa only [repartition_color₀₁, ofTriple_color₀₁] using
      (T.pairColors.color_coordPair_eq_iff _).1 (hcolor (coordPair x 0 1 (by decide)))
  · simpa only [repartition_color₀₂, ofTriple_color₀₂] using
      (T.pairColors.color_coordPair_eq_iff _).1 (hcolor (coordPair x 0 2 (by decide)))
  · simpa only [repartition_color₁₂, ofTriple_color₁₂] using
      (T.pairColors.color_coordPair_eq_iff _).1 (hcolor (coordPair x 1 2 (by decide)))

/-- Moving vertices in `B` between corresponding cells changes the polyad of at most
`3 |B| |V|²` injective triples. The cell map need not be injective for this bound. -/
theorem card_filter_ofTriple_ne_repartition_le [DecidableEq κ]
    (f : S.vertexPart.parts → T.vertexPart.parts)
    (hcolor : ∀ p, T.pairColors.color p = S.pairColors.color p) (B : Finset V)
    (hcell : ∀ A (hA : A ∈ S.vertexPart.parts), A \ B ⊆ f ⟨A, hA⟩) :
    #{x | ofTriple T x ≠ (ofTriple S x).repartition f} ≤
      3 * #B * Fintype.card V ^ 2 := by
  refine (card_le_card ?_).trans (card_filter_injective_exists_mem_le B)
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  by_contra! h
  exact hx (repartition_ofTriple f hcolor x
    (fun A hA i hi ↦ hcell A hA (mem_sdiff.2 ⟨hi, h i⟩))).symm

end Polyad3

namespace Colored3Graph

variable {κ₃ : Type*} [DecidableEq κ₃] [Fintype κ]
  {H : Colored3Graph κ₃ V} {δ ε η : ℝ} {r : ℕ}

open Classical in
/-- **Top regularity after rebalancing vertex cells.** Suppose that the pair coloring is
unchanged, corresponding cells are distinct, and all vertices outside `B` stay in their
corresponding cell. If `δ + 2η + η / ε ≤ ε`, the support of the new polyads that fail
`(ε, r)`-regularity is at most the old `(δ, r)`-exceptional support plus
`(1 + 2 / η) 3 |B| |V|²`. All supports count ordered injective triples. -/
theorem sum_card_support_not_isTopRegularOverPolyad_le_of_repartition
    {f : S.vertexPart.parts → T.vertexPart.parts} (hf : Function.Injective f)
    (hcolor : ∀ p, T.pairColors.color p = S.pairColors.color p) (B : Finset V)
    (hcell : ∀ A (hA : A ∈ S.vertexPart.parts), A \ B ⊆ f ⟨A, hA⟩)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    (∑ Q : Polyad3 T with ¬H.IsTopRegularOverPolyad Q ε r, (#Q.support : ℝ)) ≤
      (∑ P : Polyad3 S with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
        (1 + 2 / η) * (3 * #B * Fintype.card V ^ 2 : ℕ) := by
  classical
  refine (sum_card_support_not_isTopRegularOverPolyad_le_of_injective
    (Polyad3.repartition_injective hf) hε hη hbudget).trans ?_
  have hm : (#{x | Polyad3.ofTriple T x ≠ (Polyad3.ofTriple S x).repartition f} : ℝ) ≤
      (3 * #B * Fintype.card V ^ 2 : ℕ) := by
    exact_mod_cast Polyad3.card_filter_ofTriple_ne_repartition_le f hcolor B hcell
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hm
    (by positivity : (0 : ℝ) ≤ 1 + 2 / η))

end Colored3Graph

end TauCeti
