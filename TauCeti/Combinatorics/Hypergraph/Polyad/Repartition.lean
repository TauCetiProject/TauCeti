/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic
import TauCeti.Data.Fintype.CardEmbedding
import Mathlib.Tactic.Linarith

/-!
# Polyads after moving vertex cells

A matching of the cells of two lower skeletons, together with a map of their pair palettes,
assigns a new polyad to each old polyad. No containment of matched cells is required. A triple
keeps its assigned polyad unless one of its vertices leaves its matched cell or one of its
three pair colors changes. Thus moving `b` vertices and recoloring `e` ordered pairs moves at
most `3 b |V|² + 3 e |V|` injective triples, independently of the number of cells and colors.

This is the support bookkeeping needed to preserve top regularity when a vertex partition is
rebalanced. All triples are role-ordered and injective; repeated cells are allowed.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the padding-and-rebalancing setting.
-/

public section

open Finset

namespace TauCeti.Polyad3

variable {κ κ' V : Type*} [Fintype V] [DecidableEq V]
  {S : PairSkeleton3 κ V} {T : PairSkeleton3 κ' V}

/-- Replace the three cells by their matched cells and map the three pair colors.
This is a map of polyad data, not an assertion of support containment. -/
def mapData (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ') :
    Polyad3 T :=
  ofData (f ⟨P.c₀, P.hc₀⟩) (f ⟨P.c₁, P.hc₁⟩) (f ⟨P.c₂, P.hc₂⟩)
    (f ⟨P.c₀, P.hc₀⟩).property (f ⟨P.c₁, P.hc₁⟩).property (f ⟨P.c₂, P.hc₂⟩).property
    (g P.color₀₁) (g P.color₀₂) (g P.color₁₂)

variable (P : Polyad3 S) (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')

/-- The new role-zero cell is the matched old cell. -/
@[simp]
theorem mapData_c₀ : (P.mapData f g).c₀ = (f ⟨P.c₀, P.hc₀⟩).val := by simp [mapData]

/-- The new role-one cell is the matched old cell. -/
@[simp]
theorem mapData_c₁ : (P.mapData f g).c₁ = (f ⟨P.c₁, P.hc₁⟩).val := by simp [mapData]

/-- The new role-two cell is the matched old cell. -/
@[simp]
theorem mapData_c₂ : (P.mapData f g).c₂ = (f ⟨P.c₂, P.hc₂⟩).val := by simp [mapData]

/-- The color on roles zero and one is mapped by the palette map. -/
@[simp]
theorem mapData_color₀₁ : (P.mapData f g).color₀₁ = g P.color₀₁ := by simp [mapData]

/-- The color on roles zero and two is mapped by the palette map. -/
@[simp]
theorem mapData_color₀₂ : (P.mapData f g).color₀₂ = g P.color₀₂ := by simp [mapData]

/-- The color on roles one and two is mapped by the palette map. -/
@[simp]
theorem mapData_color₁₂ : (P.mapData f g).color₁₂ = g P.color₁₂ := by simp [mapData]

variable {P f g}

/-- Injective maps of cells and colors give an injective map of polyads. -/
theorem mapData_injective (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective fun P : Polyad3 S ↦ P.mapData f g := by
  intro P Q h
  have hcell {A B : S.vertexPart.parts} (h : (f A).val = (f B).val) : A.val = B.val :=
    congrArg Subtype.val (hf (Subtype.ext h))
  exact ext_data (hcell (by simpa using congrArg c₀ h))
    (hcell (by simpa using congrArg c₁ h)) (hcell (by simpa using congrArg c₂ h))
    (hg (by simpa using congrArg color₀₁ h)) (hg (by simpa using congrArg color₀₂ h))
    (hg (by simpa using congrArg color₁₂ h))

/-- A triple retains its polyad if its vertices remain in their matched cells and its three
pair colors are mapped as prescribed. -/
theorem mapData_ofTriple_of_mem (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')
    (x : {x : Fin 3 → V // Function.Injective x})
    (hcell : ∀ i, x.1 i ∈ (f ⟨S.vertexPart.part (x.1 i), S.vertexPart.part_mem.2 (mem_univ _)⟩).val)
    (h₀₁ : T.pairColors.color (coordPair x 0 1 (by decide)) =
      g (S.pairColors.color (coordPair x 0 1 (by decide))))
    (h₀₂ : T.pairColors.color (coordPair x 0 2 (by decide)) =
      g (S.pairColors.color (coordPair x 0 2 (by decide))))
    (h₁₂ : T.pairColors.color (coordPair x 1 2 (by decide)) =
      g (S.pairColors.color (coordPair x 1 2 (by decide)))) :
    (ofTriple S x).mapData f g = ofTriple T x := by
  apply mem_support_iff_eq_ofTriple.1
  apply (mem_support _ x).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hcell 0
  · simpa using hcell 1
  · simpa using hcell 2
  · exact (T.pairColors.color_coordPair_eq_iff _).1 (by simpa using h₀₁)
  · exact (T.pairColors.color_coordPair_eq_iff _).1 (by simpa using h₀₂)
  · exact (T.pairColors.color_coordPair_eq_iff _).1 (by simpa using h₁₂)

/-- Moving `b` vertices out of their matched cells and changing `e` ordered pair colors moves
at most `3 b |V|² + 3 e |V|` injective triples between the matched polyads. -/
theorem card_filter_ofTriple_ne_mapData_ofTriple_le [DecidableEq κ']
    (f : S.vertexPart.parts → T.vertexPart.parts) (g : κ → κ')
    (B : Finset V) (E : Finset {p : V × V // p.1 ≠ p.2})
    (hcell : ∀ v ∉ B,
      v ∈ (f ⟨S.vertexPart.part v, S.vertexPart.part_mem.2 (mem_univ _)⟩).val)
    (hcolor : ∀ p ∉ E, T.pairColors.color p = g (S.pairColors.color p)) :
    #{x | ofTriple T x ≠ (ofTriple S x).mapData f g} ≤
      3 * #B * Fintype.card V ^ 2 + 3 * #E * Fintype.card V := by
  classical
  let A : Finset {x : Fin 3 → V // Function.Injective x} := {x | ∃ i, x.1 i ∈ B}
  let A₀₁ : Finset {x : Fin 3 → V // Function.Injective x} := {x | coordPair x 0 1 (by decide) ∈ E}
  let A₀₂ : Finset {x : Fin 3 → V // Function.Injective x} := {x | coordPair x 0 2 (by decide) ∈ E}
  let A₁₂ : Finset {x : Fin 3 → V // Function.Injective x} := {x | coordPair x 1 2 (by decide) ∈ E}
  have hsub : ({x | ofTriple T x ≠ (ofTriple S x).mapData f g} :
      Finset {x : Fin 3 → V // Function.Injective x}) ⊆ A ∪ (A₀₁ ∪ A₀₂ ∪ A₁₂) := by
    intro x hx
    by_contra h
    simp only [A, A₀₁, A₀₂, A₁₂, mem_union, mem_filter, mem_univ, true_and,
      not_or, not_exists] at h
    exact (mem_filter.1 hx).2 (mapData_ofTriple_of_mem f g x
      (fun i ↦ hcell _ (h.1 i)) (hcolor _ h.2.1.1) (hcolor _ h.2.1.2) (hcolor _ h.2.2)).symm
  have hB := card_filter_injective_exists_mem_le (n := 3) B
  have h₀₁ := card_filter_coordPair_mem_le E (by decide : (0 : Fin 3) ≠ 1) (k := 2) (by decide)
  have h₀₂ := card_filter_coordPair_mem_le E (by decide : (0 : Fin 3) ≠ 2) (k := 1) (by decide)
  have h₁₂ := card_filter_coordPair_mem_le E (by decide : (1 : Fin 3) ≠ 2) (k := 0) (by decide)
  have := (card_le_card hsub).trans (card_union_le _ _)
  have := card_union_le (A₀₁ ∪ A₀₂) A₁₂
  have := card_union_le A₀₁ A₀₂
  dsimp only [A, A₀₁, A₀₂, A₁₂] at *
  norm_num only at hB
  linarith

end TauCeti.Polyad3
