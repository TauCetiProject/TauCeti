/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Map
public import TauCeti.Order.Partition.Finpartition
import Mathlib.Tactic.Linarith

/-!
# Coarse parents of polyads

A refinement of vertex cells and a projection of pair colors assign each fine polyad a coarse
parent. When the projection recovers the original pair coloring, each fine pair graph lies in
the corresponding coarse pair graph. The fine supports with a given parent partition its
support, including when cells repeat. These facts let local slicing estimates be summed over
a refined skeleton without charging the same coarse exceptional support more than once.

The construction also compares two colorings of the pairs on the same vertex cells. A triple
keeps its polyad, up to the color map, whenever its three coordinate pairs keep their colors
(`Polyad3.coarsen_ofTriple_of_color_coordPair`), and an injective color map then sends distinct
polyads to distinct polyads (`Polyad3.coarsen_injective`). Recoloring `|E|` ordered pairs
therefore changes the polyad of at most `3 |E| |V|` triples
(`Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le`).
-/

public section

open Finset

namespace TauCeti.Polyad3

variable {κ κ' V : Type*} [Fintype V] [DecidableEq V]
  {S : PairSkeleton3 κ V} {T : PairSkeleton3 κ' V}

/-- The coarse parent of a fine polyad: replace its cells by their coarse parents and project
its three pair colors. -/
noncomputable def coarsen (P : Polyad3 T) (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ) :
    Polyad3 S :=
  P.map (Finpartition.refinementParent hV) f

@[simp]
theorem coarsen_c₀ (P : Polyad3 T) (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ) :
    (P.coarsen hV f).c₀ = (Finpartition.refinementParent hV ⟨P.c₀, P.hc₀⟩).val := by
  simp [coarsen]

@[simp]
theorem coarsen_c₁ (P : Polyad3 T) (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ) :
    (P.coarsen hV f).c₁ = (Finpartition.refinementParent hV ⟨P.c₁, P.hc₁⟩).val := by
  simp [coarsen]

@[simp]
theorem coarsen_c₂ (P : Polyad3 T) (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ) :
    (P.coarsen hV f).c₂ = (Finpartition.refinementParent hV ⟨P.c₂, P.hc₂⟩).val := by
  simp [coarsen]

@[simp]
theorem coarsen_color₀₁ (P : Polyad3 T) (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ) :
    (P.coarsen hV f).color₀₁ = f P.color₀₁ := by simp [coarsen]

@[simp]
theorem coarsen_color₀₂ (P : Polyad3 T) (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ) :
    (P.coarsen hV f).color₀₂ = f P.color₀₂ := by simp [coarsen]

@[simp]
theorem coarsen_color₁₂ (P : Polyad3 T) (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ) :
    (P.coarsen hV f).color₁₂ = f P.color₁₂ := by simp [coarsen]

/-- If the two skeletons have the same vertex cells, the coarse parent along an injective color
map determines the polyad. -/
theorem coarsen_injective (hV : T.vertexPart = S.vertexPart) {f : κ' → κ}
    (hf : Function.Injective f) : Function.Injective fun P : Polyad3 T ↦ P.coarsen hV.le f := by
  have hcell : ∀ A (hA : A ∈ T.vertexPart.parts),
      (Finpartition.refinementParent hV.le ⟨A, hA⟩).val = A := fun A hA ↦
    congrArg Subtype.val
      ((Finpartition.refinementParent_eq_iff hV.le (A := ⟨A, hV ▸ hA⟩)).2 le_rfl)
  have hparent : Function.Injective (Finpartition.refinementParent hV.le) := by
    intro A B h
    apply Subtype.ext
    simpa only [hcell] using congrArg Subtype.val h
  simpa only [coarsen] using map_injective hparent hf

/-- The coarse parent of the polyad of a triple is its polyad over the coarse skeleton as soon
as the color map recovers the coarse colors of its three coordinate pairs. Other pairs are
unconstrained. -/
theorem coarsen_ofTriple_of_color_coordPair (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
    {x : {x : Fin 3 → V // Function.Injective x}}
    (h₀₁ : S.pairColors.color (coordPair x 0 1 (by decide)) =
      f (T.pairColors.color (coordPair x 0 1 (by decide))))
    (h₀₂ : S.pairColors.color (coordPair x 0 2 (by decide)) =
      f (T.pairColors.color (coordPair x 0 2 (by decide))))
    (h₁₂ : S.pairColors.color (coordPair x 1 2 (by decide)) =
      f (T.pairColors.color (coordPair x 1 2 (by decide)))) :
    (ofTriple T x).coarsen hV f = ofTriple S x := by
  obtain ⟨k₀, k₁, k₂, -⟩ := ((ofTriple T x).mem_support x).1 (mem_support_ofTriple x)
  refine mem_support_iff_eq_ofTriple.1 ((mem_support _ x).2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
  · exact (coarsen_c₀ _ hV f).symm ▸ Finpartition.le_refinementParent hV _ k₀
  · exact (coarsen_c₁ _ hV f).symm ▸ Finpartition.le_refinementParent hV _ k₁
  · exact (coarsen_c₂ _ hV f).symm ▸ Finpartition.le_refinementParent hV _ k₂
  · exact (S.pairColors.color_coordPair_eq_iff _).1 (by simpa using h₀₁)
  · exact (S.pairColors.color_coordPair_eq_iff _).1 (by simpa using h₀₂)
  · exact (S.pairColors.color_coordPair_eq_iff _).1 (by simpa using h₁₂)

/-- **Moved triples.** Let the vertex cells of `T` refine those of `S`, and let the pair colors of
`S` be those of `T` mapped by `g`, except on a set `E` of ordered pairs. At most `3 |E| |V|`
injective triples then have a polyad over `S` other than the coarse parent of their polyad over
`T`. -/
theorem card_filter_ofTriple_ne_coarsen_ofTriple_le [DecidableEq κ]
    (hV : T.vertexPart ≤ S.vertexPart) (g : κ' → κ) :
    #{x | ofTriple S x ≠ (ofTriple T x).coarsen hV g} ≤
      3 * #{p | S.pairColors.color p ≠ g (T.pairColors.color p)} * Fintype.card V := by
  set E : Finset {p : V × V // p.1 ≠ p.2} := {p | S.pairColors.color p ≠ g (T.pairColors.color p)}
  have hsub : ({x | ofTriple S x ≠ (ofTriple T x).coarsen hV g} :
        Finset {x : Fin 3 → V // Function.Injective x}) ⊆
      (({x | coordPair x 0 1 (by decide) ∈ E} : Finset _) ∪
        ({x | coordPair x 0 2 (by decide) ∈ E} : Finset _)) ∪
        ({x | coordPair x 1 2 (by decide) ∈ E} : Finset _) := by
    intro x hx
    rw [mem_filter] at hx
    by_contra hE
    simp only [mem_union, mem_filter, mem_univ, true_and, not_or, E, not_not] at hE
    exact hx.2 (coarsen_ofTriple_of_color_coordPair hV g hE.1.1 hE.1.2 hE.2).symm
  have h₀₁ := card_filter_coordPair_mem_le E (by decide : (0 : Fin 3) ≠ 1) (k := 2) (by decide)
  have h₀₂ := card_filter_coordPair_mem_le E (by decide : (0 : Fin 3) ≠ 2) (k := 1) (by decide)
  have h₁₂ := card_filter_coordPair_mem_le E (by decide : (1 : Fin 3) ≠ 2) (k := 0) (by decide)
  have := (card_le_card hsub).trans (card_union_le _ _)
  have := card_union_le
    ({x | coordPair x 0 1 (by decide) ∈ E} : Finset {x : Fin 3 → V // Function.Injective x})
    ({x | coordPair x 0 2 (by decide) ∈ E} : Finset {x : Fin 3 → V // Function.Injective x})
  linarith

variable (hV : T.vertexPart ≤ S.vertexPart) (f : κ' → κ)
  (hf : ∀ p, S.pairColors.color p = f (T.pairColors.color p))
include hf

/-- The zero-one pair graph lies in that of the coarse parent. -/
theorem pairSupport₀₁_subset_coarsen (P : Polyad3 T) :
    P.pairSupport₀₁ ⊆ (P.coarsen hV f).pairSupport₀₁ := by
  intro p hp
  rw [mem_pairSupport₀₁] at hp ⊢
  simp only [coarsen_c₀, coarsen_c₁, coarsen_color₀₁]
  exact ⟨Finpartition.le_refinementParent hV _ hp.1,
    Finpartition.le_refinementParent hV _ hp.2.1, by simp [hf, hp.2.2]⟩

/-- The zero-two pair graph lies in that of the coarse parent. -/
theorem pairSupport₀₂_subset_coarsen (P : Polyad3 T) :
    P.pairSupport₀₂ ⊆ (P.coarsen hV f).pairSupport₀₂ := by
  intro p hp
  rw [mem_pairSupport₀₂] at hp ⊢
  simp only [coarsen_c₀, coarsen_c₂, coarsen_color₀₂]
  exact ⟨Finpartition.le_refinementParent hV _ hp.1,
    Finpartition.le_refinementParent hV _ hp.2.1, by simp [hf, hp.2.2]⟩

/-- The one-two pair graph lies in that of the coarse parent. -/
theorem pairSupport₁₂_subset_coarsen (P : Polyad3 T) :
    P.pairSupport₁₂ ⊆ (P.coarsen hV f).pairSupport₁₂ := by
  intro p hp
  rw [mem_pairSupport₁₂] at hp ⊢
  simp only [coarsen_c₁, coarsen_c₂, coarsen_color₁₂]
  exact ⟨Finpartition.le_refinementParent hV _ hp.1,
    Finpartition.le_refinementParent hV _ hp.2.1, by simp [hf, hp.2.2]⟩

/-- A fine polyad's support lies in the support of its coarse parent. -/
theorem support_subset_coarsen (P : Polyad3 T) : P.support ⊆ (P.coarsen hV f).support := by
  intro x hx
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := mem_support_iff_coordPair_mem.1 hx
  exact mem_support_iff_coordPair_mem.2 ⟨pairSupport₀₁_subset_coarsen hV f hf P h₀₁,
    pairSupport₀₂_subset_coarsen hV f hf P h₀₂, pairSupport₁₂_subset_coarsen hV f hf P h₁₂⟩

/-- Taking the coarse parent commutes with taking the polyad of a triple. -/
@[simp]
theorem coarsen_ofTriple (x : {x : Fin 3 → V // Function.Injective x}) :
    (ofTriple T x).coarsen hV f = ofTriple S x :=
  coarsen_ofTriple_of_color_coordPair hV f (hf _) (hf _) (hf _)

open Classical in
/-- The fine supports with a given coarse parent partition that parent's support. -/
theorem biUnion_support_coarsen [DecidableEq κ] [Fintype κ'] (P : Polyad3 S) :
    (univ.filter fun Q : Polyad3 T ↦ Q.coarsen hV f = P).biUnion support = P.support := by
  classical
  ext x
  simp only [mem_biUnion, mem_filter, mem_univ, true_and, mem_support_iff_eq_ofTriple]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ.symm.trans (coarsen_ofTriple hV f hf x)
  · intro hx
    exact ⟨ofTriple T x, (coarsen_ofTriple hV f hf x).trans hx.symm, rfl⟩

open Classical in
/-- Fine support sizes add up exactly to the support size of the coarse parent. -/
theorem sum_card_support_coarsen [DecidableEq κ] [Fintype κ'] (P : Polyad3 S) :
    ∑ Q : Polyad3 T with Q.coarsen hV f = P, #Q.support = #P.support := by
  classical
  rw [← biUnion_support_coarsen hV f hf P, card_biUnion]
  exact fun _ _ _ _ hne ↦ pairwise_disjoint_support hne

end TauCeti.Polyad3
