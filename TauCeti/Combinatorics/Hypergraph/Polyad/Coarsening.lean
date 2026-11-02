/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic
public import TauCeti.Order.Partition.Finpartition

/-!
# Coarse parents of polyads

A refinement of vertex cells and a projection of pair colors assign each fine polyad a coarse
parent. When the projection recovers the original pair coloring, each fine pair graph lies in
the corresponding coarse pair graph. The fine supports with a given parent partition its
support, including when cells repeat. These facts let local slicing estimates be summed over
a refined skeleton without charging the same coarse exceptional support more than once.
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
  let A := Finpartition.refinementParent hV ⟨P.c₀, P.hc₀⟩
  let B := Finpartition.refinementParent hV ⟨P.c₁, P.hc₁⟩
  let C := Finpartition.refinementParent hV ⟨P.c₂, P.hc₂⟩
  ofData A B C A.property B.property C.property
    (f P.color₀₁) (f P.color₀₂) (f P.color₁₂)

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
  mem_support_iff_eq_ofTriple.1 (support_subset_coarsen hV f hf _ (mem_support_ofTriple x))

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
