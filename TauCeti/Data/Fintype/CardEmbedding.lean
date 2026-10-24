/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.Fiber
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Pairwise

/-! # Embeddings into prescribed cells

Given a family `c : ι → Finset V` of cells, we count the embeddings `f : ι ↪ V` with
`f i ∈ c i` for every `i`. When the cells are taken from a pairwise disjoint family, injectivity
only constrains indices sharing a cell, so the count factors over the cells: a cell `A` hosting
`m` indices contributes the falling factorial `(#A).descFactorial m`, and an unused cell
contributes one. In particular, distinct cells contribute just their sizes, and in general the
count is at most the product of the sizes of the cells.

## Main results

* `Nat.card_embedding_mem_eq_prod_descFactorial`: the count over a pairwise disjoint family
  of cells is the product of falling factorials of the cell sizes at the occurrence counts.
* `Nat.card_embedding_mem_eq_prod_of_injective`: for distinct disjoint cells, the count is the
  product of the cell sizes.
* `Nat.card_embedding_mem_le_prod`: the count never exceeds the product of the cell sizes.
-/

public section

open Finset Function

namespace Nat

variable {ι V : Type*}

/-- **Embeddings into disjoint cells.** If the cells `c i` lie in a pairwise disjoint family `s`,
then the embeddings `f : ι ↪ V` with `f i ∈ c i` for all `i` are counted cell by cell: each cell
`A ∈ s` contributes the falling factorial of its size at the number of indices assigned to it. -/
theorem card_embedding_mem_eq_prod_descFactorial [Finite ι] (c : ι → Finset V)
    {s : Finset (Finset V)} (hs : ∀ i, c i ∈ s) (hdisj : (s : Set (Finset V)).PairwiseDisjoint id) :
    Nat.card {f : ι ↪ V // ∀ i, f i ∈ c i} = ∏ A ∈ s, (#A).descFactorial (occCount c A) := by
  classical
  have := Fintype.ofFinite ι
  -- Evaluating a family of cellwise embeddings at the cell of each index.
  let g' (g : (A : s) → ({i // c i = A.1} ↪ A.1)) (i : ι) : V := g ⟨c i, hs i⟩ ⟨i, rfl⟩
  -- The value at an index only depends on its cell.
  have hg' (g : (A : s) → ({i // c i = A.1} ↪ A.1)) (A : s) (x : {i // c i = A.1}) :
      g' g x.1 = g A x := by
    obtain ⟨A, hA⟩ := A
    obtain ⟨i, hi⟩ := x
    obtain rfl : c i = A := hi
    rfl
  have hg'_mem (g : (A : s) → ({i // c i = A.1} ↪ A.1)) (i : ι) : g' g i ∈ c i :=
    (g ⟨c i, hs i⟩ ⟨i, rfl⟩).2
  have hg'_inj (g : (A : s) → ({i // c i = A.1} ↪ A.1)) : Injective (g' g) := by
    intro i j hij
    -- A common value forces a common cell, inside which `g` is injective.
    have hc : c j = c i :=
      hdisj.elim_finset (hs j) (hs i) (g' g j) (hg'_mem g j) (hij ▸ hg'_mem g i)
    have h := hg' g ⟨c i, hs i⟩ ⟨j, hc⟩
    rw [← hij, hg' g ⟨c i, hs i⟩ ⟨i, rfl⟩] at h
    exact congrArg Subtype.val (Subtype.ext_iff.2 h |> (g _).injective)
  let e : {f : ι ↪ V // ∀ i, f i ∈ c i} ≃ ((A : s) → ({i // c i = A.1} ↪ A.1)) :=
    { toFun f A := ⟨fun x ↦ ⟨f.1 x.1, Eq.subst (motive := (f.1 x.1 ∈ ·)) x.2 (f.2 x.1)⟩,
          fun x y h ↦ Subtype.ext (f.1.injective (congrArg Subtype.val h))⟩
      invFun g := ⟨⟨g' g, hg'_inj g⟩, hg'_mem g⟩
      left_inv _ := rfl
      right_inv g := funext fun A ↦ Embedding.ext fun x ↦ Subtype.ext (hg' g A x) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi, ← prod_coe_sort s]
  refine Finset.prod_congr rfl fun A _ ↦ ?_
  rw [Fintype.card_embedding_eq, Fintype.card_coe, occCount_def, Nat.card_eq_fintype_card]

/-- **Embeddings into distinct disjoint cells.** If the cells `c i` are pairwise distinct members
of a pairwise disjoint family, the embeddings `f : ι ↪ V` with `f i ∈ c i` for all `i` are counted
by the product of the cell sizes. -/
theorem card_embedding_mem_eq_prod_of_injective [Fintype ι] {c : ι → Finset V} (hc : Injective c)
    {s : Finset (Finset V)} (hs : ∀ i, c i ∈ s)
    (hdisj : (s : Set (Finset V)).PairwiseDisjoint id) :
    Nat.card {f : ι ↪ V // ∀ i, f i ∈ c i} = ∏ i, #(c i) := by
  classical
  have himage : univ.image c ⊆ s := fun A hA ↦ by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hA
    exact hs i
  rw [card_embedding_mem_eq_prod_descFactorial c hs hdisj, ← Finset.prod_subset himage
    fun A _ hA ↦ ?_, prod_image fun i _ j _ h ↦ hc h]
  · simp [occCount_apply_of_injective c hc]
  · rw [occCount_of_notMem_range c A fun ⟨i, hi⟩ ↦ hA (mem_image.2 ⟨i, mem_univ _, hi⟩),
      Nat.descFactorial_zero]

/-- The embeddings `f : ι ↪ V` with `f i ∈ c i` for all `i` are at most as many as the product
of the cell sizes, the number of all maps with this property. -/
theorem card_embedding_mem_le_prod [Fintype ι] (c : ι → Finset V) :
    Nat.card {f : ι ↪ V // ∀ i, f i ∈ c i} ≤ ∏ i, #(c i) := by
  classical
  rw [← Fintype.card_piFinset, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective (fun f ↦ ⟨f.1, Fintype.mem_piFinset.2 f.2⟩) fun f g h ↦
    Subtype.ext (Embedding.ext (congrFun (congrArg Subtype.val h)))

end Nat
