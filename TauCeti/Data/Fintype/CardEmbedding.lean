/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.Fiber
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Pairwise

/-! # Counting embeddings

The injective maps `α → β` between finite types correspond to the embeddings `α ↪ β`, so there
are `(card β).descFactorial (card α)` of them. We restate `Fintype.card_embedding_eq` for the
subtype of injective functions, the form in which counts over injective tuples `Fin n → V` are
taken.

We also count embeddings into prescribed cells. Given a family `c : ι → Finset V` of cells, we
count the embeddings `f : ι ↪ V` with `f i ∈ c i` for every `i`. When the cells are taken from a
pairwise disjoint family, injectivity only constrains indices sharing a cell, so the count factors
over the cells: a cell `A` hosting `m` indices contributes the falling factorial
`(#A).descFactorial m`, and an unused cell contributes one. In particular, distinct cells
contribute just their sizes, and in general the count is at most the product of the sizes of the
cells.

Finally, we bound the embeddings with prescribed values on part of the domain. An embedding
`f : β ↪ V` with `f ∘ e = x` along an embedding `e : α ↪ β` is determined by its values off the
range of `e`, so there are at most `card V ^ (card β - card α)` of them. When `β` is a linear
order, summing over the `(card β).choose m` increasing tuples `g : Fin m ↪o β` bounds the
embeddings sending some increasing `m`-tuple into a prescribed set `T` of `m`-tuples.

## Main results

* `Fintype.card_subtype_injective`: there are `(card β).descFactorial (card α)` injective maps
  `α → β`.
* `Equiv.embeddingMemEquivPi`: over a pairwise disjoint family of cells, the embeddings into the
  cells are the families of embeddings, one for each cell, of the indices assigned to that cell.
* `Nat.card_embedding_mem_eq_prod_descFactorial`: the count over a pairwise disjoint family
  of cells is the product of falling factorials of the cell sizes at the occurrence counts.
* `Nat.card_embedding_mem_eq_prod_of_injective`: for distinct disjoint cells, the count is the
  product of the cell sizes.
* `Nat.card_embedding_mem_le_prod`: the count never exceeds the product of the cell sizes.
* `Function.Embedding.natCard_embedding_comp_eq_le`: at most `card V ^ (card β - card α)`
  embeddings `f : β ↪ V` satisfy `f ∘ e = x`.
* `Finset.natCard_embedding_exists_comp_mem_le`: at most
  `(card β).choose m * #T * card V ^ (card β - m)` embeddings send some increasing `m`-tuple
  into `T`.
-/

public section

open Finset Function

namespace Fintype

/-- There are `(card β).descFactorial (card α)` injective maps `α → β`; for instance
`|V| (|V| - 1) (|V| - 2)` injective triples `Fin 3 → V`. This is `Fintype.card_embedding_eq` for
the subtype of injective functions. -/
theorem card_subtype_injective {α β : Type*} [Fintype α] [Fintype β]
    [Fintype {f : α → β // Function.Injective f}] :
    card {f : α → β // Function.Injective f} = (card β).descFactorial (card α) := by
  rw [card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _), card_embedding_eq]

end Fintype

namespace Equiv

variable {ι V : Type*} {c : ι → Finset V} {s : Finset (Finset V)}

/-- The value of a family of cellwise embeddings at an index only depends on its cell. -/
private theorem embeddingMemEquivPi_aux (hs : ∀ i, c i ∈ s)
    (g : (A : s) → ({i // c i = A.1} ↪ A.1)) (A : s) (i : ι) (hi : c i = A.1) :
    (g ⟨c i, hs i⟩ ⟨i, rfl⟩ : V) = g A ⟨i, hi⟩ := by
  obtain ⟨A, hA⟩ := A
  obtain rfl : c i = A := hi
  rfl

/-- Gluing a family of cellwise embeddings into disjoint cells gives an injective map. -/
private theorem embeddingMemEquivPi_injective (hs : ∀ i, c i ∈ s)
    (hdisj : (s : Set (Finset V)).PairwiseDisjoint id) (g : (A : s) → ({i // c i = A.1} ↪ A.1)) :
    Injective fun i ↦ (g ⟨c i, hs i⟩ ⟨i, rfl⟩ : V) := by
  intro i j hij
  beta_reduce at hij
  -- A common value forces a common cell, inside which `g` is injective.
  have hc : c j = c i :=
    hdisj.elim_finset (hs j) (hs i) _ (g ⟨c j, hs j⟩ ⟨j, rfl⟩).2 (hij ▸ (g ⟨c i, hs i⟩ ⟨i, rfl⟩).2)
  have h := embeddingMemEquivPi_aux hs g ⟨c i, hs i⟩ j hc
  rw [← hij] at h
  exact congrArg Subtype.val (Subtype.ext_iff.2 h |> (g _).injective)

variable (c) in
/-- **Embeddings into disjoint cells, cell by cell.** If the cells `c i` lie in a pairwise
disjoint family `s`, an embedding `f : ι ↪ V` with `f i ∈ c i` for all `i` is the same as a
family, indexed by the cells `A ∈ s`, of embeddings of the indices assigned to `A` into `A`. -/
def embeddingMemEquivPi (hs : ∀ i, c i ∈ s) (hdisj : (s : Set (Finset V)).PairwiseDisjoint id) :
    {f : ι ↪ V // ∀ i, f i ∈ c i} ≃ ((A : s) → ({i // c i = A.1} ↪ A.1)) where
  toFun f _ := ⟨fun x ↦ ⟨f.1 x.1, Eq.subst (motive := (f.1 x.1 ∈ ·)) x.2 (f.2 x.1)⟩,
    fun _ _ h ↦ Subtype.ext (f.1.injective (congrArg Subtype.val h))⟩
  invFun g := ⟨⟨fun i ↦ g ⟨c i, hs i⟩ ⟨i, rfl⟩, embeddingMemEquivPi_injective hs hdisj g⟩,
    fun i ↦ (g ⟨c i, hs i⟩ ⟨i, rfl⟩).2⟩
  left_inv _ := rfl
  right_inv g := funext fun A ↦ Embedding.ext fun x ↦
    Subtype.ext (embeddingMemEquivPi_aux hs g A x.1 x.2)

@[simp]
theorem embeddingMemEquivPi_apply_apply_coe (hs : ∀ i, c i ∈ s)
    (hdisj : (s : Set (Finset V)).PairwiseDisjoint id) (f : {f : ι ↪ V // ∀ i, f i ∈ c i}) (A : s)
    (x : {i // c i = A.1}) : (embeddingMemEquivPi c hs hdisj f A x : V) = f.1 x.1 :=
  (rfl)

@[simp]
theorem embeddingMemEquivPi_symm_apply_coe_apply (hs : ∀ i, c i ∈ s)
    (hdisj : (s : Set (Finset V)).PairwiseDisjoint id) (g : (A : s) → ({i // c i = A.1} ↪ A.1))
    (i : ι) : ((embeddingMemEquivPi c hs hdisj).symm g).1 i = g ⟨c i, hs i⟩ ⟨i, rfl⟩ :=
  (rfl)

end Equiv

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
  rw [Nat.card_congr (Equiv.embeddingMemEquivPi c hs hdisj), Nat.card_eq_fintype_card,
    Fintype.card_pi, ← prod_coe_sort s]
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

namespace Function.Embedding

variable {V : Type*}

/-- An embedding `f : β ↪ V` with prescribed values `f ∘ e = x` along an embedding `e : α ↪ β` is
determined by its values off the range of `e`, so there are at most
`card V ^ (card β - card α)` of them. -/
theorem natCard_embedding_comp_eq_le {α β : Type*} [Fintype α] [Fintype β] [Fintype V]
    (e : α ↪ β) (x : α → V) :
    Nat.card {f : β ↪ V // ⇑f ∘ e = x} ≤ Fintype.card V ^ (Fintype.card β - Fintype.card α) := by
  classical
  let s : Finset β := univ.map e
  have hcode : Injective fun (f : {f : β ↪ V // ⇑f ∘ e = x}) (b : ↥sᶜ) ↦ f.1 b := by
    intro f g h
    refine Subtype.ext (Embedding.ext fun b ↦ ?_)
    by_cases hb : b ∈ s
    · obtain ⟨a, -, rfl⟩ := mem_map.1 hb
      exact (congrFun f.2 a).trans (congrFun g.2 a).symm
    · exact congrFun h ⟨b, mem_compl.2 hb⟩
  refine (Nat.card_le_card_of_injective _ hcode).trans_eq ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe, card_compl, card_map,
    Finset.card_univ]

end Function.Embedding

namespace Finset

variable {V : Type*}

/-- At most `(card β).choose m * #T * card V ^ (card β - m)` embeddings `f : β ↪ V` of a finite
linear order send some increasing `m`-tuple of `β` into a prescribed set `T` of `m`-tuples: there
are `(card β).choose m` increasing tuples `g`, and for each of them and each `x ∈ T` at most
`card V ^ (card β - m)` embeddings satisfy `f ∘ g = x`. -/
theorem natCard_embedding_exists_comp_mem_le {β : Type*} [Fintype β] [LinearOrder β]
    [Fintype V] {m : ℕ} (T : Finset (Fin m → V)) :
    Nat.card {f : β ↪ V // ∃ g : Fin m ↪o β, ⇑f ∘ g ∈ T} ≤
      (Fintype.card β).choose m * #T * Fintype.card V ^ (Fintype.card β - m) := by
  classical
  -- Every increasing `m`-tuple is the increasing enumeration of its range, an `m`-subset.
  let U : Finset (β ↪ V) := (univ.powersetCard m).attach.biUnion fun s ↦ T.biUnion fun x ↦
    {f | ⇑f ∘ s.1.orderEmbOfFin (mem_powersetCard.1 s.2).2 = x}
  have hU (f : β ↪ V) (hf : ∃ g : Fin m ↪o β, ⇑f ∘ g ∈ T) : f ∈ U := by
    obtain ⟨g, hg⟩ := hf
    have hcard : #(univ.map g.toEmbedding) = m := by simp
    simp only [U, mem_biUnion, mem_attach, mem_filter, mem_univ, true_and]
    refine ⟨⟨_, mem_powersetCard.2 ⟨subset_univ _, hcard⟩⟩, _, hg, ?_⟩
    rw [← orderEmbOfFin_unique' hcard fun i ↦ mem_map_of_mem _ (mem_univ i)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc #{f : β ↪ V | ∃ g : Fin m ↪o β, ⇑f ∘ g ∈ T}
      ≤ #U := card_le_card fun f hf ↦ hU f (mem_filter.1 hf).2
    _ ≤ ∑ _s ∈ (univ.powersetCard m).attach, ∑ _x ∈ T,
          Fintype.card V ^ (Fintype.card β - m) := by
      refine card_biUnion_le.trans <| sum_le_sum fun s _ ↦ card_biUnion_le.trans <|
        sum_le_sum fun x _ ↦ ?_
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      simpa using
        (s.1.orderEmbOfFin (mem_powersetCard.1 s.2).2).toEmbedding.natCard_embedding_comp_eq_le x
    _ = (Fintype.card β).choose m * #T * Fintype.card V ^ (Fintype.card β - m) := by
      simp [card_powersetCard, mul_assoc]

end Finset
