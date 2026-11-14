/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Set.PowersetCard

/-!
# Embeddings with a prescribed image of a finite subset

Fix two subsets of cardinality `r` in finite types. There are at most
`r! * |β|^(|α| - r)` embeddings from `α` to `β` taking the first subset onto the second.
This separates the choices on a prescribed subset from the unconstrained remaining vertices,
as needed when bounding the number of copies affected by a hyperedge edit.

When the source is `Fin n` itself, the count is exact: every `n`-element subset of `β` is the
image of exactly `n!` embeddings of `Fin n`. Consequently a count of labelled embeddings
`Fin n ↪ β` through a condition on their images is `n!` times the count of the `n`-element
subsets satisfying it, which converts labelled copy counts into counts of unordered subsets.
-/

public section

open Finset

namespace TauCeti

/-- The embeddings taking one prescribed `r`-element subset onto another are bounded by the
`r!` bijections on those subsets and arbitrary choices on the complement. -/
theorem card_embedding_map_eq_le {α β : Type*} [Fintype α] [Fintype β] {r : ℕ}
    {s : Set.powersetCard α r} {t : Set.powersetCard β r} :
    Nat.card {f : α ↪ β // Set.powersetCard.map r f s = t} ≤
      r.factorial * Fintype.card β ^ (Fintype.card α - r) := by
  classical
  let code : {f : α ↪ β // Set.powersetCard.map r f s = t} →
      (s.val ↪ t.val) × (↥(s.valᶜ) → β) := fun f ↦
    (⟨fun a ↦ ⟨f.val a, by
        have hm : f.val a ∈ (Set.powersetCard.map r f.val s).val := by
          simp only [Set.powersetCard.val_map, Finset.mem_map]
          exact ⟨a, a.prop, rfl⟩
        simpa only [f.prop] using hm⟩,
      fun a b h ↦ Subtype.ext (f.val.injective (congrArg Subtype.val h))⟩,
      fun a ↦ f.val a)
  have hinj : Function.Injective code := by
    intro f g h
    apply Subtype.ext
    ext a
    by_cases ha : a ∈ s.val
    · exact congrArg Subtype.val
        (congrFun (congrArg (fun p ↦ (p.1 : s.val → t.val)) h) ⟨a, ha⟩)
    · exact congrFun (congrArg Prod.snd h) ⟨a, Finset.mem_compl.mpr ha⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fun, Fintype.card_coe, Set.powersetCard.card_eq, Finset.card_compl,
    Nat.descFactorial_self] using Nat.card_le_card_of_injective code hinj

end TauCeti

namespace Set.powersetCard

/-- Every `n`-element subset of `β` is the image of exactly `n!` embeddings of `Fin n`. -/
theorem natCard_ofFinEmb_eq_factorial {β : Type*} {n : ℕ} (t : powersetCard β n) :
    Nat.card {f : Fin n ↪ β // ofFinEmb n β f = t} = n.factorial := by
  classical
  -- Such an embedding is the same as an embedding of `Fin n` into `t`, which is onto `t`
  -- because both have `n` elements.
  let e : {f : Fin n ↪ β // ofFinEmb n β f = t} ≃ (Fin n ↪ t.val) :=
    { toFun f := ⟨fun i ↦ ⟨f.1 i, by
          have h := Finset.mem_map_of_mem f.1 (Finset.mem_univ i)
          rwa [← val_ofFinEmb, f.2] at h⟩,
        fun i j h ↦ f.1.injective (congrArg Subtype.val h)⟩
      invFun g := ⟨g.trans (Function.Embedding.subtype _), by
        refine Subtype.ext ?_
        rw [val_ofFinEmb]
        refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_
        · obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
          exact (g i).2
        · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, card_eq]⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe, card_eq, Nat.descFactorial_self]

/-- There are `n!` times as many embeddings of `Fin n` whose image satisfies a condition as there
are `n`-element subsets satisfying it. -/
theorem card_filter_ofFinEmb {β : Type*} [Fintype β] {n : ℕ}
    (p : powersetCard β n → Prop) [DecidablePred p] :
    #{f : Fin n ↪ β | p (ofFinEmb n β f)} = n.factorial * #{s | p s} := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := ofFinEmb n β) (t := {s | p s})
    fun f hf ↦ by simpa using hf, mul_comm]
  refine Finset.sum_const_nat fun s hs ↦ ?_
  rw [← natCard_ofFinEmb_eq_factorial s, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  rintro rfl
  simpa using hs

end Set.powersetCard
