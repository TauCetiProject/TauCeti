/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Set.PowersetCard
import TauCeti.Data.Fintype.Card.Embedding

/-!
# Embeddings with a prescribed image of a finite subset

Fix two subsets of cardinality `r` in finite types. There are at most
`r! * |β|^(|α| - r)` embeddings from `α` to `β` taking the first subset onto the second.
This separates the choices on a prescribed subset from the unconstrained remaining vertices,
as needed when bounding the number of copies affected by a hyperedge edit.

When the whole source is mapped onto a prescribed subset, the count is exact: an `n`-element
type maps onto a prescribed `n`-element finset in exactly `n!` ways. In particular every
`n`-element subset of `β` is the image of exactly `n!` embeddings of `Fin n`. Consequently a
count of labelled embeddings `Fin n ↪ β` through a condition on their images is `n!` times the
count of the `n`-element subsets satisfying it, which converts labelled copy counts into counts
of unordered subsets.
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

/-- An `n`-element type maps onto a prescribed `n`-element finset by exactly `n!` embeddings. -/
theorem natCard_embedding_map_univ_eq_factorial {α β : Type*} [Fintype α] {t : Finset β}
    (ht : #t = Fintype.card α) :
    Nat.card {f : α ↪ β // univ.map f = t} = (Fintype.card α).factorial := by
  classical
  -- An embedding maps the elements of `α` onto `t` exactly when it maps them into `t`.
  have h (f : α ↪ β) : univ.map f = t ↔ ∀ a, f a ∈ t :=
    ⟨fun hf a ↦ hf ▸ mem_map_of_mem f (mem_univ a), fun hf ↦ eq_of_subset_of_card_le
      (fun x hx ↦ by obtain ⟨a, -, rfl⟩ := mem_map.1 hx; exact hf a)
      (by rw [card_map, card_univ, ht])⟩
  -- These are the orderings of `t` by `α`.
  have hocc : Function.occCount (fun _ : α ↦ t) t = Fintype.card α := by
    rw [Function.occCount_eq_card_filter, filter_true_of_mem fun _ _ ↦ rfl, card_univ]
  rw [Nat.card_congr (Equiv.subtypeEquivRight h),
    Nat.card_embedding_mem_eq_prod_descFactorial (fun _ ↦ t) (fun _ ↦ mem_singleton_self t)
      (by simp), prod_singleton, hocc, ht, Nat.descFactorial_self]

end TauCeti

namespace Set.powersetCard

/-- Every `n`-element subset of `β` is the image of exactly `n!` embeddings of `Fin n`. -/
theorem natCard_ofFinEmb_eq_factorial {β : Type*} {n : ℕ} (t : powersetCard β n) :
    Nat.card {f : Fin n ↪ β // ofFinEmb n β f = t} = n.factorial := by
  have h := TauCeti.natCard_embedding_map_univ_eq_factorial (α := Fin n) (t := t.val)
    (by rw [card_eq, Fintype.card_fin])
  rw [Fintype.card_fin] at h
  simpa only [Subtype.ext_iff, val_ofFinEmb] using h

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
