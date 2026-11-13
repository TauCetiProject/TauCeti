/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin

/-!
# Counting functions with small range

A function into a nonempty finite type `β` visiting at most `r` values factors through `Fin r`.
Counting the two maps in this factorization bounds the number of such functions by
`|β|^r * r^|α|`. This deliberately coarse bound controls sums over matrix trace words with fewer
than the leading number of vertices.
-/

public section

namespace TauCeti

open Finset

/-- There are at most `|β|^r * r^|α|` functions from `α` to a nonempty finite type `β` that
visit at most `r` values. The domain and `r` may be empty or zero. -/
theorem card_filter_card_image_le {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    [DecidableEq α] [DecidableEq β] (r : ℕ) :
    #{f : α → β | #(univ.image f) ≤ r} ≤ Fintype.card β ^ r * r ^ Fintype.card α := by
  classical
  have hsurj : Set.SurjOn (fun p : (Fin r → β) × (α → Fin r) ↦ p.1 ∘ p.2)
      (↑(univ : Finset ((Fin r → β) × (α → Fin r))))
      (↑({f : α → β | #(univ.image f) ≤ r} : Finset (α → β))) := by
    intro f hf
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (α := ↥(univ.image f)) (β := Fin r) (by
        rw [Fintype.card_coe, Fintype.card_fin]
        exact (mem_filter.mp hf).2)
    let g : α → Fin r := fun a ↦ e ⟨f a, mem_image_of_mem f (mem_univ a)⟩
    let h : Fin r → β := Function.extend e Subtype.val (fun _ ↦ Classical.choice ‹Nonempty β›)
    refine ⟨(h, g), mem_univ _, ?_⟩
    funext a
    simpa only [h, g, Function.comp_apply] using
      e.injective.extend_apply Subtype.val (fun _ ↦ Classical.choice ‹Nonempty β›)
        ⟨f a, mem_image_of_mem f (mem_univ a)⟩
  simpa using card_le_card_of_surjOn _ hsurj

/-- At most `|β|^r * r^(|ι₁| + |ι₂|)` pairs of functions from `ι₁` and `ι₂` into a nonempty
finite type `β` have combined range of size at most `r`. Either domain or `r` may be empty or
zero. -/
theorem card_filter_card_image_union_le {ι₁ ι₂ β : Type*} [Fintype ι₁] [Fintype ι₂]
    [Fintype β] [Nonempty β] [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq β] (r : ℕ) :
    #{p : (ι₁ → β) × (ι₂ → β) | #(univ.image p.1 ∪ univ.image p.2) ≤ r} ≤
      Fintype.card β ^ r * r ^ (Fintype.card ι₁ + Fintype.card ι₂) := by
  let e := (Equiv.sumArrowEquivProdArrow ι₁ ι₂ β).symm
  have himage (p : (ι₁ → β) × (ι₂ → β)) :
      univ.image (e p) = univ.image p.1 ∪ univ.image p.2 := by
    rcases p with ⟨f, g⟩
    ext x
    simp [e, Sum.exists]
  have hinj : #(filter (fun p : (ι₁ → β) × (ι₂ → β) ↦ #(univ.image p.1 ∪ univ.image p.2) ≤ r)
      univ) ≤ #{f : ι₁ ⊕ ι₂ → β | #(univ.image f) ≤ r} :=
    card_le_card_of_injOn e (fun p hp ↦ by
      rw [mem_coe, mem_filter] at hp ⊢
      exact ⟨mem_univ _, (himage p).symm ▸ hp.2⟩) e.injective.injOn
  simpa only [Fintype.card_sum] using hinj.trans (card_filter_card_image_le r)

end TauCeti
