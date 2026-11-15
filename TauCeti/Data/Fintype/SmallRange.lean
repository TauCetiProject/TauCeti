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

end TauCeti
