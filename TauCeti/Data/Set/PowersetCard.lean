/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Fixed-cardinality subsets: coercions and embeddings

`Set.powersetCard.coe_ofSingleton` identifies the finite set underlying the singleton
equivalence. It lets computations with fixed-cardinality subsets use the usual singleton API.

`Set.powersetCard.card_embedding_map_eq_le` bounds the number of embeddings `α ↪ β` that carry
a fixed `n`-subset of `α` onto a fixed `n`-subset of `β` by `n! * |β| ^ (|α| - n)`. Summed over
subsets, it bounds how many labelled copies of a finite pattern meet a given family of subsets.
-/

public section

open Nat

namespace Set.powersetCard

/-- The finite set underlying the singleton equivalence is the singleton itself. -/
@[simp]
theorem coe_ofSingleton {α : Type*} (a : α) :
    ((ofSingleton a : powersetCard α 1) : Finset α) = {a} := rfl

variable {α β : Type*} {n : ℕ}

/-- At most `n! * |β| ^ (|α| - n)` embeddings `α ↪ β` carry a fixed `n`-subset `s` of `α` onto a
fixed `n`-subset `t` of `β`. -/
theorem card_embedding_map_eq_le [Finite α] [Finite β] (s : powersetCard α n)
    (t : powersetCard β n) :
    Nat.card {f : α ↪ β // map n f s = t} ≤ n ! * Nat.card β ^ (Nat.card α - n) := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have hmem (f : {f : α ↪ β // map n f s = t}) {a : α} (ha : a ∈ (s : Finset α)) :
      f.1 a ∈ (t : Finset β) := by
    obtain ⟨f, rfl⟩ := f
    exact Finset.mem_map_of_mem _ ha
  -- Such an embedding is determined by its restriction `s ↪ t` and by its values off `s`.
  let g : {f : α ↪ β // map n f s = t} →
      ((s : Finset α) ↪ (t : Finset β)) × ({a // a ∉ (s : Finset α)} → β) := fun f ↦
    (⟨fun a ↦ ⟨f.1 a, hmem f a.2⟩,
      fun _ _ h ↦ Subtype.ext (f.1.injective (congrArg Subtype.val h))⟩, fun a ↦ f.1 a)
  have hg : Function.Injective g := by
    intro f₁ f₂ h
    refine Subtype.ext (DFunLike.ext _ _ fun a ↦ ?_)
    by_cases ha : a ∈ (s : Finset α)
    · exact congrArg (fun p ↦ (p.1 ⟨a, ha⟩ : β)) h
    · exact congr_fun (congrArg Prod.snd h) ⟨a, ha⟩
  refine (Nat.card_le_card_of_injective g hg).trans_eq ?_
  simp [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_subtype_compl,
    Nat.descFactorial_self]

end Set.powersetCard
