/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.Fintype.CardEmbedding

/-!
# Regression examples: embeddings into prescribed cells

These examples check the falling-factorial convention for repeated cells through public
statements only: two indices sharing a two-element cell have two eligible injections, not the
four independent choices of the size product, and three indices sharing a two-element cell have
none.
-/

open Finset Function

/-- Two indices assigned to one two-element cell have `2 * 1 = 2` injections. -/
example : Nat.card {f : Fin 2 ↪ Fin 2 // ∀ i, f i ∈ (fun _ ↦ (univ : Finset (Fin 2))) i} = 2 := by
  rw [Nat.card_embedding_mem_eq_prod_descFactorial _ (s := {univ}) (fun _ ↦ mem_singleton_self _)
    (by simp), prod_singleton, occCount_eq_card_filter]
  simp

/-- Three indices assigned to one two-element cell have no injections. -/
example : Nat.card {f : Fin 3 ↪ Fin 2 // ∀ i, f i ∈ (fun _ ↦ (univ : Finset (Fin 2))) i} = 0 := by
  rw [Nat.card_embedding_mem_eq_prod_descFactorial _ (s := {univ}) (fun _ ↦ mem_singleton_self _)
    (by simp), prod_singleton, occCount_eq_card_filter]
  simp
