/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Order.Hom.WithTopBot

/-!
# Finite sets of `WithBot α`

A finite set of `WithBot α` either avoids `⊥`, and is then the image of a finite set of `α` under
the coercion, or contains `⊥`, and is then `insert ⊥` of such an image. These lemmas compare the
two kinds of finite sets and count their elements; they are used to split a cube indexed by
`WithBot ι` into its two faces in the direction of `⊥`.

## Main results

* `Finset.exists_eq_map_coeWithBot_or_exists_eq_insert_bot`: every finite set of `WithBot α` is
  `S.map Function.Embedding.coeWithBot` or `insert ⊥ (S.map Function.Embedding.coeWithBot)`.
* `Finset.map_coeWithBot_ne_insert_bot` and `Finset.insert_bot_map_coeWithBot_inj`: these
  presentations are unique.
* `Finset.card_insert_bot_map_coeWithBot`, `Finset.card_filter_lt_coe_map_coeWithBot` and
  `Finset.card_filter_lt_coe_insert_bot_map_coeWithBot` count their elements, and their elements
  below a given element of `α`.
-/

public section

namespace Finset

variable {α : Type*}

section DecidableEq

variable [DecidableEq α]

/-- Inserting `⊥` into the image of a finite set of `α` adds one element. -/
theorem card_insert_bot_map_coeWithBot (S : Finset α) :
    #(insert ⊥ (S.map Function.Embedding.coeWithBot)) = #S + 1 := by
  rw [card_insert_of_notMem (by simp), card_map]

/-- Every finite set of `WithBot α` is the image of a finite set of `α`, possibly with `⊥`
inserted. -/
theorem exists_eq_map_coeWithBot_or_exists_eq_insert_bot (T : Finset (WithBot α)) :
    (∃ S : Finset α, T = S.map Function.Embedding.coeWithBot) ∨
      ∃ S : Finset α, T = insert ⊥ (S.map Function.Embedding.coeWithBot) := by
  let S : Finset α := T.preimage (↑) WithBot.coe_injective.injOn
  have key : ∀ a : α, (a : WithBot α) ∈ S.map Function.Embedding.coeWithBot ↔ (a : WithBot α) ∈ T :=
    fun a ↦ by simp [S]
  by_cases h : ⊥ ∈ T
  · refine .inr ⟨S, Finset.ext fun a ↦ ?_⟩
    induction a using WithBot.recBotCoe with
    | bot => simp [h]
    | coe a => simp [key a]
  · refine .inl ⟨S, Finset.ext fun a ↦ ?_⟩
    induction a using WithBot.recBotCoe with
    | bot => simp [h]
    | coe a => exact (key a).symm

/-- The image of a finite set of `α` never equals an image with `⊥` inserted. -/
theorem map_coeWithBot_ne_insert_bot (S T : Finset α) :
    S.map Function.Embedding.coeWithBot ≠ insert ⊥ (T.map Function.Embedding.coeWithBot) :=
  fun e ↦ by simpa using congrArg (⊥ ∈ ·) e

/-- An image of a finite set of `α` with `⊥` inserted determines the finite set. -/
theorem insert_bot_map_coeWithBot_inj {S T : Finset α} :
    insert ⊥ (S.map Function.Embedding.coeWithBot) =
      insert ⊥ (T.map Function.Embedding.coeWithBot) ↔ S = T :=
  ⟨fun e ↦ by simpa using congrArg (Finset.erase · ⊥) e, fun e ↦ e ▸ rfl⟩

end DecidableEq

variable [LT α] [DecidableLT α]

/-- The elements of the image of a finite set `S` of `α` below `a` correspond to the elements of
`S` below `a`. -/
theorem card_filter_lt_coe_map_coeWithBot (S : Finset α) (a : α) :
    #{b ∈ S.map Function.Embedding.coeWithBot | b < (a : WithBot α)} = #{b ∈ S | b < a} := by
  rw [filter_map, card_map]
  simp

/-- Inserting `⊥` into the image of a finite set adds one element below each `a : α`. -/
theorem card_filter_lt_coe_insert_bot_map_coeWithBot [DecidableEq α] (S : Finset α) (a : α) :
    #{b ∈ insert ⊥ (S.map Function.Embedding.coeWithBot) | b < (a : WithBot α)} =
      #{b ∈ S | b < a} + 1 := by
  rw [filter_insert, ite_eq_left_of_eq_true _ _ (eq_true (WithBot.bot_lt_coe a)),
    card_insert_of_notMem (by simp), card_filter_lt_coe_map_coeWithBot]

end Finset
