/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.WithTopBot
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite sets of `WithBot α`

A finite set of `WithBot α` either avoids `⊥`, and is then the image of a finite set of `α` under
the coercion, or contains `⊥`, and is then `WithBot.insertBot` of a finite set of `α`. These lemmas
compare the two kinds of finite sets, count their elements below a given element and describe their
complements; they are used to split a cube indexed by `WithBot ι` into its two faces in the
direction of `⊥`.

## Main results

* `WithBot.insertBot_eq_insert`, `WithBot.card_insertBot`: `WithBot.insertBot S` is
  `insert ⊥ (S.map Function.Embedding.coeWithBot)`, with one more element than `S`.
* `WithBot.map_coeWithBot_subset_insertBot`: the image of `S` is contained in
  `WithBot.insertBot S`.
* `Finset.exists_eq_map_coeWithBot_or_exists_eq_insertBot`: every finite set of `WithBot α` is
  `S.map Function.Embedding.coeWithBot` or `WithBot.insertBot S`.
* `Finset.map_coeWithBot_ne_insertBot`: the two kinds of finite sets are distinct.
* `Finset.card_filter_lt_coe_map_coeWithBot` and `Finset.card_filter_lt_coe_insertBot` count their
  elements below a given element of `α`.
* `Finset.optionComplEquivComplMapCoeWithBot` and `Finset.complEquivComplInsertBot` identify their
  complements with `Option ↥Sᶜ` and `↥Sᶜ`.
-/

public section

open Finset

variable {α : Type*}

namespace WithBot

/-- `WithBot.insertBot S` inserts `⊥` into the image of `S` under the coercion. -/
theorem insertBot_eq_insert [DecidableEq α] (S : Finset α) :
    insertBot S = insert ⊥ (S.map Function.Embedding.coeWithBot) :=
  cons_eq_insert _ _ (by simp)

/-- The image of `S` under the coercion is contained in `WithBot.insertBot S`. -/
theorem map_coeWithBot_subset_insertBot (S : Finset α) :
    S.map Function.Embedding.coeWithBot ⊆ insertBot S :=
  subset_cons (by simp)

@[simp]
theorem card_insertBot (S : Finset α) : #(insertBot S) = #S + 1 := by
  classical
  rw [insertBot_eq_insert, card_insert_of_notMem (by simp), card_map]

end WithBot

namespace Finset

/-- Every finite set of `WithBot α` is the image of a finite set of `α`, possibly with `⊥`
inserted. -/
theorem exists_eq_map_coeWithBot_or_exists_eq_insertBot (T : Finset (WithBot α)) :
    (∃ S : Finset α, T = S.map Function.Embedding.coeWithBot) ∨
      ∃ S : Finset α, T = WithBot.insertBot S := by
  classical
  have h : (eraseNone T).map Function.Embedding.coeWithBot = T.erase ⊥ := map_some_eraseNone T
  by_cases hT : ⊥ ∈ T
  · exact .inr ⟨eraseNone T, by rw [WithBot.insertBot_eq_insert, h, insert_erase hT]⟩
  · exact .inl ⟨eraseNone T, by rw [h, erase_eq_of_notMem hT]⟩

/-- The image of a finite set of `α` never equals `WithBot.insertBot` of a finite set. -/
theorem map_coeWithBot_ne_insertBot (S T : Finset α) :
    S.map Function.Embedding.coeWithBot ≠ WithBot.insertBot T :=
  fun e ↦ by simpa using congrArg (⊥ ∈ ·) e

section Compl

variable [Fintype α] [DecidableEq α]

/-- The elements outside the image of `S` in `WithBot α` are `⊥` and the elements outside `S`. -/
noncomputable def optionComplEquivComplMapCoeWithBot (S : Finset α) :
    Option ↥Sᶜ ≃ ↥(S.map Function.Embedding.coeWithBot)ᶜ :=
  .ofBijective (fun o ↦ o.elim ⟨⊥, by simp⟩ fun a ↦ ⟨a.1, by simpa using mem_compl.1 a.2⟩) <| by
    refine ⟨fun o o' e ↦ ?_, fun a ↦ ?_⟩
    · replace e := congrArg Subtype.val e
      rcases o with _ | ⟨a, ha⟩ <;> rcases o' with _ | ⟨a', ha'⟩
      · rfl
      · exact absurd e WithBot.bot_ne_coe
      · exact absurd e WithBot.coe_ne_bot
      · exact congrArg some (Subtype.ext (WithBot.coe_injective e))
    · obtain ⟨a, ha⟩ := a
      induction a using WithBot.recBotCoe with
      | bot => exact ⟨none, rfl⟩
      | coe a => exact ⟨some ⟨a, by simpa using ha⟩, rfl⟩

@[simp]
theorem coe_optionComplEquivComplMapCoeWithBot_none (S : Finset α) :
    (optionComplEquivComplMapCoeWithBot S none : WithBot α) = ⊥ :=
  (rfl)

@[simp]
theorem coe_optionComplEquivComplMapCoeWithBot_some (S : Finset α) (a : ↥Sᶜ) :
    (optionComplEquivComplMapCoeWithBot S (some a) : WithBot α) = a :=
  (rfl)

/-- The elements outside `WithBot.insertBot S` are the elements outside `S`. -/
noncomputable def complEquivComplInsertBot (S : Finset α) :
    ↥Sᶜ ≃ ↥(WithBot.insertBot S)ᶜ :=
  .ofBijective (fun a ↦ ⟨a.1, by simpa using mem_compl.1 a.2⟩) <| by
    refine ⟨fun a a' e ↦ Subtype.ext (by simpa using e), fun a ↦ ?_⟩
    obtain ⟨a, ha⟩ := a
    induction a using WithBot.recBotCoe with
    | bot => simp at ha
    | coe a => exact ⟨⟨a, by simpa using ha⟩, rfl⟩

@[simp]
theorem coe_complEquivComplInsertBot (S : Finset α) (a : ↥Sᶜ) :
    (complEquivComplInsertBot S a : WithBot α) = a :=
  (rfl)

end Compl

variable [LT α] [DecidableLT α]

/-- The elements of the image of a finite set `S` of `α` below `a` correspond to the elements of
`S` below `a`. -/
theorem card_filter_lt_coe_map_coeWithBot (S : Finset α) (a : α) :
    #{b ∈ S.map Function.Embedding.coeWithBot | b < (a : WithBot α)} = #{b ∈ S | b < a} := by
  rw [filter_map, card_map]
  simp

/-- Inserting `⊥` into the image of a finite set adds one element below each `a : α`. -/
theorem card_filter_lt_coe_insertBot (S : Finset α) (a : α) :
    #{b ∈ WithBot.insertBot S | b < (a : WithBot α)} = #{b ∈ S | b < a} + 1 := by
  classical
  rw [WithBot.insertBot_eq_insert, filter_insert,
    ite_eq_left_of_eq_true _ _ (eq_true (WithBot.bot_lt_coe a)), card_insert_of_notMem (by simp),
    card_filter_lt_coe_map_coeWithBot]

end Finset
