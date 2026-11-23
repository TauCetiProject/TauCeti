/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Staged.Partial
public import TauCeti.Computability.Staged.Race.Relative

/-!
# Earliest-discovery races of staged partial functions

A race retains the first discovery of the two tables passed to it, with a left tie rule.
A cofinal monotone clock can turn two discoveries into a tie and change which side wins.
-/

public section

namespace TauCeti.StagedPartial

variable {α β γ : Type*} (P : StagedPartial α β)

/-- Race two presentations on the same input. The first discovery wins and simultaneous
first discoveries are resolved in favor of the left table. -/
def race (Q : StagedPartial α γ) : StagedPartial α (β ⊕ γ) where
  stage x := Staged.race (P.stage x) (Q.stage x)
  persistent hst h := Staged.race_mono hst h

/-- The stage table of a race records the first tagged observation. -/
@[simp]
theorem stage_race (Q : StagedPartial α γ) (x : α) (s : ℕ) :
    (P.race Q).stage x s = Staged.race (P.stage x) (Q.stage x) s := (rfl)

/-- The left value wins when it is present at the first discovery stage. -/
@[simp]
theorem inl_mem_eval_race_iff {Q : StagedPartial α γ} {x : α} {y : β} :
    Sum.inl y ∈ (P.race Q).eval x ↔
      ∃ s, (∀ t < s, P.stage x t = none ∧ Q.stage x t = none) ∧ P.stage x s = some y := by
  simp only [mem_eval_iff, stage_race, Staged.race_eq_some_inl_iff]
  exact ⟨fun ⟨_, s, _, h⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, s, le_rfl, h⟩⟩

/-- The right value wins when it is present at the first discovery stage and the left is absent. -/
@[simp]
theorem inr_mem_eval_race_iff {Q : StagedPartial α γ} {x : α} {z : γ} :
    Sum.inr z ∈ (P.race Q).eval x ↔
      ∃ s, (∀ t < s, P.stage x t = none ∧ Q.stage x t = none) ∧
        P.stage x s = none ∧ Q.stage x s = some z := by
  simp only [mem_eval_iff, stage_race, Staged.race_eq_some_inr_iff]
  exact ⟨fun ⟨_, s, _, h⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, s, le_rfl, h⟩⟩

/-- A left winner is a value of the left partial function. -/
theorem mem_eval_of_inl_mem_eval_race {Q : StagedPartial α γ} {x : α} {y : β}
    (h : Sum.inl y ∈ (P.race Q).eval x) : y ∈ P.eval x := by
  obtain ⟨s, -, hs⟩ := P.inl_mem_eval_race_iff.1 h
  exact P.mem_eval_iff.2 ⟨s, hs⟩

/-- A right winner is a value of the right partial function. -/
theorem mem_eval_of_inr_mem_eval_race {Q : StagedPartial α γ} {x : α} {z : γ}
    (h : Sum.inr z ∈ (P.race Q).eval x) : z ∈ Q.eval x := by
  obtain ⟨s, -, -, hs⟩ := P.inr_mem_eval_race_iff.1 h
  exact Q.mem_eval_iff.2 ⟨s, hs⟩

/-- A race converges on an input exactly when at least one of its two sides converges. -/
@[simp]
theorem dom_eval_race (Q : StagedPartial α γ) (x : α) :
    ((P.race Q).eval x).Dom ↔ (P.eval x).Dom ∨ (Q.eval x).Dom := by
  simp only [Part.dom_iff_mem, mem_eval_iff, stage_race, exists_comm (α := β ⊕ γ),
    exists_comm (α := β), exists_comm (α := γ)]
  exact Staged.exists_race_eq_some_iff

/-- Racing effective tables gives a table computable in the same oracle family. -/
theorem computableIn₂_stage_race [Primcodable α] [Primcodable β] [Primcodable γ]
    {G : Set (ℕ →. ℕ)} {Q : StagedPartial α γ} (hP : ComputableIn₂ G P.stage)
    (hQ : ComputableIn₂ G Q.stage) : ComputableIn₂ G (P.race Q).stage := by
  simpa only [ComputableIn₂, stage_race] using Staged.computableIn₂_race hP hQ

end TauCeti.StagedPartial
