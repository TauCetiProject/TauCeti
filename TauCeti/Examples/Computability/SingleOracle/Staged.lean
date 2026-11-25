/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Staged.Basic
import TauCeti.Computability.SingleOracle.Staged.Search
import TauCeti.Computability.Staged.Partial.Race

/-!
# Examples of staged oracle computations

An oracle may supply a large answer at address zero. A successful normalized stage must exceed
the answer, while the use is still one. An unanswered query yields no observation at any stage.
For races, skipping initial stages can turn successive discoveries into a tie even though both
underlying partial functions are unchanged. Finally, a compiled search can distinguish an absent
observation from a stage program that is undefined.
-/

open Encodable TauCeti TauCeti.Oracle.Single Code

-- Only the output bound delays this query if the stage already exceeds the program index.
example (O : ℕ → ℕ) (s : ℕ) (hindex : encode (oracle : Code) < s) :
    (oracle.stagedEval fun z => some (O z)).stage 0 s = some ⟨O 0, 1⟩ ↔ O 0 < s := by
  cases s with
  | zero => omega
  | succ s => simp [hindex]

-- A missing oracle answer never produces a record, even at arbitrarily large stages.
example : ¬((oracle.stagedEval fun _ => none).eval 0).Dom := by
  rw [StagedPartial.not_dom_eval_iff]
  intro s
  cases s with
  | zero => simp
  | succ s => exact Option.eq_none_iff_forall_ne_some.2 fun d => by simp

-- Reindexing both inputs cofinally before taking the race can change which side wins.
example : ∃ P Q : StagedPartial ℕ ℕ,
    Sum.inr 7 ∈ (P.race Q).eval 7 ∧
    ∃ t : ℕ → ℕ, ∃ ht : Monotone t, (∀ s, ∃ k, s ≤ t k) ∧
      Sum.inl 7 ∈ ((P.reindex t ht).race (Q.reindex t ht)).eval 7 := by
  let delayed (start : ℕ) : StagedPartial ℕ ℕ :=
    { stage := fun x s => if start ≤ s then some x else none
      persistent := fun hst h => by
        split_ifs at h with hs
        simp [hs.trans hst, h] }
  let t (s : ℕ) := s + 2
  have ht : Monotone t := fun _ _ h => Nat.add_le_add_right h 2
  refine ⟨delayed 2, delayed 1, ?_, t, ht, fun s => ⟨s, Nat.le_add_right _ _⟩, ?_⟩
  · refine (StagedPartial.inr_mem_eval_race_iff _).2 ⟨1, ?_, ?_, ?_⟩
    · intro u hu
      obtain rfl := Nat.lt_one_iff.1 hu
      simp [delayed]
    · simp [delayed]
    · simp [delayed]
  · exact (StagedPartial.inl_mem_eval_race_iff _).2 ⟨0, by simp, by simp [delayed, t]⟩

-- A reported absence permits search to continue, while an undefined initial observation
-- blocks the search even though stage one would report a success in both cases.
example :
    let stageAnswers (initial : Part ℕ) : ℕ →. ℕ := fun n =>
      if n = Nat.pair 0 0 then initial
      else if n = Nat.pair 0 1 then Part.some (encode (some (0 : ℕ))) else Part.none
    eval (stageAnswers (Part.some (encode (none : Option ℕ)))) oracle.searchStages 0 =
      Part.some 0 ∧ eval (stageAnswers Part.none) oracle.searchStages 0 = Part.none := by
  intro stageAnswers
  constructor
  · refine Part.eq_some_iff.2 (mem_eval_searchStages.2 ⟨1, ?_, ?_⟩)
    · rw [eval_oracle]
      simp [stageAnswers]
    · intro t ht
      obtain rfl := Nat.lt_one_iff.1 ht
      rw [eval_oracle]
      simp [stageAnswers]
  · apply Part.eq_none_iff.2
    intro y hy
    obtain ⟨s, hs, hbefore⟩ := mem_eval_searchStages.1 hy
    cases s with
    | zero =>
      rw [eval_oracle] at hs
      simp [stageAnswers] at hs
    | succ s =>
      have h := hbefore 0 s.succ_pos
      rw [eval_oracle] at h
      simp [stageAnswers] at h

-- Racing two presentations gives a single oracle-recursive function of the input,
-- with both the winner's side and its recorded use available in the result.
example (O : ℕ → ℕ) (c d : Code) :
    RecursiveIn {(O : ℕ →. ℕ)}
      (((c.stagedEval fun z => some (O z)).race (d.stagedEval fun z => some (O z))).eval) := by
  apply StagedPartial.recursiveIn_eval
  have hO : ComputableIn {(O : ℕ →. ℕ)} O := RecursiveIn.oracle _ (Set.mem_singleton _)
  have hσ := Primrec.option_some.computableIn.comp hO
  exact (c.stagedEval fun z => some (O z)).computableIn₂_stage_race
    (c.computableIn₂_stage_stagedEval hσ) (d.computableIn₂_stage_stagedEval hσ)
