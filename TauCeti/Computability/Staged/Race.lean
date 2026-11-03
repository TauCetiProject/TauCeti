/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.Basic

/-!
# Earliest-discovery races

`TauCeti.Staged.race` races two streams of finite observations. It retains the result seen at
the first successful stage, preferring the left stream only when both first succeed at that
stage. In particular, later discovery on the left cannot replace an earlier winner on the right.
The tag, value, and any additional data in that value are all retained.

No persistence hypothesis on the streams is needed for these finite-data results. Soundness
for partial computations requires sound observations; in particular, retaining a transient
observation from a moving oracle need not give a computation in the limit oracle.

The race is primitive recursive uniformly in primitive-recursive streams. Its application to
fixed-oracle computations is in `TauCeti.Computability.SingleOracle.Race`.
-/

public section

namespace TauCeti.Staged

variable {α β : Type*}

/-- Retain the earliest discovered result of two streams, with a left tie rule. Stage zero is
inspected as well. An absent result is `none`, not an arbitrary tagged default value. -/
def race (l : ℕ → Option α) (r : ℕ → Option β) : ℕ → Option (α ⊕ β)
  | 0 => (l 0).map Sum.inl <|> (r 0).map Sum.inr
  | s + 1 => race l r s <|> ((l (s + 1)).map Sum.inl <|> (r (s + 1)).map Sum.inr)

variable {l : ℕ → Option α} {r : ℕ → Option β} {s t : ℕ} {z : α ⊕ β}

/-- At stage zero the left stream wins a tie. -/
@[simp]
theorem race_zero (l : ℕ → Option α) (r : ℕ → Option β) :
    race l r 0 = ((l 0).map Sum.inl <|> (r 0).map Sum.inr) := (rfl)

/-- A later observation is consulted only if no result has yet been discovered. -/
theorem race_succ (l : ℕ → Option α) (r : ℕ → Option β) (s : ℕ) :
    race l r (s + 1) =
      (race l r s <|> ((l (s + 1)).map Sum.inl <|> (r (s + 1)).map Sum.inr)) := (rfl)

/-- The race has no winner exactly when neither stream has succeeded at any inspected stage. -/
@[simp]
theorem race_eq_none_iff :
    race l r s = none ↔ ∀ t ≤ s, l t = none ∧ r t = none := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [race_succ, Option.orElse_eq_none, ih]
    simp only [Option.orElse_eq_none, Option.map_eq_none_iff]
    constructor
    · rintro ⟨h, hs⟩ t ht
      obtain ht | rfl := Nat.le_succ_iff.1 ht
      · exact h t ht
      · exact hs
    · intro h
      exact ⟨fun t ht => h t (ht.trans s.le_succ), h _ le_rfl⟩

/-- A winner never changes, even if the observations themselves subsequently change. -/
theorem race_mono (hst : s ≤ t) (h : race l r s = some z) : race l r t = some z := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => simp [race_succ, ih]

/-- A result comes from the first successful observation, with the left tie rule applied at
that stage. This characterizes both the discovery time and the retained value. -/
theorem race_eq_some_iff :
    race l r s = some z ↔ ∃ t ≤ s, (∀ u < t, l u = none ∧ r u = none) ∧
      ((l t).map Sum.inl <|> (r t).map Sum.inr) = some z := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [race_succ, Option.orElse_eq_some, ih]
    constructor
    · rintro (⟨t, ht, hbefore, htval⟩ | ⟨hnone, hsval⟩)
      · exact ⟨t, ht.trans s.le_succ, hbefore, htval⟩
      · exact ⟨s + 1, le_rfl, fun u hu => race_eq_none_iff.1 hnone u (by omega), hsval⟩
    · rintro ⟨t, ht, hbefore, htval⟩
      by_cases hts : t ≤ s
      · exact Or.inl ⟨t, hts, hbefore, htval⟩
      · have hteq : t = s + 1 := by omega
        subst t
        exact Or.inr ⟨race_eq_none_iff.2 fun u hu => hbefore u (by omega), htval⟩

/-- A left result is retained exactly when the left stream succeeds at some stage `t ≤ s`
at which neither stream had succeeded earlier. Simultaneous discovery on the right does not
prevent a left win. -/
@[simp]
theorem race_eq_some_inl_iff {a : α} :
    race l r s = some (Sum.inl a) ↔ ∃ t ≤ s,
      (∀ u < t, l u = none ∧ r u = none) ∧ l t = some a := by
  simp [race_eq_some_iff]

/-- A right result wins only if the left stream is still absent at the discovery stage. -/
@[simp]
theorem race_eq_some_inr_iff {b : β} :
    race l r s = some (Sum.inr b) ↔ ∃ t ≤ s,
      (∀ u < t, l u = none ∧ r u = none) ∧ l t = none ∧ r t = some b := by
  simp [race_eq_some_iff]

/-- The race eventually succeeds exactly when at least one stream ever succeeds. The winning
side need not be the left side when both streams eventually succeed. -/
theorem exists_race_eq_some_iff :
    (∃ s z, race l r s = some z) ↔ (∃ s a, l s = some a) ∨ ∃ s b, r s = some b := by
  constructor
  · rintro ⟨s, z, hs⟩
    obtain ⟨t, -, -, ht⟩ := race_eq_some_iff.1 hs
    cases hl : l t with
    | some a => exact Or.inl ⟨t, a, hl⟩
    | none =>
      cases hr : r t with
      | some b => exact Or.inr ⟨t, b, hr⟩
      | none => simp [hl, hr] at ht
  · intro h
    obtain ⟨s, hs⟩ : ∃ s, l s ≠ none ∨ r s ≠ none := by
      rcases h with ⟨s, a, hs⟩ | ⟨s, b, hs⟩
      · exact ⟨s, Or.inl (by simp [hs])⟩
      · exact ⟨s, Or.inr (by simp [hs])⟩
    cases hrun : race l r s with
    | some z => exact ⟨s, z, hrun⟩
    | none => exact False.elim (hs.elim (fun h => h (race_eq_none_iff.1 hrun s le_rfl).1)
        (fun h => h (race_eq_none_iff.1 hrun s le_rfl).2))

/-- Racing primitive-recursive observations is primitive recursive uniformly in their common
parameter and the stage. The observation values may carry additional finite data. -/
theorem primrec_race {γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {l : γ → ℕ → Option α} {r : γ → ℕ → Option β}
    (hl : Primrec₂ l) (hr : Primrec₂ r) :
    Primrec₂ fun a s => race (l a) (r a) s := by
  have ho : Primrec fun p : γ × ℕ =>
      (l p.1 p.2).map Sum.inl <|> (r p.1 p.2).map Sum.inr :=
    Primrec.option_orElse.comp ((Primrec.option_map₁ Primrec.sumInl).comp hl)
      ((Primrec.option_map₁ Primrec.sumInr).comp hr)
  have hrec := Primrec.nat_rec (ho.comp (Primrec.id.pair (Primrec.const 0)))
    (Primrec.option_orElse.comp (Primrec.snd.comp Primrec.snd)
      (ho.comp (Primrec.fst.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))))).to₂
  exact hrec.of_eq fun a s => by
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [race_succ]
      exact congrArg (fun o => o <|> ((l a (s + 1)).map Sum.inl <|>
        (r a (s + 1)).map Sum.inr)) ih

end TauCeti.Staged
