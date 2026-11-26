/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.RecursiveIn
import TauCeti.Computability.Primrec.List

/-!
# Earliest-discovery races of finite families

Given finitely many streams of optional observations, `raceFamily` keeps the first discovery
in stage order, breaking ties by the least stream index. Its output retains the winning index
and the full observation. The winner persists even for streams that can subsequently change.
For persistent streams, absence of a winner at a given stage is equivalent to absence of any
observation at that stage.

The race is uniformly computable in any oracle family in which the observations are uniformly
computable. The search only reads stages up to and including the specified stage.

## References

* C. Freer, `Computability/StagedRace.lean` in `computable-model-theory`, for two-stream
  earliest-discovery racing.
-/

public section

namespace TauCeti.Staged

variable {α : Type*} {k : ℕ}

/-- Select the first successful stream at one stage, returning its index with its observation. -/
private def firstAt (D : Fin k → ℕ → Option α) (t : ℕ) : Option (Fin k × α) :=
  ((List.finRange k).find? fun i => (D i t).isSome).bind fun i => (D i t).map (i, ·)

private theorem firstAt_eq_none_iff {D : Fin k → ℕ → Option α} {t : ℕ} :
    firstAt D t = none ↔ ∀ i, D i t = none := by
  unfold firstAt
  generalize h : (List.finRange k).find? (fun i => (D i t).isSome) = winner
  cases winner with
  | none => simpa using List.find?_eq_none.1 h
  | some i =>
    have hi := List.find?_some h
    simp only [Option.bind_some, Option.map_eq_none_iff]
    constructor
    · intro hnone
      simp [hnone] at hi
    · intro hall
      exact hall i

private theorem firstAt_eq_some_iff {D : Fin k → ℕ → Option α} {t : ℕ} {i : Fin k} {a : α} :
    firstAt D t = some (i, a) ↔ D i t = some a ∧ ∀ j < i, D j t = none := by
  have hfind : (List.finRange k).find? (fun j => (D j t).isSome) = some i ↔
      (D i t).isSome ∧ ∀ j < i, D j t = none := by
    simp only [List.find?_eq_some_iff_getElem, List.getElem_finRange, Fin.cast_mk,
      Option.not_isSome, Option.isNone_iff_eq_none, List.length_finRange, and_congr_right_iff]
    intro _
    constructor
    · rintro ⟨j, hj, rfl, hbefore⟩
      exact fun l hl => hbefore l hl
    · intro hbefore
      exact ⟨i, i.isLt, rfl, fun j hj => hbefore ⟨j, hj.trans i.isLt⟩ hj⟩
  simp only [firstAt, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, b, hb, rfl, rfl⟩
    exact ⟨hb, (hfind.1 hj).2⟩
  · rintro ⟨ha, hbefore⟩
    exact ⟨i, hfind.2 ⟨by simp [ha], hbefore⟩, a, ha, rfl, rfl⟩

/-- Race a finite family of streams through stage `s`, including stage zero. Retain the first
discovery, breaking ties by the least stream index at its discovery stage. -/
def raceFamily (D : Fin k → ℕ → Option α) (s : ℕ) : Option (Fin k × α) :=
  (List.range (s + 1)).findSome? (firstAt D)

variable {D : Fin k → ℕ → Option α} {s t : ℕ} {i : Fin k} {a : α}

/-- Every stream is still absent through this stage exactly when the race has no winner. -/
@[simp]
theorem raceFamily_eq_none_iff :
    raceFamily D s = none ↔ ∀ t ≤ s, ∀ i, D i t = none := by
  simp only [raceFamily, List.findSome?_eq_none_iff, List.mem_range, Nat.lt_succ_iff,
    firstAt_eq_none_iff]

/-- An observation wins if it is the earliest in stage order and its index is the least among
the discoveries at that stage. -/
@[simp]
theorem raceFamily_eq_some_iff :
    raceFamily D s = some (i, a) ↔ ∃ t ≤ s, D i t = some a ∧
      (∀ u < t, ∀ j, D j u = none) ∧ (∀ j < i, D j t = none) := by
  induction s with
  | zero => simp [raceFamily, firstAt_eq_some_iff]
  | succ s ih =>
    have hstep : raceFamily D (s + 1) = (raceFamily D s <|> firstAt D (s + 1)) := by
      unfold raceFamily
      rw [List.range_succ, List.findSome?_append, List.findSome?_singleton]
      simp only [Option.orElse_eq_orElse, Option.orElse_eq_or]
    rw [hstep, Option.orElse_eq_some, ih, raceFamily_eq_none_iff, firstAt_eq_some_iff]
    constructor
    · rintro (⟨t, ht, ha, hbefore, htie⟩ | ⟨hbefore, ha, htie⟩)
      · exact ⟨t, ht.trans s.le_succ, ha, hbefore, htie⟩
      · exact ⟨s + 1, le_rfl, ha, fun u hu => hbefore u (Nat.le_of_lt_succ hu), htie⟩
    · rintro ⟨t, ht, ha, hbefore, htie⟩
      rcases Nat.le_succ_iff.1 ht with hts | rfl
      · exact Or.inl ⟨t, hts, ha, hbefore, htie⟩
      · exact Or.inr ⟨fun u hu => hbefore u (Nat.lt_succ_of_le hu), ha, htie⟩

/-- A discovered result, including its index, persists at every later stage. -/
theorem raceFamily_mono {w : Fin k × α} (hst : s ≤ t) (h : raceFamily D s = some w) :
    raceFamily D t = some w := by
  obtain ⟨i, a⟩ := w
  obtain ⟨u, hu, hw⟩ := raceFamily_eq_some_iff.1 h
  exact raceFamily_eq_some_iff.2 ⟨u, hu.trans hst, hw⟩

/-- For persistent streams it suffices to check for observations at the current stage. -/
theorem raceFamily_eq_none_iff_of_persistent
    (hD : ∀ i ⦃s t a⦄, s ≤ t → D i s = some a → D i t = some a) :
    raceFamily D s = none ↔ ∀ i, D i s = none := by
  refine raceFamily_eq_none_iff.trans ⟨fun h => h s le_rfl, fun h t ht i => ?_⟩
  cases hobs : D i t with
  | none => rfl
  | some a => simpa [h i] using hD i ht hobs

/-- The race eventually discovers a winner exactly when some stream ever succeeds. -/
theorem exists_raceFamily_eq_some_iff :
    (∃ s z, raceFamily D s = some z) ↔ ∃ i s a, D i s = some a := by
  constructor
  · rintro ⟨s, ⟨i, a⟩, h⟩
    obtain ⟨t, _, hobs, _, _⟩ := raceFamily_eq_some_iff.1 h
    exact ⟨i, t, a, hobs⟩
  · rintro ⟨i, s, a, h⟩
    cases hw : raceFamily D s with
    | none => simpa [h] using raceFamily_eq_none_iff.1 hw s le_rfl i
    | some z => exact ⟨s, z, hw⟩

/-- For uniformly oracle-computable observations, racing is computable in the same oracle
family, uniformly in the common parameter and the stage. -/
theorem computableIn₂_raceFamily {γ : Type*} [Primcodable α] [Primcodable γ]
    {G : Set (ℕ →. ℕ)} {D : γ → Fin k → ℕ → Option α}
    (hD : ComputableIn G fun p : (γ × ℕ) × Fin k => D p.1.1 p.2 p.1.2) :
    ComputableIn₂ G fun x s => raceFamily (D x) s := by
  have hobs (i : Fin k) : ComputableIn G fun p : γ × ℕ => D p.1 i p.2 :=
    hD.comp (ComputableIn.id.pair (ComputableIn.const i))
  have hfind (indices : List (Fin k)) : ComputableIn G fun p : γ × ℕ =>
      indices.find? (fun i => (D p.1 i p.2).isSome) := by
    induction indices with
    | nil => exact ComputableIn.const none
    | cons i indices ih =>
      have choose : Primrec fun p : Option α × Option (Fin k) =>
          cond p.1.isSome (some i) p.2 :=
        Primrec.cond (Primrec.option_isSome.comp Primrec.fst) (Primrec.const _) Primrec.snd
      exact (choose.computableIn.comp ((hobs i).pair ih)).of_eq fun p => by
        cases h : D p.1 i p.2 <;> simp [h]
  have tag : Primrec fun p : Option α × Fin k => p.1.map (p.2, ·) :=
    Primrec.option_map Primrec.fst ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  have htag : ComputableIn₂ G fun (p : γ × ℕ) i => (D p.1 i p.2).map (i, ·) :=
    tag.computableIn.comp (hD.pair ComputableIn.snd)
  have hrow : ComputableIn₂ G fun x t => firstAt (D x) t :=
    (hfind (List.finRange k)).option_bind htag
  have hrows : ComputableIn₂ G fun x s =>
      (List.range (s + 1)).map (firstAt (D x)) :=
    hrow.list_range_map.comp
      (ComputableIn.fst.pair (Primrec.succ.computableIn.comp ComputableIn.snd))
  have hfirst : Primrec fun L : List (Option (Fin k × α)) => (L.find? Option.isSome).bind id :=
    (Primrec.option_bind₁ Primrec.id).comp
      (Primrec.list_find? Primrec.id (Primrec.option_isSome.comp Primrec.snd).to₂)
  refine (hfirst.computableIn.comp hrows).of_eq fun ⟨x, s⟩ => ?_
  simp only [Part.some_inj, raceFamily]
  have hmap := List.findSome?_map (p := id) (f := firstAt (D x)) (l := List.range (s + 1))
  rw [Function.id_comp] at hmap
  rw [← hmap]
  generalize (List.range (s + 1)).map (firstAt (D x)) = L
  induction L with
  | nil => rfl
  | cons o L ih =>
    cases o with
    | none => simpa only [List.find?_cons, Option.isSome_none, List.findSome?_cons, id_eq] using ih
    | some _ => rfl

end TauCeti.Staged
