/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTimeParser

/-!
# Polynomial-time parser composition and proof erasure

These combinators preserve the unconsumed suffix and compile to the option and
pair machines. The erasure lemmas relate ordinary list results to the existing
dependent vector parsers.
-/

@[expose] public section

namespace TauCeti.BinaryCodec

open Computability BitEncoding Turing

variable {α β γ : Type}

/-- Transform a successful parsed value while preserving its unconsumed suffix. -/
def mapParser (f : α → β → γ) (parser : α → Parser β) (a : α) : Parser γ :=
  fun bits => (parser a bits).map fun q => (f a q.1, q.2)

/-- Continue parsing the unconsumed suffix with a parser depending on the first value. -/
def bindParser (parser : α → Parser β) (next : α × β → Parser γ) (a : α) : Parser γ :=
  fun bits => (parser a bits).bind fun q => next (a, q.1) q.2

/-- Return a value without consuming any input bits. -/
def pureParser (f : α → β) (a : α) : Parser β := fun bits => some (f a, bits)

/-- Reject a successful parse when its value fails the supplied Boolean check. -/
def filterParser (f : α → β → Bool) (parser : α → Parser β) (a : α) : Parser β :=
  fun bits => (parser a bits).bind fun q => bif f a q.1 then some q else none

theorem consumes_reparam {parser : α → Parser β} (hc : Consumes parser) (f : γ → α) :
    Consumes (fun a => parser (f a)) := fun a => hc (f a)

theorem consumes_mapParser {f : α → β → γ} {parser : α → Parser β}
    (hc : Consumes parser) : Consumes (mapParser f parser) := by
  intro a bits value tail h
  cases hp : parser a bits with
  | none => simp [mapParser, hp] at h
  | some q =>
    have hh : (f a q.1, q.2) = (value, tail) := by simpa [mapParser, hp] using h
    have ht : q.2 = tail := congrArg Prod.snd hh
    rw [← ht]
    exact hc a bits q.1 q.2 hp

theorem consumes_bindParser {parser : α → Parser β} {next : α × β → Parser γ}
    (hp : Consumes parser) (hq : Consumes next) : Consumes (bindParser parser next) := by
  intro a bits value tail h
  cases hs : parser a bits with
  | none => simp [bindParser, hs] at h
  | some q =>
    have hh : next (a, q.1) q.2 = some (value, tail) := by simpa [bindParser, hs] using h
    exact (hq (a, q.1) q.2 value tail hh).trans (hp a bits q.1 q.2 hs)

theorem consumes_pureParser (f : α → β) : Consumes (pureParser f) := by
  intro a bits value tail h
  have hh : (f a, bits) = (value, tail) := Option.some.inj h
  have ht : bits = tail := congrArg Prod.snd hh
  rw [← ht]

theorem consumes_filterParser {f : α → β → Bool} {parser : α → Parser β}
    (hc : Consumes parser) : Consumes (filterParser f parser) := by
  intro a bits value tail h
  cases hp : parser a bits with
  | none => simp [filterParser, hp] at h
  | some q =>
    cases hf : f a q.1 with
    | false => simp [filterParser, hp, hf] at h
    | true =>
      have hh : q = (value, tail) := by simpa [filterParser, hp, hf] using h
      exact hc a bits value tail (hh ▸ hp)

theorem consumes_congr {p q : α → Parser β} (h : ∀ a bits, p a bits = q a bits)
    (hp : Consumes p) : Consumes q := fun a bits value tail hq => hp a bits value tail
  ((h a bits).trans hq)

section Machines

variable [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
  [Primcodable γ] [BitEncoding γ] [Inhabited β]

@[fun_prop] theorem polyTime_mapParser {f : α → β → γ} {parser : α → Parser β}
    (hf : PolyTime (fun p : α × β => f p.1 p.2))
    (hp : PolyTime (fun p : α × List Bool => parser p.1 p.2)) :
    PolyTime (fun p : α × List Bool => mapParser f parser p.1 p.2) := by
  unfold mapParser
  fun_prop

@[fun_prop] theorem polyTime_bindParser {parser : α → Parser β} {next : α × β → Parser γ}
    (hp : PolyTime (fun p : α × List Bool => parser p.1 p.2))
    (hq : PolyTime (fun p : (α × β) × List Bool => next p.1 p.2)) :
    PolyTime (fun p : α × List Bool => bindParser parser next p.1 p.2) := by
  unfold bindParser
  fun_prop

omit [Primcodable γ] [BitEncoding γ] in
@[fun_prop] theorem polyTime_filterParser {f : α → β → Bool} {parser : α → Parser β}
    (hf : PolyTime (fun p : α × β => f p.1 p.2))
    (hp : PolyTime (fun p : α × List Bool => parser p.1 p.2)) :
    PolyTime (fun p : α × List Bool => filterParser f parser p.1 p.2) := by
  unfold filterParser
  fun_prop

omit [Primcodable γ] [BitEncoding γ] [Inhabited β] in
@[fun_prop] theorem polyTime_pureParser {f : α → β} (hf : PolyTime f) :
    PolyTime (fun p : α × List Bool => pureParser f p.1 p.2) := by
  unfold pureParser
  fun_prop

omit [Primcodable γ] [BitEncoding γ] in
@[fun_prop] theorem polyTime_readAll {parser : α → Parser β}
    (hp : PolyTime (fun p : α × List Bool => parser p.1 p.2)) :
    PolyTime (fun p : α × List Bool => readAll (parser p.1) p.2) := by
  have hh : PolyTime (fun p : α × List Bool =>
      (parser p.1 p.2).bind fun q => bif decide (q.2 = []) then some q.1 else none) := by
    fun_prop
  exact PolyTime.of_eq hh fun p => by
    unfold readAll
    cases parser p.1 p.2 with
    | none => rfl
    | some q => rcases q with ⟨value, tail⟩; cases tail <;> rfl

end Machines

theorem readAll_map (p : Parser α) (f : α → β) (bits : List Bool) :
    readAll (fun b => (p b).map fun q => (f q.1, q.2)) bits =
      (readAll p bits).map f := by
  unfold readAll
  dsimp only
  cases p bits with
  | none => rfl
  | some q =>
    rcases q with ⟨value, tail⟩
    cases tail <;> rfl

theorem readMany_map (p : Parser α) (f : α → β) (count : ℕ) (bits : List Bool) :
    readMany (fun b => (p b).map fun q => (f q.1, q.2)) count bits =
      (readMany p count bits).map (fun q => (q.1.map f, q.2)) := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih =>
    simp only [readMany]
    cases p bits with
    | none => simp
    | some q =>
      obtain ⟨value, rest⟩ := q
      simp only [Option.map_some, ih]
      cases hs : readMany p count rest <;> simp [hs]

theorem readList_map (p : Parser α) (f : α → β) (bits : List Bool) :
    readList (fun b => (p b).map fun q => (f q.1, q.2)) bits =
      (readList p bits).map (fun q => (q.1.map f, q.2)) := by
  unfold readList
  cases readUnary bits with
  | none => simp
  | some q => simp [readMany_map]

theorem readVector_list (p : Parser α) (count : ℕ) (bits : List Bool) :
    (readVector p count bits).map (fun q => (List.ofFn q.1, q.2)) =
      readMany p count bits := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih =>
    simp only [readVector, readMany]
    cases p bits with
    | none => simp
    | some q =>
      obtain ⟨value, rest⟩ := q
      cases hs : readVector p count rest with
      | none =>
        have hm : readMany p count rest = none := by simpa [hs] using (ih rest).symm
        simp [hs, hm]
      | some q =>
        have hm : readMany p count rest = some (List.ofFn q.1, q.2) := by
          simpa [hs] using (ih rest).symm
        simp [hs, hm]

end TauCeti.BinaryCodec
