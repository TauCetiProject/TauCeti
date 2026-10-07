/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTimeCodec

/-!
# Polynomial-time parser repetition

A parser may return variable-size entries. Its output-length bound and a cap on
the original input bound the accumulator throughout repetition. Failure is an
absorbing state. The construction therefore bounds successful and rejected runs.
-/

@[expose] public section

namespace TauCeti.BinaryCodec

open Computability BitEncoding Turing

/-- Successful parsing never increases the unconsumed input. -/
def Consumes {α β : Type} (parser : α → Parser β) : Prop :=
  ∀ a bits value tail, parser a bits = some (value, tail) → tail.length ≤ bits.length

theorem consumes_readUnary : Consumes (fun _ : Unit => readUnary) :=
  fun _ _ _ _ h => by have := readUnary_size h; omega

theorem consumes_readBit : Consumes (fun _ : Unit => readBit) := by
  intro _ bits value tail h
  cases bits with
  | nil => simp [readBit] at h
  | cons b bits =>
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    simp

theorem consumes_indexParser : Consumes indexParser := by
  intro bound bits value tail h
  unfold indexParser at h
  dsimp only at h
  cases hflag : decide (indexWidth bound ≤ bits.length) &&
      decide ((bits.take (indexWidth bound)).foldl (binaryStep bound) 0 < bound)
  · simp [hflag] at h
  · simp only [hflag, Bool.cond_true] at h
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    simp

variable {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
  [Inhabited β]

/-- One parser call, with the unconsumed input capped at the original length. -/
def manyStep (parser : α → Parser β) (p : α × ℕ)
    (o : Option (List β × List Bool)) : Option (List β × List Bool) :=
  o.bind fun q => (parser p.1 (q.2.take p.2)).map fun r => (r.1 :: q.1, r.2)

@[fun_prop] theorem polyTime_manyStep {parser : α → Parser β}
    (hp : PolyTime (fun p : α × List Bool => parser p.1 p.2)) :
    PolyTime (fun p : (α × ℕ) × Option (List β × List Bool) => manyStep parser p.1 p.2) := by
  unfold manyStep
  fun_prop

omit [Inhabited β] in
theorem manyStep_growth {parser : α → Parser β}
    (hp : PolyTime (fun p : α × List Bool => parser p.1 p.2)) (hc : Consumes parser) :
    ∃ c, ∀ p o, (enc (manyStep parser p o)).length ≤
      (enc o).length + ((enc p).length + 2) ^ c := by
  unfold PolyTime at hp
  obtain ⟨m⟩ := hp
  obtain ⟨d, hd⟩ := Turing.BitMachines.length_enc_le_of_tm m
  refine ⟨3 * d + 3, fun ⟨a, N⟩ o => ?_⟩
  cases o with
  | none =>
    change 1 ≤ 1 + _
    omega
  | some q =>
    obtain ⟨acc, bits⟩ := q
    have hx : 3 ≤ (enc (a, N)).length + 2 := by
      rw [length_enc_prod, length_enc_nat]
      omega
    cases hr : parser a (bits.take N) with
    | none =>
      simp only [manyStep, Option.bind_some, hr, Option.map_none, enc_none,
        enc_some, List.length_cons, List.length_nil]
      omega
    | some r =>
      obtain ⟨value, tail⟩ := r
      have ht := hc a (bits.take N) value tail hr
      have ho := hd (a, bits.take N)
      change (enc (parser a (bits.take N))).length ≤ _ at ho
      rw [hr, enc_some, List.length_cons, length_enc_prod] at ho
      have hi : (enc (a, bits.take N)).length + 2 ≤ ((enc (a, N)).length + 2) ^ 3 := by
        rw [length_enc_prod, length_enc_bits, length_enc_prod, length_enc_nat,
          List.length_take]
        have ht := Nat.min_le_left N bits.length
        have hb : 3 ≤ 2 * (enc a).length + 1 + N + 2 := by omega
        have hsq := Nat.pow_le_pow_left hb 2
        norm_num at hsq
        simp only [pow_succ, pow_zero] at hsq ⊢
        nlinarith
      have hv : (enc value).length ≤ ((enc (a, N)).length + 2) ^ (3 * d) := by
        have hh := Nat.pow_le_pow_left hi d
        rw [← pow_mul] at hh
        omega
      have h1 : 1 ≤ ((enc (a, N)).length + 2) ^ (3 * d) := one_le_pow₀ (by omega)
      have h8 : 8 ≤ ((enc (a, N)).length + 2) ^ 3 :=
        (by norm_num : 8 ≤ 3 ^ 3).trans (Nat.pow_le_pow_left hx 3)
      have hh := Nat.mul_le_mul_right (((enc (a, N)).length + 2) ^ (3 * d)) h8
      simp only [manyStep, Option.bind_some, hr, Option.map_some, enc_some,
        List.length_cons, length_enc_prod, length_enc_cons, length_enc_bits,
        length_enc_nat] at hv h1 hh ⊢
      rw [pow_add]
      simp only [List.length_take] at ht
      have := Nat.min_le_right N bits.length
      nlinarith

omit [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β] [Inhabited β] in
theorem iterate_manyStep {parser : α → Parser β} (hc : Consumes parser)
    (a : α) (N count : ℕ) (acc : List β) (bits : List Bool) (hb : bits.length ≤ N) :
    (manyStep parser (a, N))^[count] (some (acc, bits)) =
      (readMany (parser a) count bits).map (fun r => (r.1.reverse ++ acc, r.2)) := by
  induction count generalizing acc bits with
  | zero => simp [readMany]
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    simp only [manyStep, Option.bind_some, List.take_of_length_le hb]
    cases hr : parser a bits with
    | none =>
      simp only [Option.map_none]
      rw [Function.iterate_fixed (by rfl)]
      simp [readMany, hr]
    | some r =>
      obtain ⟨value, rest⟩ := r
      simp only [Option.map_some]
      rw [ih _ _ ((hc a bits value rest hr).trans hb)]
      simp only [readMany, hr]
      cases hs : readMany (parser a) count rest <;>
        simp [hs, List.reverse_cons, List.append_assoc]

@[fun_prop] theorem polyTime_readMany {parser : α → Parser β}
    (hp : PolyTime (fun p : α × List Bool => parser p.1 p.2)) (hc : Consumes parser) :
    PolyTime (fun p : α × ℕ × List Bool => readMany (parser p.1) p.2.1 p.2.2) := by
  obtain ⟨c, hb⟩ := manyStep_growth hp hc
  have hI := PolyTime.iterate₂ (polyTime_manyStep hp) c hb
  have hw : PolyTime (fun p : α × ℕ × List Bool =>
      ((p.1, p.2.2.length), p.2.1, some (([] : List β), p.2.2))) := by fun_prop
  have h : PolyTime (fun p : α × ℕ × List Bool =>
      ((manyStep parser (p.1, p.2.2.length))^[p.2.1]
        (some ([], p.2.2))).map (fun r => (r.1.reverse, r.2))) := by
    exact PolyTime.option_map (by fun_prop) (PolyTime.comp hI hw)
  exact PolyTime.of_eq h fun p => by
    rw [iterate_manyStep hc _ _ _ _ _ le_rfl]
    cases readMany (parser p.1) p.2.1 p.2.2 <;> simp

omit [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β] [Inhabited β] in
theorem consumes_readMany {parser : α → Parser β} (hc : Consumes parser) :
    Consumes (fun p : α × ℕ => readMany (parser p.1) p.2) := by
  rintro ⟨a, count⟩ bits values tail h
  induction count generalizing bits values with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact le_rfl
  | succ count ih =>
    simp only [readMany] at h
    cases hp : parser a bits with
    | none => simp [hp] at h
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      have hh : (do
          let (values, tail) ← readMany (parser a) count rest
          pure (value :: values, tail)) = some (values, tail) := by simpa [hp] using h
      cases hr : readMany (parser a) count rest with
      | none => simp [hr] at hh
      | some pair =>
        obtain ⟨values', tail'⟩ := pair
        have hh' : value :: values' = values ∧ tail' = tail := by simpa [hr] using hh
        obtain ⟨rfl, rfl⟩ := hh'
        exact (ih rest values' hr).trans (hc a bits value rest hp)

@[fun_prop] theorem polyTime_readList {parser : α → Parser β}
    (hp : PolyTime (fun p : α × List Bool => parser p.1 p.2)) (hc : Consumes parser) :
    PolyTime (fun p : α × List Bool => readList (parser p.1) p.2) := by
  have hm := polyTime_readMany hp hc
  change PolyTime (fun p : α × List Bool =>
    (readUnary p.2).bind fun q => readMany (parser p.1) q.1 q.2)
  apply PolyTime.option_bind
  · have hw : PolyTime (fun p : (α × List Bool) × (ℕ × List Bool) =>
        (p.1.1, p.2.1, p.2.2)) := by fun_prop
    exact PolyTime.comp hm hw
  · exact PolyTime.comp polyTime_readUnary PolyTime.snd

omit [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β] [Inhabited β] in
theorem consumes_readList {parser : α → Parser β} (hc : Consumes parser) :
    Consumes (fun a => readList (parser a)) := by
  intro a bits values tail h
  simp only [readList] at h
  cases hu : readUnary bits with
  | none => simp [hu] at h
  | some pair =>
    obtain ⟨count, rest⟩ := pair
    simp only [hu] at h
    change readMany (parser a) count rest = some (values, tail) at h
    exact (consumes_readMany hc (a, count) rest values tail h).trans
      (by have := readUnary_size hu; omega)

end TauCeti.BinaryCodec
