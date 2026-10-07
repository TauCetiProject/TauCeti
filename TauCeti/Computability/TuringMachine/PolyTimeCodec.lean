/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTimeNat
public import TauCeti.Computability.Encoding.BooleanList

/-!
# Polynomial-time binary parsers

Unary counts are read by a bounded fold. Binary indices are accumulated with
saturation at the supplied bound, so malformed bit strings cannot cause an
exponential unary allocation.
-/

@[expose] public section

namespace TauCeti.BinaryCodec

open Computability BitEncoding Turing

/-- Scan the initial unary prefix, retaining a flag for a missing terminator. -/
def unaryStep (q : ℕ × Bool) (b : Bool) : ℕ × Bool :=
  bif q.2 then (bif b then (q.1 + 1, true) else (q.1, false)) else q

theorem foldl_unaryStep_false (bits : List Bool) (n : ℕ) :
    bits.foldl unaryStep (n, false) = (n, false) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simpa [unaryStep] using ih

theorem foldl_unaryStep_add (bits : List Bool) (n c : ℕ) (b : Bool) :
    bits.foldl unaryStep (n + c, b) =
      let q := bits.foldl unaryStep (c, b)
      (n + q.1, q.2) := by
  induction bits generalizing c b with
  | nil => rfl
  | cons bit bits ih =>
    cases b <;> cases bit <;>
      simp only [List.foldl_cons, unaryStep, Bool.cond_false, Bool.cond_true] <;>
      simpa [Nat.add_assoc] using ih (b := _) (c := _)

/-- The bounded-fold implementation of the unary parser. -/
def unaryParser (bits : List Bool) : Option (ℕ × List Bool) :=
  let q := bits.foldl unaryStep (0, true)
  bif q.2 then none else some (q.1, bits.drop (q.1 + 1))

theorem unaryParser_eq_readUnary (bits : List Bool) : unaryParser bits = readUnary bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b with
    | false => simp [unaryParser, readUnary, unaryStep, foldl_unaryStep_false]
    | true =>
      have hs := foldl_unaryStep_add bits 1 0 true
      simp only [Nat.add_zero] at hs
      simp only [unaryParser, List.foldl_cons, unaryStep, Bool.cond_true] at ih ⊢
      rw [hs]
      cases h : bits.foldl unaryStep (0, true) with
      | mk n flag =>
        cases flag <;>
          simp [h, ← ih, readUnary, Nat.add_left_comm, Nat.add_comm]

@[fun_prop] theorem polyTime_readUnary : PolyTime (fun bits => readUnary bits) := by
  have hfold := PolyTime.foldl
    (g := fun (_ : Unit) q b => unaryStep q b) (by unfold unaryStep; fun_prop) 0
    fun u q b => by
      obtain ⟨n, flag⟩ := q
      cases flag <;> cases b <;>
        simp [unaryStep, length_enc_prod, length_enc_nat, enc_bool]
      all_goals omega
  have hw : PolyTime (fun bits : List Bool => ((), (0, true), bits)) := by fun_prop
  have hscan : PolyTime (fun bits : List Bool => bits.foldl unaryStep (0, true)) :=
    PolyTime.comp (g := fun p : Unit × (ℕ × Bool) × List Bool =>
      p.2.2.foldl unaryStep p.2.1) hfold hw
  have h : PolyTime unaryParser := by
    unfold unaryParser
    fun_prop
  exact PolyTime.of_eq h unaryParser_eq_readUnary

@[fun_prop] theorem polyTime_readBit : PolyTime (fun bits => readBit bits) := by
  have h : PolyTime (fun bits : List Bool => bits.head?.map fun b => (b, bits.tail)) := by
    fun_prop
  exact PolyTime.of_eq h fun bits => by cases bits <;> rfl

/-- Saturating binary accumulation. Values at or beyond the bound remain rejected. -/
def binaryStep (bound value : ℕ) (bit : Bool) : ℕ :=
  min bound (2 * value + bif bit then 1 else 0)

theorem binaryStep_le (bound value : ℕ) (bit : Bool) :
    binaryStep bound value bit ≤ bound :=
  Nat.min_le_left _ _

@[fun_prop] theorem polyTime_binaryStep :
    PolyTime (fun p : ℕ × ℕ × Bool => binaryStep p.1 p.2.1 p.2.2) := by
  unfold binaryStep
  fun_prop

@[fun_prop] theorem polyTime_binaryFold :
    PolyTime (fun p : ℕ × ℕ × List Bool => p.2.2.foldl (binaryStep p.1) p.2.1) := by
  exact PolyTime.foldl polyTime_binaryStep 1 fun bound value bit => by
    rw [length_enc_nat, length_enc_nat, length_enc_nat, pow_one]
    have := binaryStep_le bound value bit
    omega

/-- Parse an index as a natural; the range proof is checked before returning. -/
def indexParser (bound : ℕ) (bits : List Bool) : Option (ℕ × List Bool) :=
  let width := indexWidth bound
  let value := (bits.take width).foldl (binaryStep bound) 0
  bif decide (width ≤ bits.length) && decide (value < bound)
    then some (value, bits.drop width) else none

@[fun_prop] theorem polyTime_indexWidth : PolyTime indexWidth := by
  unfold indexWidth
  have hw : PolyTime (fun bound : ℕ => (1, (bound - 1).size)) := by fun_prop
  exact PolyTime.comp (g := fun p : ℕ × ℕ => max p.1 p.2) PolyTime.max hw

@[fun_prop] theorem polyTime_indexParser :
    PolyTime (fun p : ℕ × List Bool => indexParser p.1 p.2) := by
  have hf : PolyTime (fun p : ℕ × List Bool =>
      (p.2.take (indexWidth p.1)).foldl (binaryStep p.1) 0) :=
    PolyTime.comp (f := fun p : ℕ × List Bool => (p.1, 0, p.2.take (indexWidth p.1)))
      polyTime_binaryFold (by fun_prop)
  have hw : PolyTime (fun p : ℕ × List Bool => indexWidth p.1) :=
    PolyTime.comp polyTime_indexWidth PolyTime.fst
  have hb : PolyTime (fun p : ℕ × List Bool =>
      decide (indexWidth p.1 ≤ p.2.length) &&
        decide ((p.2.take (indexWidth p.1)).foldl (binaryStep p.1) 0 < p.1)) :=
    PolyTime.comp PolyTime.and (PolyTime.pair
      (PolyTime.le hw (by fun_prop)) (PolyTime.lt hf PolyTime.fst))
  have hs := PolyTime.comp PolyTime.some (PolyTime.pair hf
    (show PolyTime (fun p : ℕ × List Bool => p.2.drop (indexWidth p.1)) from by fun_prop))
  exact PolyTime.comp PolyTime.cond (PolyTime.pair hb (PolyTime.pair hs (PolyTime.const none)))

theorem binaryStep_min (bound value : ℕ) (bit : Bool) :
    binaryStep bound (min bound value) bit = min bound (2 * value + bif bit then 1 else 0) := by
  unfold binaryStep
  cases bit <;> simp only [Bool.cond_false, Bool.cond_true] <;>
    omega

/-- The unrestricted binary value, used only to specify the saturating computation. -/
def binaryValue (bits : List Bool) : ℕ :=
  bits.foldl (fun value bit => 2 * value + bif bit then 1 else 0) 0

theorem binaryFold_eq_min (bound : ℕ) (bits : List Bool) (value : ℕ) :
    bits.foldl (binaryStep bound) (min bound value) =
      min bound (bits.foldl (fun v b => 2 * v + bif b then 1 else 0) value) := by
  induction bits generalizing value with
  | nil => rfl
  | cons bit bits ih => rw [List.foldl_cons, binaryStep_min, ih, List.foldl_cons]

theorem readBitsLE_length (bits : List Bool) :
    readBitsLE bits.length bits =
      some (bits.foldr (fun bit value => (bif bit then 1 else 0) + 2 * value) 0, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [readBitsLE, ih]

theorem readBits_eq (width : ℕ) (bits : List Bool) :
    readBits width bits =
      if width ≤ bits.length then some (binaryValue (bits.take width), bits.drop width)
        else none := by
  by_cases h : width ≤ bits.length
  · have hl : (bits.take width).reverse.length = width := by simp [h]
    have hr := readBitsLE_length (bits.take width).reverse
    rw [hl] at hr
    simp only [readBits, h, ite_true, hr, Option.pure_def]
    change some (_, bits.drop width) = some (_, bits.drop width)
    simp only [binaryValue, List.foldl_eq_foldr_reverse, Nat.add_comm]
  · simp [readBits, h]

theorem indexParser_eq_readIndex (bound : ℕ) (bits : List Bool) :
    indexParser bound bits = (readIndex bound bits).map (fun p => (p.1.val, p.2)) := by
  have hb : (bits.take (indexWidth bound)).foldl (binaryStep bound) 0 =
      min bound (binaryValue (bits.take (indexWidth bound))) := by
    simpa [binaryValue] using binaryFold_eq_min bound (bits.take (indexWidth bound)) 0
  simp only [indexParser, hb, readIndex, readBits_eq]
  by_cases hw : indexWidth bound ≤ bits.length
  · simp only [hw, decide_true, Bool.true_and, ite_true]
    by_cases hv : binaryValue (bits.take (indexWidth bound)) < bound
    · simp [hv, hv.le]
    · simp [hv]
  · simp [hw]

end TauCeti.BinaryCodec
