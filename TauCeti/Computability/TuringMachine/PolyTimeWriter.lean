/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTimeCodec

/-!
# Polynomial-time writers for the binary wire format

Binary output is produced by a clocked halving loop. Its unary numerical state
never grows, and its output grows by one bit per iteration. No variable power
of two is constructed by the machine.
-/

@[expose] public section

namespace Turing.PolyTime

open Computability BitEncoding TauCeti.BinaryCodec

variable {α β γ : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
  [Primcodable γ] [BitEncoding γ]

@[fun_prop] theorem flatMap {f : α → β → List γ} {l : α → List β}
    (hf : PolyTime fun p : α × β => f p.1 p.2) (hl : PolyTime l) :
    PolyTime fun a => (l a).flatMap (f a) := by
  simpa only [List.flatMap_def] using comp flatten (map₂ hf hl)

@[fun_prop] theorem writeUnary : PolyTime TauCeti.BinaryCodec.writeUnary := by
  unfold TauCeti.BinaryCodec.writeUnary
  fun_prop

/-- Append the current low bit and halve the remaining unary value. -/
def writeStep (p : ℕ × List Bool) : ℕ × List Bool :=
  (p.1 / 2, p.2 ++ [decide (p.1 % 2 = 1)])

theorem writeStep_iterate_snd (width value : ℕ) (acc : List Bool) :
    (writeStep^[width] (value, acc)).2 = acc ++ writeBitsLE width value := by
  induction width generalizing value acc with
  | zero => simp [writeBitsLE]
  | succ width ih =>
    rw [Function.iterate_succ_apply, writeStep, ih]
    simp [writeBitsLE, List.append_assoc]

@[fun_prop] theorem writeBitsLE :
    PolyTime (fun p : ℕ × ℕ => TauCeti.BinaryCodec.writeBitsLE p.1 p.2) := by
  have hs : PolyTime (fun p : Unit × (ℕ × List Bool) => writeStep p.2) := by
    unfold writeStep
    fun_prop
  have hI := iterate₂ (g := fun _ : Unit => writeStep) hs 2 fun (u : Unit) p => by
    have hdiv := Nat.div_le_self p.1 2
    have hu : (enc u).length = 0 := rfl
    have hp : (enc p).length = 2 * p.1 + 1 + (4 * p.2.length + 1) := by
      change (enc (p.1, p.2)).length = _
      rw [length_enc_prod, length_enc_nat, length_enc_bits]
    rw [hp, hu]
    simp only [writeStep, length_enc_prod, length_enc_nat, length_enc_bits,
      List.length_append, List.length_singleton]
    omega
  have hw : PolyTime (fun p : ℕ × ℕ => ((), p.1, (p.2, ([] : List Bool)))) := by
    fun_prop
  exact of_eq (comp snd (comp hI hw)) fun p => by
    simpa only [List.nil_append] using writeStep_iterate_snd p.1 p.2 []

@[fun_prop] theorem writeBits :
    PolyTime (fun p : ℕ × ℕ => TauCeti.BinaryCodec.writeBits p.1 p.2) :=
  comp reverse writeBitsLE

@[fun_prop] theorem indexWidth : PolyTime TauCeti.BinaryCodec.indexWidth := by
  unfold TauCeti.BinaryCodec.indexWidth
  fun_prop

/-- Write an unbounded natural using the declared index width. -/
def writeNatIndex (bound value : ℕ) : List Bool :=
  TauCeti.BinaryCodec.writeBits (TauCeti.BinaryCodec.indexWidth bound) value

@[fun_prop] theorem writeNatIndex_polyTime :
    PolyTime (fun p : ℕ × ℕ => writeNatIndex p.1 p.2) := by
  unfold writeNatIndex
  fun_prop

theorem writeNatIndex_eq_writeIndex {bound : ℕ} (i : Fin bound) :
    writeNatIndex bound i.val = writeIndex i := rfl

@[fun_prop] theorem writeList {f : α → β → List Bool} {l : α → List β}
    (hf : PolyTime fun p : α × β => f p.1 p.2) (hl : PolyTime l) :
    PolyTime fun a => TauCeti.BinaryCodec.writeList (f a) (l a) := by
  unfold TauCeti.BinaryCodec.writeList
  fun_prop

/-- The vector writer is the concatenation of the listed vector entries. -/
theorem writeVector_eq_flatMap {γ : Type} (f : γ → List Bool)
    {n : ℕ} (v : Fin n → γ) :
    writeVector f v = (List.ofFn v).flatMap f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [TauCeti.BinaryCodec.writeVector, List.ofFn_succ, List.flatMap_cons, ih]
    rfl

end Turing.PolyTime
