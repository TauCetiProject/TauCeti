/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Fin.Tuple.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Self-delimiting binary data

Counts are unary (`true` repeated, then `false`). Indices use exactly
`max 1 (size (bound - 1))` bits, most significant bit first. Parsers return
the unused suffix, so a caller can reject trailing data. Index parsing
rejects out-of-range values, including every index into an empty collection.
-/

@[expose] public section

namespace TauCeti.BinaryCodec

/-- A parser returning a decoded value and the unconsumed Boolean suffix. -/
abbrev Parser (α : Type) := List Bool → Option (α × List Bool)

/-- Encode a natural number as `n` true bits followed by a false terminator. -/
def writeUnary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Read a false-terminated unary natural, rejecting a missing terminator. -/
def readUnary : Parser ℕ
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readUnary rest
      pure (n + 1, tail)

theorem readUnary_writeUnary (n : ℕ) (tail : List Bool) :
    readUnary (writeUnary n ++ tail) = some (n, tail) := by
  induction n with
  | zero => simp [writeUnary, readUnary]
  | succ n ih =>
    have hcons : writeUnary (n + 1) ++ tail = true :: (writeUnary n ++ tail) := by
      simp [writeUnary, List.replicate_succ, List.append_assoc]
    rw [hcons]
    simp only [readUnary]
    rw [ih]
    rfl

theorem readUnary_size {bits tail : List Bool} {n : ℕ}
    (h : readUnary bits = some (n, tail)) :
    n + 1 + tail.length ≤ bits.length := by
  induction bits generalizing n tail with
  | nil => simp [readUnary] at h
  | cons bit bits ih =>
    cases bit with
    | false =>
      simp only [readUnary, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [List.length_cons]
      omega
    | true =>
      simp only [readUnary] at h
      cases hr : readUnary bits with
      | none => simp [hr] at h
      | some pair =>
        rcases pair with ⟨m, rest⟩
        simp only [hr, Option.pure_def] at h
        rcases h with ⟨rfl, rfl⟩
        have hsize := ih hr
        dsimp at hsize ⊢
        omega

/-- Encode the lowest `width` bits of a natural in little-endian order. -/
def writeBitsLE : ℕ → ℕ → List Bool
  | 0, _ => []
  | width + 1, value => decide (value % 2 = 1) :: writeBitsLE width (value / 2)

/-- Read exactly `width` bits as a little-endian natural. -/
def readBitsLE : ℕ → Parser ℕ
  | 0, bits => some (0, bits)
  | _ + 1, [] => none
  | width + 1, bit :: bits => do
      let (value, tail) ← readBitsLE width bits
      pure ((if bit then 1 else 0) + 2 * value, tail)

theorem writeBitsLE_length (width value : ℕ) :
    (writeBitsLE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [writeBitsLE, ih]

theorem readBitsLE_writeBitsLE (width value : ℕ) (hvalue : value < 2 ^ width)
    (tail : List Bool) :
    readBitsLE width (writeBitsLE width value ++ tail) = some (value, tail) := by
  induction width generalizing value with
  | zero =>
    have hv : value = 0 := by simpa using hvalue
    simp [writeBitsLE, readBitsLE, hv]
  | succ width ih =>
    have hhalf : value / 2 < 2 ^ width := by
      rw [Nat.pow_succ] at hvalue
      omega
    have hvalue' : (if value % 2 = 1 then 1 else 0) + 2 * (value / 2) = value := by
      have := Nat.mod_lt value (by decide : 0 < 2)
      split <;> omega
    simp [writeBitsLE, readBitsLE, ih _ hhalf, hvalue']

/-- Encode the lowest `width` bits of a natural in big-endian order. -/
def writeBits (width value : ℕ) : List Bool := (writeBitsLE width value).reverse

/-- Read exactly `width` bits as a big-endian natural. -/
def readBits (width : ℕ) : Parser ℕ := fun bits =>
  if width ≤ bits.length then do
    let (value, _) ← readBitsLE width (bits.take width).reverse
    pure (value, bits.drop width)
  else none

theorem writeBits_length (width value : ℕ) :
    (writeBits width value).length = width := by
  simp [writeBits, writeBitsLE_length]

theorem readBits_writeBits (width value : ℕ) (hvalue : value < 2 ^ width)
    (tail : List Bool) :
    readBits width (writeBits width value ++ tail) = some (value, tail) := by
  have hlength : (writeBitsLE width value).reverse.length = width := by
    simp [writeBitsLE_length]
  have hread := readBitsLE_writeBitsLE width value hvalue []
  simp only [List.append_nil] at hread
  simp [readBits, writeBits, hlength, hread]

/-- The positive bit width needed to encode indices below `bound`. -/
def indexWidth (bound : ℕ) : ℕ := max 1 (bound - 1).size

theorem index_lt_pow {bound : ℕ} (i : Fin bound) :
    i.val < 2 ^ indexWidth bound := by
  apply Nat.size_le.mp
  exact (Nat.size_le_size (by omega : i.val ≤ bound - 1)).trans (le_max_right _ _)

/-- Encode a bounded index using its bound-dependent bit width. -/
def writeIndex {bound : ℕ} (i : Fin bound) : List Bool :=
  writeBits (indexWidth bound) i.val

/-- Read a bounded index, rejecting values outside the specified bound. -/
def readIndex (bound : ℕ) : Parser (Fin bound) := fun bits => do
  let (value, tail) ← readBits (indexWidth bound) bits
  if h : value < bound then pure (⟨value, h⟩, tail) else none

theorem readIndex_writeIndex {bound : ℕ} (i : Fin bound) (tail : List Bool) :
    readIndex bound (writeIndex i ++ tail) = some (i, tail) := by
  simp [readIndex, writeIndex, readBits_writeBits _ _ (index_lt_pow i), i.isLt]

/-- Read one Boolean bit, rejecting an empty input. -/
def readBit : Parser Bool
  | [] => none
  | bit :: tail => some (bit, tail)

/-- Run a parser exactly `count` times, rejecting any failed element. -/
def readMany {α : Type} (parser : Parser α) : ℕ → Parser (List α)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (value, rest) ← parser bits
      let (values, tail) ← readMany parser count rest
      pure (value :: values, tail)

theorem readMany_write {α : Type} (parser : Parser α) (encoder : α → List Bool)
    (hround : ∀ value tail, parser (encoder value ++ tail) = some (value, tail))
    (values : List α) (tail : List Bool) :
    readMany parser values.length (values.flatMap encoder ++ tail) =
      some (values, tail) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp [readMany, List.append_assoc, hround, ih]

/-- Encode a list by a unary length followed by concatenated element encodings. -/
def writeList {α : Type} (encoder : α → List Bool) (values : List α) : List Bool :=
  writeUnary values.length ++ values.flatMap encoder

/-- Read a unary length and then that many encoded elements. -/
def readList {α : Type} (parser : Parser α) : Parser (List α) := fun bits => do
  let (count, rest) ← readUnary bits
  readMany parser count rest

theorem readList_writeList {α : Type} (parser : Parser α) (encoder : α → List Bool)
    (hround : ∀ value tail, parser (encoder value ++ tail) = some (value, tail))
    (values : List α) (tail : List Bool) :
    readList parser (writeList encoder values ++ tail) = some (values, tail) := by
  simp [readList, writeList, List.append_assoc, readUnary_writeUnary,
    readMany_write parser encoder hround]

/-- Encode a vector by concatenating its entries in increasing index order. -/
def writeVector {α : Type} (encoder : α → List Bool) :
    {count : ℕ} → (Fin count → α) → List Bool
  | 0, _ => []
  | _ + 1, values => encoder (values 0) ++ writeVector encoder (Fin.tail values)

/-- Read the specified number of entries as a finite-indexed vector. -/
def readVector {α : Type} (parser : Parser α) : (count : ℕ) → Parser (Fin count → α)
  | 0, bits => some (Fin.elim0, bits)
  | count + 1, bits => do
      let (value, rest) ← parser bits
      let (values, tail) ← readVector parser count rest
      pure (Fin.cons value values, tail)

theorem readVector_writeVector {α : Type} (parser : Parser α)
    (encoder : α → List Bool)
    (hround : ∀ value tail, parser (encoder value ++ tail) = some (value, tail))
    {count : ℕ} (values : Fin count → α) (tail : List Bool) :
    readVector parser count (writeVector encoder values ++ tail) = some (values, tail) := by
  induction count with
  | zero =>
    have h : Fin.elim0 = values := by funext i; exact i.elim0
    simp [readVector, writeVector, h]
  | succ count ih =>
    simp [readVector, writeVector, List.append_assoc, hround, ih, Fin.cons_self_tail]

/-- Read one value and reject a nonempty trailing suffix. -/
def readAll {α : Type} (parser : Parser α) (bits : List Bool) : Option α := do
  let (value, tail) ← parser bits
  if tail.isEmpty then pure value else none

theorem readAll_write {α : Type} (parser : Parser α) (encoder : α → List Bool)
    (hround : ∀ value tail, parser (encoder value ++ tail) = some (value, tail))
    (value : α) :
    readAll parser (encoder value) = some value := by
  have h := hround value []
  simp only [List.append_nil] at h
  simp [readAll, h]


end TauCeti.BinaryCodec
