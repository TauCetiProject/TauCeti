/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.Encoding.BooleanList
public import TauCeti.GroupTheory.Perm.Certificates.Check

/-!
# Raw binary certificates and their verified interpretation

This implements the wire format in the proposal. An input has a unary degree,
a unary generator count, and forward-image tables. A certificate has its tag,
ambient words, a point mask, a base point, one word per complement point in
increasing order, and (for group-equality claims) conjugate factors.

The parser validates every table and index and rejects unused suffixes.
Conjugators and subgroup generators are interpreted from ambient words, so
their ambient-group membership is proved during decoding.
-/

open Equiv
open TauCeti.BinaryCodec TauCeti.FinitePermutation TauCeti.CertifiedPermutation

@[expose] public section

namespace TauCeti.CertificateWire

/-- Encode a bounded generator index followed by an inversion bit. -/
def writeLetter {size : ℕ} (letter : Fin size × Bool) : List Bool :=
  writeIndex letter.1 ++ [letter.2]

/-- Read a bounded generator index followed by an inversion bit. -/
def readLetter (size : ℕ) : Parser (Fin size × Bool) := fun bits => do
  let (index, rest) ← readIndex size bits
  let (inverted, tail) ← readBit rest
  pure ((index, inverted), tail)

theorem readLetter_writeLetter {size : ℕ} (letter : Fin size × Bool) (tail : List Bool) :
    readLetter size (writeLetter letter ++ tail) = some (letter, tail) := by
  simp [readLetter, writeLetter, List.append_assoc, readIndex_writeIndex, readBit]

/-- Encode a signed word with its unary length prefix. -/
def writeWord {size : ℕ} (word : Word size) : List Bool := writeList writeLetter word

/-- Read a signed word over the specified number of generators. -/
def readWord (size : ℕ) : Parser (Word size) := readList (readLetter size)

theorem readWord_writeWord {size : ℕ} (word : Word size) (tail : List Bool) :
    readWord size (writeWord word ++ tail) = some (word, tail) :=
  readList_writeList _ _ readLetter_writeLetter _ _

/-- Encode a permutation by its forward table in increasing point order. -/
def writePermutation {degree : ℕ} (g : Perm (Fin degree)) : List Bool :=
  writeVector writeIndex g

/-- Read a forward table and reject repeated entries before computing its inverse. -/
def readPermutation (degree : ℕ) : Parser (Perm (Fin degree)) := fun bits => do
  let (table, tail) ← readVector (readIndex degree) degree bits
  if h : Function.Injective table then
    pure (permutationOfTable table h, tail)
  else none

theorem readPermutation_writePermutation {degree : ℕ}
    (g : Perm (Fin degree)) (tail : List Bool) :
    readPermutation degree (writePermutation g ++ tail) = some (g, tail) := by
  simp [readPermutation, writePermutation, readVector_writeVector _ _ readIndex_writeIndex,
    g.injective, permutationOfTable_roundtrip]

/-- A degree and a list of permutations on the corresponding finite point set. -/
abbrev GroupData := (degree : ℕ) × List (Perm (Fin degree))

/-- Encode the degree and the length-prefixed generator tables. -/
def writeGroup (group : GroupData) : List Bool :=
  writeUnary group.1 ++ writeList writePermutation group.2

/-- Read a degree and the length-prefixed permutation generator tables. -/
def readGroup : Parser GroupData := fun bits => do
  let (degree, rest) ← readUnary bits
  let (gs, tail) ← readList (readPermutation degree) rest
  pure (⟨degree, gs⟩, tail)

theorem readGroup_writeGroup (group : GroupData) (tail : List Bool) :
    readGroup (writeGroup group ++ tail) = some (group, tail) := by
  rcases group with ⟨degree, gs⟩
  simp [readGroup, writeGroup, List.append_assoc, readUnary_writeUnary,
    readList_writeList _ _ readPermutation_writePermutation]

/-- Encode double transitivity, alternating, and symmetric claims by `00`, `01`, and `10`. -/
def writeClaim : Claim → List Bool
  | .doublyTransitive => [false, false]
  | .alternating => [false, true]
  | .symmetric => [true, false]

/-- Read a two-bit claim tag, rejecting the reserved tag `11`. -/
def readClaim : Parser Claim
  | false :: false :: tail => some (.doublyTransitive, tail)
  | false :: true :: tail => some (.alternating, tail)
  | true :: false :: tail => some (.symmetric, tail)
  | _ => none

theorem readClaim_writeClaim (claim : Claim) (tail : List Bool) :
    readClaim (writeClaim claim ++ tail) = some (claim, tail) := by
  cases claim <;> rfl

/-- A word for an ambient conjugator and a signed subgroup generator. -/
structure RawFactor (ambientSize subgroupSize : ℕ) where
  /-- A signed word over the ambient generators for the conjugating element. -/
  conjugator : Word ambientSize
  /-- The position of the subgroup generator to conjugate. -/
  generatorIndex : Fin subgroupSize
  /-- Whether to invert the selected subgroup generator. -/
  inverted : Bool

/-- Encode a normal-closure factor as a conjugator word and a signed generator index. -/
def writeFactor {ambientSize subgroupSize : ℕ} (factor : RawFactor ambientSize subgroupSize) :
    List Bool :=
  writeWord factor.conjugator ++ writeIndex factor.generatorIndex ++ [factor.inverted]

/-- Read a conjugator word and a signed generator index using their respective bounds. -/
def readFactor (ambientSize subgroupSize : ℕ) : Parser (RawFactor ambientSize subgroupSize) :=
  fun bits => do
    let (conjugator, rest) ← readWord ambientSize bits
    let (index, rest) ← readIndex subgroupSize rest
    let (inverted, tail) ← readBit rest
    pure (⟨conjugator, index, inverted⟩, tail)

theorem readFactor_writeFactor {ambientSize subgroupSize : ℕ}
    (factor : RawFactor ambientSize subgroupSize) (tail : List Bool) :
    readFactor ambientSize subgroupSize (writeFactor factor ++ tail) = some (factor, tail) := by
  simp [readFactor, writeFactor, List.append_assoc, readWord_writeWord,
    readIndex_writeIndex, readBit]

/-- The type of cycle factors needed by each supported claim. -/
def FactorsFor (claim : Claim) (ambientSize subgroupSize : ℕ) : Type :=
  match claim with
  | .doublyTransitive => Unit
  | _ => List (RawFactor ambientSize subgroupSize)

/-- Extract the cycle-factor list; double-transitivity certificates need no factors. -/
def factorList {ambientSize subgroupSize : ℕ} :
    (claim : Claim) → FactorsFor claim ambientSize subgroupSize →
      List (RawFactor ambientSize subgroupSize)
  | .doublyTransitive, _ => []
  | .alternating, factors => factors
  | .symmetric, factors => factors

/-- Encode exactly the cycle-factor payload required by the claim. -/
def writeFactors {ambientSize subgroupSize : ℕ} :
    (claim : Claim) → FactorsFor claim ambientSize subgroupSize → List Bool
  | .doublyTransitive, _ => []
  | .alternating, factors => writeList writeFactor factors
  | .symmetric, factors => writeList writeFactor factors

/-- Read exactly the cycle-factor payload required by the claim. -/
def readFactors (ambientSize subgroupSize : ℕ) :
    (claim : Claim) → Parser (FactorsFor claim ambientSize subgroupSize)
  | .doublyTransitive => fun bits => some ((), bits)
  | .alternating => readList (readFactor ambientSize subgroupSize)
  | .symmetric => readList (readFactor ambientSize subgroupSize)

theorem readFactors_writeFactors {ambientSize subgroupSize : ℕ}
    (claim : Claim) (factors : FactorsFor claim ambientSize subgroupSize) (tail : List Bool) :
    readFactors ambientSize subgroupSize claim (writeFactors claim factors ++ tail) =
      some (factors, tail) := by
  cases claim with
  | doublyTransitive => cases factors; rfl
  | alternating =>
    exact readList_writeList _ _ readFactor_writeFactor _ _
  | symmetric =>
    exact readList_writeList _ _ readFactor_writeFactor _ _

/-- List the points outside a Boolean fixed-set mask in increasing index order. -/
def complement {degree : ℕ} (mask : Fin degree → Bool) : List (Fin degree) :=
  (List.finRange degree).filter fun x => !mask x

/-- The finite word, mask, orbit, and claim data of an encoded certificate. -/
structure RawCertificate (degree ambientSize : ℕ) where
  /-- The property asserted of the normal closure. -/
  claim : Claim
  /-- Words over the ambient generators defining the subgroup generators. -/
  generatorWords : List (Word ambientSize)
  /-- A Boolean mask for the pointwise fixed set. -/
  mask : Fin degree → Bool
  /-- The starting point for the orbit witnesses. -/
  base : Fin degree
  /-- An orbit word for each point in the complement, in increasing point order. -/
  orbitWords : Fin (complement mask).length → Word generatorWords.length
  /-- The normal-closure product required by the claim; absent for double transitivity. -/
  cycleFactors : FactorsFor claim ambientSize generatorWords.length

/-- Encode a raw certificate with the canonical Boolean wire format. -/
def writeCertificate {degree ambientSize : ℕ} (c : RawCertificate degree ambientSize) :
    List Bool :=
  writeClaim c.claim ++ writeList writeWord c.generatorWords ++
    writeVector (fun bit => [bit]) c.mask ++ writeIndex c.base ++
    writeVector writeWord c.orbitWords ++ writeFactors c.claim c.cycleFactors

/-- Read a raw certificate for the specified degree and ambient generator count. -/
def readCertificate (degree ambientSize : ℕ) : Parser (RawCertificate degree ambientSize) :=
  fun bits => do
    let (claim, rest) ← readClaim bits
    let (generatorWords, rest) ← readList (readWord ambientSize) rest
    let (mask, rest) ← readVector readBit degree rest
    let (base, rest) ← readIndex degree rest
    let (orbitWords, rest) ←
      readVector (readWord generatorWords.length) (complement mask).length rest
    let (cycleFactors, tail) ← readFactors ambientSize generatorWords.length claim rest
    pure (⟨claim, generatorWords, mask, base, orbitWords, cycleFactors⟩, tail)

theorem readCertificate_writeCertificate {degree ambientSize : ℕ}
    (c : RawCertificate degree ambientSize) (tail : List Bool) :
    readCertificate degree ambientSize (writeCertificate c ++ tail) = some (c, tail) := by
  rcases c with ⟨claim, generatorWords, mask, base, orbitWords, factors⟩
  simp [readCertificate, writeCertificate, List.append_assoc, readClaim_writeClaim,
    readList_writeList _ _ readWord_writeWord,
    readVector_writeVector _ _ (by intro bit rest; rfl : ∀ bit rest,
      readBit ([bit] ++ rest) = some (bit, rest)),
    readIndex_writeIndex, readVector_writeVector _ _ readWord_writeWord,
    readFactors_writeFactors]

/-- Evaluate an ambient word as an element of the generated permutation subgroup. -/
def wordToAmbient {degree : ℕ} (gs : List (Perm (Fin degree))) (word : Word gs.length) :
    FiniteAction.ambientGroup gs :=
  ⟨wordValue gs word, wordValue_mem gs word⟩

/-- Evaluate the raw certificate’s ambient words as subgroup generators. -/
def decodedGenerators {degree : ℕ} (gs : List (Perm (Fin degree)))
    (c : RawCertificate degree gs.length) : List (FiniteAction.ambientGroup gs) :=
  c.generatorWords.map (wordToAmbient gs)

/-- Find a point’s position in the ordered mask complement. -/
def complementIndex {degree : ℕ} (mask : Fin degree → Bool) (x : Fin degree)
    (hx : mask x = false) : Fin (complement mask).length :=
  Fin.find (fun i => (complement mask).get i = x)
    (List.mem_iff_get.mp (by simp [complement, hx]))

theorem complementIndex_spec {degree : ℕ} (mask : Fin degree → Bool) (x : Fin degree)
    (hx : mask x = false) :
    (complement mask).get (complementIndex mask x hx) = x :=
  Fin.find_spec (p := fun i => (complement mask).get i = x) _

/-- Interpret the finite data of a raw certificate as a mathematical witness. -/
def decode {degree : ℕ} (gs : List (Perm (Fin degree)))
    (c : RawCertificate degree gs.length) :
    DecodedCertificate (FiniteAction.ambientGroup gs) where
  claim := c.claim
  generators := decodedGenerators gs c
  fixedSet := Finset.univ.filter fun x => c.mask x
  base := c.base
  orbitWords x :=
    let word := if hx : c.mask x = false then
      c.orbitWords (complementIndex c.mask x hx) else []
    word.map fun letter => (Fin.cast (List.length_map ..).symm letter.1, letter.2)
  cycleFactors := (factorList c.claim c.cycleFactors).map fun factor =>
    ⟨wordToAmbient gs factor.conjugator,
      Fin.cast (List.length_map ..).symm factor.generatorIndex, factor.inverted⟩

/-- Decode and validate a certificate, rejecting malformed or trailing data. -/
def verifyRaw {degree : ℕ} (gs : List (Perm (Fin degree))) (bits : List Bool) :
    Option (VerifiedCertificate gs) := do
  let raw ← readAll (readCertificate degree gs.length) bits
  validate gs (decode gs raw)

theorem verifyRaw_encoded_iff {degree : ℕ} (gs : List (Perm (Fin degree)))
    (c : RawCertificate degree gs.length) :
    (verifyRaw gs (writeCertificate c)).isSome = true ↔ Valid (decode gs c) := by
  simp [verifyRaw, readAll_write _ _ readCertificate_writeCertificate,
    validate_isSome_iff]

/-- An encoded input’s degree, generators, and validated certificate. -/
structure VerifiedInput where
  /-- The degree decoded from the input. -/
  degree : ℕ
  /-- The permutation generators decoded from the input. -/
  generators : List (Perm (Fin degree))
  /-- The certificate with proved validity for the decoded generators. -/
  result : VerifiedCertificate generators

/-- Parse a raw group encoding and return its validated certificate, or reject either encoding. -/
def verify (input certificate : List Bool) : Option VerifiedInput :=
  match readAll readGroup input with
  | none => none
  | some ⟨degree, gs⟩ =>
      match verifyRaw gs certificate with
      | none => none
      | some result => some ⟨degree, gs, result⟩

theorem verify_encoded_iff {degree : ℕ} (gs : List (Perm (Fin degree)))
    (c : RawCertificate degree gs.length) :
    (verify (writeGroup ⟨degree, gs⟩) (writeCertificate c)).isSome = true ↔
      Valid (decode gs c) := by
  simp only [verify, readAll_write _ _ readGroup_writeGroup]
  cases h : verifyRaw gs (writeCertificate c) <;>
    simpa only [h, Option.bind_none, Option.bind_some, Option.isSome_none,
      Option.isSome_some, Bool.false_eq_true, iff_false, true_iff] using
      (verifyRaw_encoded_iff gs c)

theorem verify_input_matches (input certificate : List Bool) (result : VerifiedInput)
    (h : verify input certificate = some result) :
    readAll readGroup input = some ⟨result.degree, result.generators⟩ := by
  unfold verify at h
  cases hg : readAll readGroup input with
  | none => simp [hg] at h
  | some group =>
      rcases group with ⟨degree, gs⟩
      simp only [hg] at h
      cases hv : verifyRaw gs certificate with
      | none => simp [hv] at h
      | some value =>
          simp only [hv] at h
          cases Option.some.inj h
          rfl

theorem VerifiedInput.sound (result : VerifiedInput) : ClaimHolds result.result.certificate :=
  result.result.sound _

theorem raw_checker_sound {degree : ℕ} (gs : List (Perm (Fin degree)))
    (bits : List Bool) (result : VerifiedCertificate gs)
    (_h : verifyRaw gs bits = some result) :
    ClaimHolds result.certificate :=
  result.sound _


end TauCeti.CertificateWire
