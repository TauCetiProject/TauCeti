/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTime.Writer
public import TauCeti.GroupTheory.Perm.Certificates.Runtime.Wire.Erasure

/-!
# Uniform polynomial-time certificate serialization

The list representation has the same canonical binary output as the dependent
certificate representation. The machines accept the degree and generator counts
as data, so their finite control is independent of those bounds.
-/

@[expose] public section

namespace TauCeti.CertificateRuntime

open Computability BitEncoding Turing BinaryCodec PermutationTables
open Turing.PolyTime (writeNatIndex)

/-- Serialize an erased bounded index and its inversion bit. -/
def writeLetter (size : ℕ) (letter : ℕ × Bool) : List Bool :=
  writeNatIndex size letter.1 ++ [letter.2]

/-- Serialize an erased signed word with its unary length prefix. -/
def writeWord (size : ℕ) (word : PermutationTables.Word) : List Bool :=
  BinaryCodec.writeList (writeLetter size) word

/-- Serialize an erased permutation table in point order. -/
def writeTable (n : ℕ) (table : Table) : List Bool :=
  table.flatMap (writeNatIndex n)

/-- Serialize an erased group input. -/
def writeGroup (group : ℕ × List Table) : List Bool :=
  writeUnary group.1 ++ BinaryCodec.writeList (writeTable group.1) group.2

/-- Serialize the three supported tags; every other value uses the reserved tag. -/
def writeClaim (claim : ℕ) : List Bool :=
  bif decide (claim = 0) then [false, false]
  else bif decide (claim = 1) then [false, true]
  else bif decide (claim = 2) then [true, false] else [true, true]

/-- Serialize an erased conjugator word and signed subgroup generator index. -/
def writeFactor (params : ℕ × ℕ) (factor : Factor) : List Bool :=
  writeWord params.1 factor.1 ++ writeNatIndex params.2 factor.2.1 ++ [factor.2.2]

/-- Serialize the erased certificate using the declared degree and ambient size. -/
def writeCertificate (params : ℕ × ℕ) (c : Certificate) : List Bool :=
  writeClaim c.1 ++ BinaryCodec.writeList (writeWord params.2) c.2.1 ++
    c.2.2.1 ++ writeNatIndex params.1 c.2.2.2.1 ++
    c.2.2.2.2.1.flatMap (writeWord c.2.1.length) ++
    (bif decide (c.1 = 0) then [] else
      BinaryCodec.writeList (writeFactor (params.2, c.2.1.length)) c.2.2.2.2.2)

@[fun_prop] theorem polyTime_writeLetter :
    PolyTime (fun p : ℕ × (ℕ × Bool) => writeLetter p.1 p.2) := by
  unfold writeLetter
  fun_prop

@[fun_prop] theorem polyTime_writeWord :
    PolyTime (fun p : ℕ × PermutationTables.Word => writeWord p.1 p.2) := by
  unfold writeWord
  fun_prop

@[fun_prop] theorem polyTime_writeTable :
    PolyTime (fun p : ℕ × Table => writeTable p.1 p.2) := by
  unfold writeTable
  fun_prop

@[fun_prop] theorem polyTime_writeGroup : PolyTime writeGroup := by
  unfold writeGroup
  fun_prop

@[fun_prop] theorem polyTime_writeClaim : PolyTime writeClaim := by
  unfold writeClaim
  fun_prop

@[fun_prop] theorem polyTime_writeFactor :
    PolyTime (fun p : (ℕ × ℕ) × Factor => writeFactor p.1 p.2) := by
  unfold writeFactor
  fun_prop

@[fun_prop] theorem polyTime_writeCertificate :
    PolyTime (fun p : (ℕ × ℕ) × Certificate => writeCertificate p.1 p.2) := by
  unfold writeCertificate
  fun_prop

theorem writeLetter_erase {size : ℕ} (letter : Fin size × Bool) :
    writeLetter size (letter.1.val, letter.2) = CertificateWire.writeLetter letter := rfl

theorem writeWord_erase {size : ℕ} (word : FinitePermutation.Word size) :
    writeWord size (eraseWord word) = CertificateWire.writeWord word := by
  simp only [writeWord, CertificateWire.writeWord, BinaryCodec.writeList, eraseWord,
    List.length_map, List.flatMap_map, writeLetter_erase]

theorem writeTable_ofPerm {n : ℕ} (g : Equiv.Perm (Fin n)) :
    writeTable n (ofPerm g) = CertificateWire.writePermutation g := by
  rw [CertificateWire.writePermutation, PolyTime.writeVector_eq_flatMap]
  simp only [writeTable, ofPerm, List.ofFn_eq_map, List.flatMap_map,
    PolyTime.writeNatIndex_eq_writeIndex]

theorem writeGroup_erase (g : CertificateWire.GroupData) :
    writeGroup (eraseGroup g) = CertificateWire.writeGroup g := by
  simp only [writeGroup, eraseGroup, CertificateWire.writeGroup, BinaryCodec.writeList,
    List.length_map, List.flatMap_map, writeTable_ofPerm]

theorem writeClaim_erase (claim : CertifiedPermutation.Claim) :
    writeClaim (claimCode claim) = CertificateWire.writeClaim claim := by
  cases claim <;> rfl

theorem writeFactor_erase {ambient subgroup : ℕ}
    (factor : CertificateWire.RawFactor ambient subgroup) :
    writeFactor (ambient, subgroup) (eraseFactor factor) =
      CertificateWire.writeFactor factor := by
  simp only [writeFactor, eraseFactor, CertificateWire.writeFactor, writeWord_erase,
    PolyTime.writeNatIndex_eq_writeIndex]

/-- The erased factor list has the same optional canonical payload. -/
theorem writeFactors_erase {ambient subgroup : ℕ} (claim : CertifiedPermutation.Claim)
    (factors : CertificateWire.FactorsFor claim ambient subgroup) :
    (bif decide (claimCode claim = 0) then [] else
      BinaryCodec.writeList (writeFactor (ambient, subgroup))
        ((CertificateWire.factorList claim factors).map eraseFactor)) =
      CertificateWire.writeFactors claim factors := by
  cases claim <;>
    dsimp [CertificateWire.FactorsFor, claimCode, CertificateWire.factorList,
      CertificateWire.writeFactors] at factors ⊢
  all_goals
    simp only [BinaryCodec.writeList, List.length_map, List.flatMap_map, writeFactor_erase]
    rfl

/-- The uniform serializer produces exactly the canonical certificate bit string. -/
theorem writeCertificate_erase {n ambient : ℕ} (c : CertificateWire.RawCertificate n ambient) :
    writeCertificate (n, ambient) (eraseCertificate c) = CertificateWire.writeCertificate c := by
  simp only [writeCertificate, eraseCertificate, CertificateWire.writeCertificate,
    writeClaim_erase, BinaryCodec.writeList, List.length_map, List.flatMap_map,
    writeWord_erase, PolyTime.writeNatIndex_eq_writeIndex,
    PolyTime.writeVector_eq_flatMap, List.ofFn_eq_map]
  simp only [← List.map_eq_flatMap]
  congr 1
  simpa only [BinaryCodec.writeList, List.length_map, List.flatMap_map] using
    writeFactors_erase c.claim c.cycleFactors

end TauCeti.CertificateRuntime
