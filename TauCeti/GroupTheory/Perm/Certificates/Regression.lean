/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Families
public import TauCeti.GroupTheory.Perm.Certificates.Search
public meta import TauCeti.GroupTheory.Perm.Certificates.Families
public meta import TauCeti.GroupTheory.Perm.Certificates.Search

/-!
# Executable boundary regressions

These evaluations exercise the compiled parser, finite-action checks, accepted
families, rejection paths, and bounded runner. They supplement the universal
kernel-checked theorems; evaluation is not used to prove any theorem.
-/

open Equiv Equiv.Perm
open TauCeti.BinaryCodec TauCeti.CertificateWire TauCeti.CertifiedPermutation
open TauCeti.SuccessfulFamilies TauCeti.BoundedRunner

@[expose] public section

namespace TauCeti.ExecutableRegression

/-- A four-cycle used to check rejection of a transitive imprimitive action. -/
def cyclicFour : Perm (Fin 4) := swap 0 1 * swap 1 2 * swap 2 3

/-- The explicit symmetric certificate at degree five. -/
def symmetricFive := symmetricCertificate (degree := 5) (by decide)

/-- The explicit alternating certificate at degree six. -/
def alternatingSix := alternatingCertificate (degree := 6) (by decide)

/-- An alternating-family witness falsely requesting a symmetric claim. -/
def incorrectOddClaim : RawCertificate 6 (triples 6 (fun _ => true)).length where
  claim := .symmetric
  generatorWords := alternatingSix.generatorWords
  mask := alternatingSix.mask
  base := alternatingSix.base
  orbitWords := alternatingSix.orbitWords
  cycleFactors := alternatingSix.cycleFactors

/-- A symmetric-family witness falsely requesting an alternating claim. -/
def incorrectEvenClaim : RawCertificate 5 (swaps 5 (fun _ => true)).length where
  claim := .alternating
  generatorWords := symmetricFive.generatorWords
  mask := symmetricFive.mask
  base := symmetricFive.base
  orbitWords := symmetricFive.orbitWords
  cycleFactors := symmetricFive.cycleFactors

/-- A certificate with an empty subgroup generator list. -/
def missingOrbitWords : RawCertificate 5 (swaps 5 (fun _ => true)).length :=
  { symmetricFive with orbitWords := fun _ => [] }

/-- A certificate with an empty pointwise fixing set. -/
def emptyFixedSet : RawCertificate 5 (swaps 5 (fun _ => true)).length where
  claim := .symmetric
  generatorWords := symmetricFive.generatorWords
  mask := fun _ => false
  base := symmetricFive.base
  orbitWords := fun _ => []
  cycleFactors := symmetricFive.cycleFactors

/-- A certificate whose orbit base belongs to its fixed set. -/
def baseInFixedSet : RawCertificate 5 (swaps 5 (fun _ => true)).length :=
  { symmetricFive with base := 0 }

/-- An alternating claim with no prime-cycle factors. -/
def missingCycle : RawCertificate 5 (swaps 5 (fun _ => true)).length :=
  { symmetricFive with cycleFactors := [] }

/-- A two-seed attempt function used to exercise first-success search. -/
def attempt (seed : Bool) : Option ℕ := if seed then some 7 else none

#eval show IO Unit from do
  let sInput := writeGroup ⟨5, swaps 5 (fun _ => true)⟩
  let sBits := writeCertificate symmetricFive
  let aInput := writeGroup ⟨6, triples 6 (fun _ => true)⟩
  let aBits := writeCertificate alternatingSix
  let duplicateTable : Fin 3 → Fin 3 := ![0, 0, 2]
  let tests : List (String × Bool) := [
    ("unary zero", (readUnary [false]).isSome),
    ("empty unary", (readUnary []).isNone),
    ("unterminated unary", (readUnary [true, true]).isNone),
    ("index into empty range", (readIndex 0 [false]).isNone),
    ("out-of-range index", (readIndex 3 [true, true]).isNone),
    ("truncated index", (readIndex 5 [false, true]).isNone),
    ("reserved tag", (readClaim [true, true]).isNone),
    ("truncated tag", (readClaim [false]).isNone),
    ("nonbijective table",
      (readAll (readPermutation 3) (writeVector writeIndex duplicateTable)).isNone),
    ("group roundtrip", (readAll readGroup sInput).isSome),
    ("truncated group", (readAll readGroup sInput.dropLast).isNone),
    ("trailing group", (readAll readGroup (sInput ++ [false])).isNone),
    ("symmetric certificate", (verify sInput sBits).isSome),
    ("alternating certificate", (verify aInput aBits).isSome),
    ("truncated certificate", (verify sInput sBits.dropLast).isNone),
    ("trailing certificate", (verify sInput (sBits ++ [false])).isNone),
    ("malformed input", (verify [] sBits).isNone),
    ("malformed certificate", (verify sInput [true, true]).isNone),
    ("odd claim over even generators",
      (verify aInput (writeCertificate incorrectOddClaim)).isNone),
    ("even claim over odd generators",
      (verify sInput (writeCertificate incorrectEvenClaim)).isNone),
    ("missing orbit witnesses", (verify sInput (writeCertificate missingOrbitWords)).isNone),
    ("empty fixed set", (verify sInput (writeCertificate emptyFixedSet)).isNone),
    ("base in fixed set", (verify sInput (writeCertificate baseInFixedSet)).isNone),
    ("missing prime cycle", (verify sInput (writeCertificate missingCycle)).isNone),
    ("cyclic transitivity", FiniteAction.transitiveCheck [cyclicFour] 0),
    ("cyclic imprimitivity", !(FiniteAction.primitiveCheck [cyclicFour] 0)),
    ("identity is not a cycle", !(FinitePermutation.cycleCheck (1 : Perm (Fin 4)))),
    ("single four-cycle", FinitePermutation.cycleCheck cyclicFour),
    ("two disjoint cycles", !(FinitePermutation.cycleCheck (swap (0 : Fin 4) 1 * swap 2 3))),
    ("first successful trial", decide (run attempt ![false, true, true] = some 7)),
    ("early stopping count", decide (calls attempt [false, true, true] = 2)),
    ("all failed trials", (run attempt ![false, false]).isNone),
    ("zero trials", (run attempt (Fin.elim0 : Fin 0 → Bool)).isNone),
    ("seed bit length",
      decide ((seedBits ![![false, true], ![true, false]]).length = 4)),
    ("raw-input search",
      (searchInput sInput (fun _ : Unit => sBits) (fun _ : Fin 1 => ())).isSome),
    ("raw-input empty search",
      (searchInput sInput (fun _ : Unit => sBits) (Fin.elim0 : Fin 0 → Unit)).isNone)]
  for test in tests do
    unless test.2 = true do
      throw (IO.userError s!"Regression failed: {test.1}")
  IO.println s!"Executable regressions: {tests.length} passed."
  IO.println s!"S_5 input/certificate bits: {sInput.length}/{sBits.length}."
  IO.println s!"A_6 input/certificate bits: {aInput.length}/{aBits.length}."

end TauCeti.ExecutableRegression
