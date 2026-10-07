/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.PolyTimeParserCombinators
public import TauCeti.GroupTheory.Perm.Certificates.Tables
public import TauCeti.GroupTheory.Perm.Certificates.Encoding

/-!
# Uniform machines for the certificate wire format

The machine representation erases bounded-index proofs, and represents vectors
by ordinary lists. All bounds are inputs to a single finite-control machine.
Binary indices are accumulated with saturation, including on rejected inputs.
-/

@[expose] public section

namespace TauCeti.CertificateRuntime

open Computability BitEncoding Turing BinaryCodec PermutationTables

/-- A cycle factor represented by an ambient conjugator and a subgroup generator letter. -/
abbrev Factor := PermutationTables.Word × ℕ × Bool

/-- Proof-erased certificate fields: claim, subgroup words, mask, base, orbits,
and cycle factors. -/
abbrev Certificate :=
  ℕ × List PermutationTables.Word × List Bool × ℕ × List PermutationTables.Word × List Factor

/-- Numeric tags for double transitivity, alternating equality, and symmetric equality. -/
def claimCode : CertifiedPermutation.Claim → ℕ
  | .doublyTransitive => 0
  | .alternating => 1
  | .symmetric => 2

/-- Parse the two-bit claim tag and retain the unconsumed suffix. -/
def readClaim (bits : List Bool) : Option (ℕ × List Bool) :=
  bif decide (bits.take 2 = [false, false]) then some (0, bits.drop 2)
  else bif decide (bits.take 2 = [false, true]) then some (1, bits.drop 2)
  else bif decide (bits.take 2 = [true, false]) then some (2, bits.drop 2)
  else none

@[fun_prop] theorem polyTime_readClaim : PolyTime readClaim := by
  unfold readClaim
  fun_prop

theorem readClaim_eq (bits : List Bool) :
    readClaim bits = (CertificateWire.readClaim bits).map (fun q => (claimCode q.1, q.2)) := by
  cases bits with
  | nil => rfl
  | cons b bits =>
    cases bits with
    | nil => cases b <;> rfl
    | cons c bits => cases b <;> cases c <;> rfl

/-- Parse a bounded generator index followed by its inverse flag. -/
def readLetter : ℕ → Parser (ℕ × Bool) :=
  bindParser indexParser
    (mapParser (fun p bit => (p.2, bit)) (fun _ => readBit))

@[fun_prop] theorem polyTime_readLetter :
    PolyTime (fun p : ℕ × List Bool => readLetter p.1 p.2) := by
  unfold readLetter bindParser mapParser
  fun_prop

theorem consumes_readLetter : Consumes readLetter :=
  consumes_bindParser consumes_indexParser
    (consumes_mapParser (consumes_reparam consumes_readBit (fun _ => ())))

/-- Parse a unary-length-prefixed list of bounded generator letters. -/
def readWord (size : ℕ) : Parser PermutationTables.Word := readList (readLetter size)

@[fun_prop] theorem polyTime_readWord :
    PolyTime (fun p : ℕ × List Bool => readWord p.1 p.2) :=
  polyTime_readList polyTime_readLetter consumes_readLetter

theorem consumes_readWord : Consumes readWord := consumes_readList consumes_readLetter

/-- Parse a conjugator word and a subgroup generator letter using the supplied sizes. -/
def readFactor : ℕ × ℕ → Parser Factor :=
  bindParser (fun p => readWord p.1)
    (mapParser (fun p letter => (p.2, letter)) (fun p => readLetter p.1.2))

@[fun_prop] theorem polyTime_readFactor :
    PolyTime (fun p : (ℕ × ℕ) × List Bool => readFactor p.1 p.2) := by
  unfold readFactor bindParser mapParser
  fun_prop

theorem consumes_readFactor : Consumes readFactor := by
  intro params bits value tail h
  unfold readFactor bindParser mapParser at h
  cases hw : readWord params.1 bits with
  | none => simp [hw] at h
  | some q =>
    cases hl : readLetter params.2 q.2 with
    | none => simp [hw, hl] at h
    | some r =>
      have he : ((q.1, r.1), r.2) = (value, tail) := by simpa [hw, hl] using h
      have ht : r.2 = tail := congrArg Prod.snd he
      rw [← ht]
      exact (consumes_readLetter params.2 q.2 r.1 r.2 hl).trans
        (consumes_readWord params.1 bits q.1 q.2 hw)

/-- Check injectivity of a table on the `n` points, after bounded image parsing. -/
def tableValid (n : ℕ) (t : Table) : Bool :=
  (List.range n).all fun x => (List.range n).all fun y =>
    !decide (lookup n t x = lookup n t y) || decide (x = y)

@[fun_prop] theorem polyTime_tableValid :
    PolyTime (fun p : ℕ × Table => tableValid p.1 p.2) := by
  unfold tableValid
  fun_prop

/-- Parse `n` bounded images and reject tables that fail the permutation check. -/
def readTable : ℕ → Parser Table :=
  filterParser tableValid (fun n => readMany (indexParser n) n)

@[fun_prop] theorem polyTime_readTable :
    PolyTime (fun p : ℕ × List Bool => readTable p.1 p.2) := by
  have hm := polyTime_readMany polyTime_indexParser consumes_indexParser
  apply polyTime_filterParser polyTime_tableValid
  exact PolyTime.comp (f := fun p : ℕ × List Bool => (p.1, p.1, p.2)) hm (by fun_prop)

theorem consumes_readTable : Consumes readTable :=
  consumes_filterParser (consumes_reparam (consumes_readMany consumes_indexParser)
    (fun n => (n, n)))

/-- Parse the unary degree and the list of permutation tables. -/
def readGroup (bits : List Bool) : Option ((ℕ × List Table) × List Bool) :=
  (readUnary bits).bind fun q =>
    (readList (readTable q.1) q.2).map fun r => ((q.1, r.1), r.2)

@[fun_prop] theorem polyTime_readTables :
    PolyTime (fun p : ℕ × List Bool => readList (readTable p.1) p.2) :=
  polyTime_readList polyTime_readTable consumes_readTable

@[fun_prop] theorem polyTime_readTables_comp {α : Type} [Primcodable α] [BitEncoding α]
    {n : α → ℕ} {bits : α → List Bool} (hn : PolyTime n) (hb : PolyTime bits) :
    PolyTime (fun a => readList (readTable (n a)) (bits a)) :=
  PolyTime.comp (f := fun a => (n a, bits a)) polyTime_readTables (PolyTime.pair hn hb)

@[fun_prop] theorem polyTime_groupRest :
    PolyTime (fun q : ℕ × List Bool =>
      (readList (readTable q.1) q.2).map fun r => ((q.1, r.1), r.2)) :=
  PolyTime.option_map
    (f := fun (q : ℕ × List Bool) (r : List Table × List Bool) => ((q.1, r.1), r.2))
    (by fun_prop) polyTime_readTables

@[fun_prop] theorem polyTime_readGroup : PolyTime readGroup := by
  unfold readGroup
  exact
  PolyTime.option_bind
    (f := fun (_ : List Bool) (q : ℕ × List Bool) =>
      (readList (readTable q.1) q.2).map fun r => ((q.1, r.1), r.2))
    (PolyTime.comp (g := fun q : ℕ × List Bool =>
      (readList (readTable q.1) q.2).map fun r => ((q.1, r.1), r.2))
      (f := fun p : List Bool × (ℕ × List Bool) => p.2)
      polyTime_groupRest PolyTime.snd) polyTime_readUnary

@[fun_prop] theorem polyTime_readWords :
    PolyTime (fun p : ℕ × List Bool => readList (readWord p.1) p.2) :=
  polyTime_readList polyTime_readWord consumes_readWord

@[fun_prop] theorem polyTime_readWords_comp {α : Type} [Primcodable α] [BitEncoding α]
    {n : α → ℕ} {bits : α → List Bool} (hn : PolyTime n) (hb : PolyTime bits) :
    PolyTime (fun a => readList (readWord (n a)) (bits a)) :=
  PolyTime.comp (f := fun a => (n a, bits a)) polyTime_readWords (PolyTime.pair hn hb)

@[fun_prop] theorem polyTime_readMask :
    PolyTime (fun p : ℕ × List Bool => readMany readBit p.1 p.2) := by
  have hm := polyTime_readMany
    (parser := fun _ : Unit => readBit) (by fun_prop) consumes_readBit
  exact PolyTime.comp (f := fun p : ℕ × List Bool => ((), p.1, p.2)) hm (by fun_prop)

@[fun_prop] theorem polyTime_readMask_comp {α : Type} [Primcodable α] [BitEncoding α]
    {n : α → ℕ} {bits : α → List Bool} (hn : PolyTime n) (hb : PolyTime bits) :
    PolyTime (fun a => readMany readBit (n a) (bits a)) :=
  PolyTime.comp (f := fun a => (n a, bits a)) polyTime_readMask (PolyTime.pair hn hb)

@[fun_prop] theorem polyTime_readOrbitWords :
    PolyTime (fun p : ℕ × ℕ × List Bool => readMany (readWord p.1) p.2.1 p.2.2) :=
  polyTime_readMany polyTime_readWord consumes_readWord

@[fun_prop] theorem polyTime_readOrbitWords_comp {α : Type}
    [Primcodable α] [BitEncoding α] {size count : α → ℕ} {bits : α → List Bool}
    (hs : PolyTime size) (hc : PolyTime count) (hb : PolyTime bits) :
    PolyTime (fun a => readMany (readWord (size a)) (count a) (bits a)) :=
  PolyTime.comp (f := fun a => (size a, count a, bits a))
    polyTime_readOrbitWords (PolyTime.pair hs (PolyTime.pair hc hb))

@[fun_prop] theorem polyTime_readFactors :
    PolyTime (fun p : (ℕ × ℕ) × List Bool => readList (readFactor p.1) p.2) :=
  polyTime_readList polyTime_readFactor consumes_readFactor

@[fun_prop] theorem polyTime_readFactors_comp {α : Type}
    [Primcodable α] [BitEncoding α] {params : α → ℕ × ℕ} {bits : α → List Bool}
    (hp : PolyTime params) (hb : PolyTime bits) :
    PolyTime (fun a => readList (readFactor (params a)) (bits a)) :=
  PolyTime.comp (f := fun a => (params a, bits a))
    polyTime_readFactors (PolyTime.pair hp hb)

/-- Parse all certificate fields using the degree and ambient generator count as bounds. -/
def readCertificate (params : ℕ × ℕ) (bits : List Bool) :
    Option (Certificate × List Bool) :=
  (readClaim bits).bind fun tag =>
    (readList (readWord params.2) tag.2).bind fun gens =>
      (readMany readBit params.1 gens.2).bind fun mask =>
        (indexParser params.1 mask.2).bind fun base =>
          (readMany (readWord gens.1.length) (mask.1.filter (! ·)).length base.2).bind
            fun words =>
              (bif decide (tag.1 = 0) then some ([], words.2)
                else readList (readFactor (params.2, gens.1.length)) words.2).map
                fun factors => ((tag.1, gens.1, mask.1, base.1, words.1, factors.1), factors.2)

@[fun_prop] theorem polyTime_readCertificate :
    PolyTime (fun p : (ℕ × ℕ) × List Bool => readCertificate p.1 p.2) := by
  unfold readCertificate
  fun_prop

end TauCeti.CertificateRuntime
