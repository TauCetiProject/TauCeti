/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.RuntimeWire
public import TauCeti.GroupTheory.Perm.Certificates.TableActions

/-!
# Erasing the proofs in the binary certificate parser

The uniform list parser and the dependent certificate parser return the same
data on every bit string, including failures and unused suffixes.
-/

@[expose] public section

namespace TauCeti.CertificateRuntime

open Equiv BinaryCodec PermutationTables

/-- Forget bounded-index proofs in a canonical cycle factor. -/
def eraseFactor {ambient subgroup : ℕ} (f : CertificateWire.RawFactor ambient subgroup) :
    Factor := (eraseWord f.conjugator, f.generatorIndex.val, f.inverted)

/-- Convert a dependent canonical certificate into the list-based runtime representation. -/
def eraseCertificate {n ambient : ℕ} (c : CertificateWire.RawCertificate n ambient) :
    Certificate :=
  (claimCode c.claim, c.generatorWords.map eraseWord, List.ofFn c.mask, c.base.val,
    List.ofFn fun i => eraseWord (c.orbitWords i),
    (CertificateWire.factorList c.claim c.cycleFactors).map eraseFactor)

/-- Forget finite-point proofs in the degree and ambient permutation tables. -/
def eraseGroup (g : CertificateWire.GroupData) : ℕ × List Table :=
  (g.1, g.2.map ofPerm)

theorem readLetter_eq (size : ℕ) (bits : List Bool) :
    readLetter size bits =
      (CertificateWire.readLetter size bits).map (fun q => ((q.1.1.val, q.1.2), q.2)) := by
  unfold readLetter bindParser mapParser CertificateWire.readLetter
  rw [indexParser_eq_readIndex]
  cases hi : readIndex size bits with
  | none => simp
  | some q =>
    rcases q with ⟨i, rest⟩
    cases hb : readBit rest <;> simp [hb]

theorem readWord_eq (size : ℕ) (bits : List Bool) :
    readWord size bits =
      (CertificateWire.readWord size bits).map (fun q => (eraseWord q.1, q.2)) := by
  unfold readWord CertificateWire.readWord
  rw [show readLetter size = fun b => (CertificateWire.readLetter size b).map
      (fun q => ((q.1.1.val, q.1.2), q.2)) from funext (readLetter_eq size)]
  simpa only [eraseWord] using
    readList_map (CertificateWire.readLetter size) (fun l : Fin size × Bool => (l.1.val, l.2)) bits

theorem readFactor_eq (ambient subgroup : ℕ) (bits : List Bool) :
    readFactor (ambient, subgroup) bits =
      (CertificateWire.readFactor ambient subgroup bits).map
        (fun q => (eraseFactor q.1, q.2)) := by
  unfold readFactor bindParser mapParser
  dsimp only
  rw [readWord_eq]
  cases hw : CertificateWire.readWord ambient bits with
  | none => simp [CertificateWire.readFactor, hw]
  | some q =>
    rcases q with ⟨w, rest⟩
    simp only [Option.map_some, Option.bind_some]
    rw [readLetter_eq]
    unfold CertificateWire.readLetter CertificateWire.readFactor
    rw [hw]
    cases hi : readIndex subgroup rest with
    | none => simp [hi]
    | some q =>
      rcases q with ⟨i, tail⟩
      cases hb : readBit tail <;> simp [hi, hb, eraseFactor]

theorem readIndexVector_eq (n : ℕ) (bits : List Bool) :
    readMany (indexParser n) n bits =
      (readVector (readIndex n) n bits).map
        (fun q => (List.ofFn fun i => (q.1 i).val, q.2)) := by
  rw [show indexParser n = fun b => (readIndex n b).map (fun q => (q.1.val, q.2))
    from funext (indexParser_eq_readIndex n), readMany_map, ← readVector_list]
  simp [Option.map_map, List.map_ofFn, Function.comp_def]

theorem tableValid_ofFn {n : ℕ} (f : Fin n → Fin n) :
    tableValid n (List.ofFn fun i => (f i).val) = decide (Function.Injective f) := by
  apply Bool.eq_iff_iff.mpr
  simp only [tableValid, all_range, Bool.or_eq_true, decide_eq_true_eq, lookup_ofFn]
  simp [Function.Injective, Fin.ext_iff, or_iff_not_imp_left]

theorem readTable_eq (n : ℕ) (bits : List Bool) :
    readTable n bits = (CertificateWire.readPermutation n bits).map
      (fun q => (ofPerm q.1, q.2)) := by
  unfold readTable filterParser
  dsimp only
  rw [readIndexVector_eq]
  cases hr : readVector (readIndex n) n bits with
  | none => simp [CertificateWire.readPermutation, hr]
  | some q =>
    rcases q with ⟨f, tail⟩
    simp only [Option.map_some, Option.bind_some, tableValid_ofFn]
    by_cases hf : Function.Injective f
    · simp [hf, CertificateWire.readPermutation, hr, ofPerm]
    · simp [hf, CertificateWire.readPermutation, hr]

theorem readGroup_eq (bits : List Bool) :
    readGroup bits = (CertificateWire.readGroup bits).map
      (fun q => (eraseGroup q.1, q.2)) := by
  unfold readGroup CertificateWire.readGroup
  cases hu : readUnary bits with
  | none => simp
  | some q =>
    rcases q with ⟨n, rest⟩
    simp only [Option.bind_some]
    have ht : readTable n = fun b => (CertificateWire.readPermutation n b).map
        (fun q => (ofPerm q.1, q.2)) := funext (readTable_eq n)
    rw [ht, readList_map]
    cases hl : readList (CertificateWire.readPermutation n) rest <;> simp [hl, eraseGroup]

theorem readWords_eq (size : ℕ) (bits : List Bool) :
    readList (readWord size) bits =
      (readList (CertificateWire.readWord size) bits).map
        (fun q => (q.1.map eraseWord, q.2)) := by
  rw [show readWord size = fun b => (CertificateWire.readWord size b).map
    (fun q => (eraseWord q.1, q.2)) from funext (readWord_eq size)]
  exact readList_map _ _ _

theorem readWordVector_eq (size count : ℕ) (bits : List Bool) :
    readMany (readWord size) count bits =
      (readVector (CertificateWire.readWord size) count bits).map
        (fun q => (List.ofFn fun i => eraseWord (q.1 i), q.2)) := by
  rw [show readWord size = fun b => (CertificateWire.readWord size b).map
    (fun q => (eraseWord q.1, q.2)) from funext (readWord_eq size),
    readMany_map, ← readVector_list]
  simp [Option.map_map, List.map_ofFn, Function.comp_def]

theorem complement_length {n : ℕ} (mask : Fin n → Bool) :
    ((List.ofFn mask).filter (! ·)).length = (CertificateWire.complement mask).length := by
  simp [CertificateWire.complement, List.ofFn_eq_map, List.filter_map,
    Function.comp_def]

theorem readFactors_eq (ambient subgroup : ℕ) (claim : CertifiedPermutation.Claim)
    (bits : List Bool) :
    (bif decide (claimCode claim = 0) then some ([], bits)
      else readList (readFactor (ambient, subgroup)) bits) =
        (CertificateWire.readFactors ambient subgroup claim bits).map
          (fun q => ((CertificateWire.factorList claim q.1).map eraseFactor, q.2)) := by
  have hf : readFactor (ambient, subgroup) = fun b =>
      (CertificateWire.readFactor ambient subgroup b).map
        (fun q => (eraseFactor q.1, q.2)) := funext (readFactor_eq ambient subgroup)
  cases claim <;>
    simp [claimCode, CertificateWire.readFactors, CertificateWire.factorList, hf,
      readList_map] <;> rfl

theorem readCertificate_eq (n ambient : ℕ) (bits : List Bool) :
    readCertificate (n, ambient) bits =
      (CertificateWire.readCertificate n ambient bits).map
        (fun q => (eraseCertificate q.1, q.2)) := by
  unfold readCertificate CertificateWire.readCertificate
  rw [readClaim_eq]
  cases ht : CertificateWire.readClaim bits with
  | none => simp
  | some q =>
    rcases q with ⟨tag, rest⟩
    simp only [Option.map_some, Option.bind_some]
    rw [readWords_eq]
    cases hg : readList (CertificateWire.readWord ambient) rest with
    | none => simp_all
    | some q =>
      rcases q with ⟨gs, rest⟩
      simp_all only [Option.map_some, Option.bind_some]
      rw [← readVector_list]
      cases hm : readVector readBit n rest with
      | none => simp_all
      | some q =>
        rcases q with ⟨mask, rest⟩
        simp_all only [Option.map_some, Option.bind_some]
        rw [indexParser_eq_readIndex]
        cases hb : readIndex n rest with
        | none => simp_all
        | some q =>
          rcases q with ⟨base, rest⟩
          simp_all only [Option.map_some, Option.bind_some, List.length_map]
          rw [complement_length, readWordVector_eq]
          cases hw : readVector (CertificateWire.readWord gs.length)
              (CertificateWire.complement mask).length rest with
          | none => simp_all
          | some q =>
            rcases q with ⟨words, rest⟩
            simp_all only [Option.map_some, Option.bind_some]
            rw [readFactors_eq]
            cases hf : CertificateWire.readFactors ambient gs.length tag rest <;>
              simp_all [eraseCertificate]

end TauCeti.CertificateRuntime
