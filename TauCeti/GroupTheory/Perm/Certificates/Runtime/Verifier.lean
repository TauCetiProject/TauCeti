/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Runtime.Semantics

/-!
# A polynomial-time TM2 verifier for binary permutation certificates

One finite-control machine reads the input degree, permutation generators, and
certificate. It rejects malformed encodings and false certificates, or returns
the checked claim tag. Its agreement with `CertificateWire.verify` holds for
every pair of bit strings, without a well-formedness hypothesis.
-/

@[expose] public section

namespace TauCeti.CertificateRuntime

open Computability BitEncoding Turing BinaryCodec

/-- Reject invalid encodings and certificates, otherwise return the certified claim. -/
def verifyClaim (input certificate : List Bool) : Option ℕ :=
  (readAll readGroup input).bind fun g =>
    (readAll (readCertificate (g.1, g.2.length)) certificate).bind fun c =>
      bif check g.1 g.2 c then some c.1 else none

/-- Acceptance by the uniform binary machine. -/
def accepts (input certificate : List Bool) : Bool :=
  (verifyClaim input certificate).isSome

@[fun_prop] theorem polyTime_verifyClaim :
    PolyTime (fun p : List Bool × List Bool => verifyClaim p.1 p.2) := by
  have hp : PolyTime (fun p : Unit × List Bool => readGroup p.2) := by fun_prop
  have hg : PolyTime (fun p : List Bool × List Bool => readAll readGroup p.1) :=
    PolyTime.comp (f := fun p : List Bool × List Bool => ((), p.1))
      (polyTime_readAll (parser := fun _ : Unit => readGroup) hp) (by fun_prop)
  have hc : PolyTime (fun p : (List Bool × List Bool) × (ℕ × List PermutationTables.Table) =>
      readAll (readCertificate (p.2.1, p.2.2.length)) p.1.2) :=
    PolyTime.comp
      (f := fun p : (List Bool × List Bool) × (ℕ × List PermutationTables.Table) =>
        ((p.2.1, p.2.2.length), p.1.2))
      (polyTime_readAll (parser := readCertificate) polyTime_readCertificate) (by fun_prop)
  have hf : PolyTime (fun p :
      ((List Bool × List Bool) × (ℕ × List PermutationTables.Table)) × Certificate =>
      bif check p.1.2.1 p.1.2.2 p.2 then some p.2.1 else none) := by
    have hh : PolyTime (fun p :
        ((List Bool × List Bool) × (ℕ × List PermutationTables.Table)) × Certificate =>
        check p.1.2.1 p.1.2.2 p.2) :=
      PolyTime.comp (f := fun p :
          ((List Bool × List Bool) × (ℕ × List PermutationTables.Table)) × Certificate =>
        (p.1.2, p.2)) polyTime_check (by fun_prop)
    fun_prop
  exact PolyTime.option_bind (PolyTime.option_bind hf hc) hg

@[fun_prop] theorem polyTime_accepts :
    PolyTime (fun p : List Bool × List Bool => accepts p.1 p.2) :=
  PolyTime.comp PolyTime.isSome polyTime_verifyClaim

theorem readAllGroup_eq (bits : List Bool) :
    readAll readGroup bits = (readAll CertificateWire.readGroup bits).map eraseGroup := by
  rw [show readGroup = fun b => (CertificateWire.readGroup b).map
    (fun q => (eraseGroup q.1, q.2)) from funext readGroup_eq]
  exact readAll_map _ _ _

theorem readAllCertificate_eq (n ambient : ℕ) (bits : List Bool) :
    readAll (readCertificate (n, ambient)) bits =
      (readAll (CertificateWire.readCertificate n ambient) bits).map eraseCertificate := by
  rw [show readCertificate (n, ambient) = fun b =>
      (CertificateWire.readCertificate n ambient b).map
        (fun q => (eraseCertificate q.1, q.2)) from funext (readCertificate_eq n ambient)]
  exact readAll_map _ _ _

theorem validate_claim {n : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length) :
    (CertifiedPermutation.validate gs (CertificateWire.decode gs c)).map
      (fun r => claimCode r.certificate.claim) =
      (bif CertifiedPermutation.certificateCheck gs (CertificateWire.decode gs c)
        then some (claimCode c.claim) else none) := by
  unfold CertifiedPermutation.validate
  by_cases h : CertifiedPermutation.certificateCheck gs (CertificateWire.decode gs c) = true
  · simp only [h, dite_true, Bool.cond_true, Option.map_some]
    rfl
  · have hf : CertifiedPermutation.certificateCheck gs (CertificateWire.decode gs c) = false :=
      Bool.eq_false_of_not_eq_true h
    rw [dite_eq_right h, hf]
    rfl

/-- Exact agreement, including parser failures, trailing bits, and all three claim tags. -/
theorem verifyClaim_eq (input certificate : List Bool) :
    verifyClaim input certificate =
      (CertificateWire.verify input certificate).map
        (fun r => claimCode r.result.certificate.claim) := by
  unfold verifyClaim CertificateWire.verify
  rw [readAllGroup_eq]
  cases hg : readAll CertificateWire.readGroup input with
  | none => rfl
  | some g =>
    rcases g with ⟨n, gs⟩
    simp only [Option.map_some, Option.bind_some, eraseGroup, List.length_map]
    rw [readAllCertificate_eq]
    unfold CertificateWire.verifyRaw
    cases hc : readAll (CertificateWire.readCertificate n gs.length) certificate with
    | none => rfl
    | some c =>
      simp only [Option.map_some, Option.bind_some, check_eq]
      have hv := validate_claim gs c
      cases hh : CertifiedPermutation.validate gs (CertificateWire.decode gs c) <;>
        simpa [hh, eraseCertificate] using hv.symm

theorem accepts_eq (input certificate : List Bool) :
    accepts input certificate = (CertificateWire.verify input certificate).isSome := by
  rw [accepts, verifyClaim_eq, Option.isSome_map]

/-- Each returned tag comes with a valid classical claim for the supplied input. -/
theorem verifyClaim_sound (input certificate : List Bool) (tag : ℕ)
    (h : verifyClaim input certificate = some tag) :
    ∃ r : CertificateWire.VerifiedInput,
      CertificateWire.verify input certificate = some r ∧
      claimCode r.result.certificate.claim = tag ∧
      CertifiedPermutation.ClaimHolds r.result.certificate := by
  rw [verifyClaim_eq] at h
  obtain ⟨r, hr, ht⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r, hr, ht, r.sound⟩

/-- The uniform finite-control TM2 machine and its polynomial transition bound. -/
theorem verifyClaim_tm2 :
    Nonempty (TM2ComputableInPolyTime enc enc
      (fun p : List Bool × List Bool => verifyClaim p.1 p.2)) := by
  simpa only [PolyTime] using polyTime_verifyClaim

/-- The polynomial bound may be expressed in the sum of the two raw bit lengths. -/
theorem verifyClaim_tm2_total_length :
    ∃ M : TM2ComputableAux Bool Bool, ∃ P : Polynomial ℕ,
      ∀ input certificate : List Bool,
        Nonempty (TM2OutputsInTime M.tm
          ((enc (input, certificate)).map M.inputAlphabet.symm)
          (some ((enc (verifyClaim input certificate)).map M.outputAlphabet.symm))
          (P.eval (input.length + certificate.length))) := by
  obtain ⟨M⟩ := verifyClaim_tm2
  refine ⟨M.toTM2ComputableAux,
    M.time.comp (Polynomial.C 8 * Polynomial.X + Polynomial.C 4), ?_⟩
  intro input certificate
  have h := M.outputsFun (input, certificate)
  refine ⟨⟨h.toEvalsTo, h.steps_le_m.trans ?_⟩⟩
  rw [Polynomial.eval_comp]
  apply Polynomial.eval_le_eval M.time
  have hl : (enc (input, certificate)).length ≤
      8 * (input.length + certificate.length) + 4 := by
    rw [length_enc_prod, length_enc_bits, length_enc_bits]
    omega
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] using hl

end TauCeti.CertificateRuntime
