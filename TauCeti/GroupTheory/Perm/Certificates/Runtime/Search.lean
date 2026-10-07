/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Runtime.Verifier
public import TauCeti.GroupTheory.Perm.Certificates.Search

/-!
# Polynomial-time bounded certificate search

The machine returns the first accepted certificate in seed order. Its transition
bound includes generation, verification, and the clocked traversal of the capped
seed list. Candidate generation has an explicit uniform polynomial-time hypothesis.
-/

@[expose] public section

namespace TauCeti.CertificateRuntime

open Computability BitEncoding Turing

/-- Retain a previous success, or check the next candidate. -/
def trial (input : List Bool) (old : Option (List Bool)) (certificate : List Bool) :
    Option (List Bool) :=
  bif old.isSome then old else bif accepts input certificate then some certificate else none

/-- Return the first accepted certificate, using a bounded fold. -/
def scan (input : List Bool) (certificates : List (List Bool)) : Option (List Bool) :=
  certificates.foldl (trial input) none

@[fun_prop] theorem polyTime_trial :
    PolyTime (fun p : List Bool × Option (List Bool) × List Bool =>
      trial p.1 p.2.1 p.2.2) := by
  unfold trial
  fun_prop

@[fun_prop] theorem polyTime_scan :
    PolyTime (fun p : List Bool × List (List Bool) => scan p.1 p.2) := by
  have hfold := PolyTime.foldl polyTime_trial 0 fun input old certificate => by
    cases old with
    | none =>
      cases h : accepts input certificate <;>
        simp [trial, h, enc_some, enc_none]
      omega
    | some previous => simp only [trial, Option.isSome_some, Bool.cond_true]; omega
  exact PolyTime.comp
    (f := fun p : List Bool × List (List Bool) => (p.1, none, p.2)) hfold (by fun_prop)

theorem foldl_trial_some (input : List Bool) (certificates : List (List Bool))
    (previous : List Bool) :
    certificates.foldl (trial input) (some previous) = some previous := by
  induction certificates with
  | nil => rfl
  | cons certificate rest ih => simpa [trial] using ih

theorem scan_eq (input : List Bool) (certificates : List (List Bool)) :
    scan input certificates = BoundedRunner.firstSuccess
      (fun certificate => bif accepts input certificate then some certificate else none)
      certificates := by
  induction certificates with
  | nil => rfl
  | cons certificate rest ih =>
    cases h : accepts input certificate with
    | false => simpa [scan, trial, BoundedRunner.firstSuccess, h] using ih
    | true => simp [scan, trial, BoundedRunner.firstSuccess, h, foldl_trial_some]

theorem scan_eq_none_iff (input : List Bool) (certificates : List (List Bool)) :
    scan input certificates = none ↔
      ∀ certificate ∈ certificates, CertificateWire.verify input certificate = none := by
  rw [scan_eq, BoundedRunner.firstSuccess_eq_none_iff]
  apply forall_congr'
  intro certificate
  apply imp_congr_right
  intro _
  rw [accepts_eq]
  cases CertificateWire.verify input certificate <;> simp

theorem scan_sound (input : List Bool) (certificates : List (List Bool))
    (certificate : List Bool) (h : scan input certificates = some certificate) :
    certificate ∈ certificates ∧
      ∃ r : CertificateWire.VerifiedInput,
        CertificateWire.verify input certificate = some r ∧
        CertifiedPermutation.ClaimHolds r.result.certificate := by
  rw [scan_eq] at h
  obtain ⟨c, hc, hv⟩ := BoundedRunner.firstSuccess_eq_some_mem _ _ _ h
  cases ha : accepts input c with
  | false => simp [ha] at hv
  | true =>
    have he : c = certificate := by simpa [ha] using hv
    subst c
    rw [accepts] at ha
    cases ht : verifyClaim input certificate with
    | none => simp [ht] at ha
    | some tag =>
      obtain ⟨r, hr, _, hs⟩ := verifyClaim_sound input certificate tag ht
      exact ⟨hc, r, hr, hs⟩

/-- Generate candidates from the supplied seeds and retain the first verified result. -/
def search (candidate : List Bool → List Bool → List Bool) (input : List Bool)
    (seeds : List (List Bool)) : Option (List Bool) :=
  scan input (seeds.map (candidate input))

@[fun_prop] theorem polyTime_search (candidate : List Bool → List Bool → List Bool)
    (hc : PolyTime (fun p : List Bool × List Bool => candidate p.1 p.2)) :
    PolyTime (fun p : List Bool × List (List Bool) => search candidate p.1 p.2) := by
  have hm : PolyTime (fun p : List Bool × List (List Bool) =>
      p.2.map (candidate p.1)) :=
    PolyTime.map₂ (f := fun p seed => candidate p.1 seed)
      (PolyTime.comp
        (f := fun p : (List Bool × List (List Bool)) × List Bool => (p.1.1, p.2))
        hc (by fun_prop)) PolyTime.snd
  exact PolyTime.comp polyTime_scan (PolyTime.pair PolyTime.fst hm)

theorem search_eq_none_iff (candidate : List Bool → List Bool → List Bool)
    (input : List Bool) (seeds : List (List Bool)) :
    search candidate input seeds = none ↔
      ∀ seed ∈ seeds, CertificateWire.verify input (candidate input seed) = none := by
  simp [search, scan_eq_none_iff]

theorem search_sound (candidate : List Bool → List Bool → List Bool)
    (input : List Bool) (seeds : List (List Bool)) (certificate : List Bool)
    (h : search candidate input seeds = some certificate) :
    ∃ seed ∈ seeds, candidate input seed = certificate ∧
      ∃ r : CertificateWire.VerifiedInput,
        CertificateWire.verify input certificate = some r ∧
        CertifiedPermutation.ClaimHolds r.result.certificate := by
  obtain ⟨hm, hs⟩ := scan_sound input _ certificate h
  obtain ⟨seed, hseed, he⟩ := List.mem_map.mp hm
  exact ⟨seed, hseed, he, hs⟩

/-- Cap the number of trials at `k * R(input.length)`. The confidence input is unary. -/
def boundedSearch (candidate : List Bool → List Bool → List Bool) (R : Polynomial ℕ)
    (input : List Bool) (k : ℕ) (seeds : List (List Bool)) : Option (List Bool) :=
  search candidate input (seeds.take (k * R.eval input.length))

@[fun_prop] theorem polyTime_boundedSearch
    (candidate : List Bool → List Bool → List Bool) (R : Polynomial ℕ)
    (hc : PolyTime (fun p : List Bool × List Bool => candidate p.1 p.2)) :
    PolyTime (fun p : List Bool × ℕ × List (List Bool) =>
      boundedSearch candidate R p.1 p.2.1 p.2.2) := by
  have hcount : PolyTime (fun p : List Bool × ℕ × List (List Bool) =>
      p.2.1 * R.eval p.1.length) := by fun_prop
  exact PolyTime.comp (polyTime_search candidate hc)
    (PolyTime.pair PolyTime.fst (PolyTime.comp PolyTime.take
      (PolyTime.pair hcount (by fun_prop))))

/-- Bound the framing overhead of a polynomial number of polynomial-length seeds. -/
noncomputable def seedEnvelope (R B : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 10 * Polynomial.X +
    (Polynomial.X * R) * (Polynomial.C 8 * B + Polynomial.C 4) + Polynomial.C 5

theorem length_enc_searchInput_le (R B : Polynomial ℕ)
    (input : List Bool) (k : ℕ) (seeds : List (List Bool))
    (hcount : seeds.length ≤ k * R.eval input.length)
    (hbits : ∀ seed ∈ seeds, seed.length ≤ B.eval input.length) :
    (enc (input, k, seeds)).length ≤ (seedEnvelope R B).eval (input.length + k) := by
  have hlist := length_enc_list_le seeds (B := 4 * B.eval input.length + 1)
    fun seed hseed => by
      have := hbits seed hseed
      rw [length_enc_bits]
      omega
  have hR := Polynomial.eval_le_eval R (show input.length ≤ input.length + k by omega)
  have hB := Polynomial.eval_le_eval B (show input.length ≤ input.length + k by omega)
  have htrials : seeds.length ≤ (input.length + k) * R.eval (input.length + k) :=
    hcount.trans (Nat.mul_le_mul (by omega) hR)
  have hseedsize : 2 * (4 * B.eval input.length + 1) + 2 ≤
      8 * B.eval (input.length + k) + 4 := by omega
  have htotal := hlist.trans (Nat.add_le_add_right (Nat.mul_le_mul htrials hseedsize) 1)
  simp only [length_enc_prod, length_enc_bits, length_enc_nat, seedEnvelope,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/-- One actual finite-control machine has a polynomial transition bound in `m + k`,
for every seed stream of at most `k * R(m)` seeds of length at most `B(m)`. -/
theorem boundedSearch_tm2
    (candidate : List Bool → List Bool → List Bool) (R B : Polynomial ℕ)
    (hc : PolyTime (fun p : List Bool × List Bool => candidate p.1 p.2)) :
    ∃ M : TM2ComputableAux Bool Bool, ∃ P : Polynomial ℕ,
      ∀ (input : List Bool) (k : ℕ) (seeds : List (List Bool)),
        seeds.length ≤ k * R.eval input.length →
        (∀ seed ∈ seeds, seed.length ≤ B.eval input.length) →
        Nonempty (TM2OutputsInTime M.tm
          ((enc (input, k, seeds)).map M.inputAlphabet.symm)
          (some ((enc (boundedSearch candidate R input k seeds)).map M.outputAlphabet.symm))
          (P.eval (input.length + k))) := by
  have hm : Nonempty (TM2ComputableInPolyTime enc enc
      (fun p : List Bool × ℕ × List (List Bool) =>
        boundedSearch candidate R p.1 p.2.1 p.2.2)) := by
    simpa only [PolyTime] using polyTime_boundedSearch candidate R hc
  obtain ⟨M⟩ := hm
  refine ⟨M.toTM2ComputableAux, M.time.comp (seedEnvelope R B), ?_⟩
  intro input k seeds hcount hbits
  have h := M.outputsFun (input, k, seeds)
  refine ⟨⟨h.toEvalsTo, h.steps_le_m.trans ?_⟩⟩
  rw [Polynomial.eval_comp]
  exact Polynomial.eval_le_eval M.time (length_enc_searchInput_le R B input k seeds hcount hbits)

end TauCeti.CertificateRuntime
