/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.FamilyTables
public import TauCeti.GroupTheory.Perm.Certificates.RuntimeWriter
public import TauCeti.GroupTheory.Perm.Certificates.RuntimeEndToEnd

/-!
# Uniform polynomial-time generators for the explicit successful families

Each candidate machine reads the unary degree from the supplied group input.
Its finite control is independent of that degree. The table scans construct
exactly the previously certified witnesses, so every seed succeeds on the
symmetric family in degree at least five and the alternating family in degree
at least six. The bounded TM2 runner therefore has zero failure probability
for positive confidence parameters on these families.
-/

@[expose] public section

namespace TauCeti.UniformFamilies

open Computability BitEncoding Turing PermutationTables
open CertificateRuntime

/-- The increasing natural indices outside the fixed point zero. -/
def complement (n : ℕ) : List ℕ :=
  (List.range n).filter fun x => !decide (x = 0)

/-- The empty or one-letter transposition orbit witness. -/
def symmetricOrbit (n : ℕ) (hs : List Table) (x : ℕ) : PermutationTables.Word :=
  bif decide (x = 1) then [] else [(FamilyTables.tableIndex hs
    (FamilyTables.swapTable n 1 x), false)]

/-- The empty or one-letter three-cycle orbit witness. -/
def alternatingOrbit (n : ℕ) (hs : List Table) (x : ℕ) : PermutationTables.Word :=
  bif decide (x = 1) then [] else [(FamilyTables.tableIndex hs
    (FamilyTables.tripleTable n 1 x (bif decide (x = 2) then 3 else 2)), false)]

/-- Construct the erased symmetric certificate by polynomially bounded table scans. -/
def symmetricCertificate (n : ℕ) : Certificate :=
  let gs := FamilyTables.swaps n false
  let hs := FamilyTables.swaps n true
  (2, FamilyTables.wordsFor gs hs, (List.range n).map fun x => decide (x = 0),
    1, (complement n).map (symmetricOrbit n hs),
    [([], FamilyTables.tableIndex hs (FamilyTables.swapTable n 1 2), false)])

/-- Construct the erased alternating certificate by polynomially bounded table scans. -/
def alternatingCertificate (n : ℕ) : Certificate :=
  let gs := FamilyTables.triples n false
  let hs := FamilyTables.triples n true
  (1, FamilyTables.wordsFor gs hs, (List.range n).map fun x => decide (x = 0),
    1, (complement n).map (alternatingOrbit n hs),
    [([], FamilyTables.tableIndex hs (FamilyTables.tripleTable n 1 2 3), false)])

/-- Read the degree prefix, using zero for a malformed prefix. -/
def degreeOf (input : List Bool) : ℕ :=
  ((BinaryCodec.readUnary input).map Prod.fst).getD 0

/-- The uniform symmetric candidate generator; it does not require random bits. -/
def symmetricCandidate (input _seed : List Bool) : List Bool :=
  let n := degreeOf input
  writeCertificate (n, (FamilyTables.swaps n false).length) (symmetricCertificate n)

/-- The uniform alternating candidate generator; it does not require random bits. -/
def alternatingCandidate (input _seed : List Bool) : List Bool :=
  let n := degreeOf input
  writeCertificate (n, (FamilyTables.triples n false).length) (alternatingCertificate n)

@[fun_prop] theorem polyTime_complement : PolyTime complement := by
  unfold complement
  fun_prop

@[fun_prop] theorem polyTime_symmetricOrbit :
    PolyTime (fun p : ℕ × List Table × ℕ => symmetricOrbit p.1 p.2.1 p.2.2) := by
  unfold symmetricOrbit
  fun_prop

@[fun_prop] theorem polyTime_alternatingOrbit :
    PolyTime (fun p : ℕ × List Table × ℕ => alternatingOrbit p.1 p.2.1 p.2.2) := by
  unfold alternatingOrbit
  fun_prop

@[fun_prop] theorem polyTime_symmetricCertificate : PolyTime symmetricCertificate := by
  unfold symmetricCertificate
  fun_prop

@[fun_prop] theorem polyTime_alternatingCertificate : PolyTime alternatingCertificate := by
  unfold alternatingCertificate
  fun_prop

@[fun_prop] theorem polyTime_degreeOf : PolyTime degreeOf := by
  unfold degreeOf
  exact PolyTime.comp
    (show PolyTime (fun p : Option (ℕ × List Bool) => (p.map Prod.fst).getD 0) by fun_prop)
    BinaryCodec.polyTime_readUnary

@[fun_prop] theorem polyTime_symmetricCandidate :
    PolyTime (fun p : List Bool × List Bool => symmetricCandidate p.1 p.2) := by
  unfold symmetricCandidate
  fun_prop

@[fun_prop] theorem polyTime_alternatingCandidate :
    PolyTime (fun p : List Bool × List Bool => alternatingCandidate p.1 p.2) := by
  unfold alternatingCandidate
  fun_prop

/-- Index casts have no effect on the erased signed word. -/
theorem erase_castWord {a b : ℕ} (h : a = b) (word : FinitePermutation.Word a) :
    eraseWord (CertificateConstruction.castWord h word) = eraseWord word := by
  simp only [eraseWord, CertificateConstruction.castWord, List.map_map, Function.comp_def,
    Fin.val_cast]

/-- The natural complement list is the erasure of the bounded complement list. -/
theorem complement_eq (n : ℕ) :
    complement n =
      (CertificateWire.complement (@SuccessfulFamilies.fixedMask n)).map Fin.val := by
  simp only [complement, CertificateWire.complement, SuccessfulFamilies.fixedMask,
    ← List.map_coe_finRange_eq_range, List.filter_map, Function.comp_def]

/-- The natural fixed-point mask is the bounded mask in point order. -/
theorem mask_eq (n : ℕ) :
    (List.range n).map (fun x => decide (x = 0)) =
      List.ofFn (@SuccessfulFamilies.fixedMask n) := by
  rw [range_eq_ofFn, List.map_ofFn]
  rfl

/-- The symmetric orbit scan returns the certified bounded word. -/
theorem symmetricOrbit_eq {n : ℕ} (hn : 5 ≤ n)
    (i : Fin (CertificateWire.complement (@SuccessfulFamilies.fixedMask n)).length) :
    symmetricOrbit n (FamilyTables.swaps n true)
      ((CertificateWire.complement (@SuccessfulFamilies.fixedMask n)).get i).val =
      eraseWord (SuccessfulFamilies.symmetricOrbit hn i) := by
  let x := (CertificateWire.complement (@SuccessfulFamilies.fixedMask n)).get i
  let b := SuccessfulFamilies.base (by omega : 4 ≤ n)
  have hb : b.val = 1 := rfl
  have hx : x = b ↔ x.val = 1 := by simp [Fin.ext_iff, hb]
  unfold symmetricOrbit SuccessfulFamilies.symmetricOrbit
  change (bif decide (x.val = 1) then [] else
    [(FamilyTables.tableIndex (FamilyTables.swaps n true)
      (FamilyTables.swapTable n 1 x.val), false)]) = _
  by_cases he : x = b
  · rw [Bool.cond_decide, ite_eq_left (hx.mp he), dite_eq_left he]
    rfl
  · have hm : Equiv.swap b x ∈ SuccessfulFamilies.swaps n SuccessfulFamilies.allowed :=
      (SuccessfulFamilies.mem_swaps_iff _ _).mpr ⟨b, x,
        by simp [b, SuccessfulFamilies.base, SuccessfulFamilies.allowed,
          SuccessfulFamilies.fixedMask],
        by simpa [x, SuccessfulFamilies.allowed, SuccessfulFamilies.fixedMask] using
          SuccessfulFamilies.complement_ne_zero i,
        Ne.symm he, rfl⟩
    have ht : FamilyTables.swapTable n 1 x.val = ofPerm (Equiv.swap b x) := by
      simpa only [hb] using FamilyTables.swapTable_ofFin b x
    rw [Bool.cond_decide, ite_eq_right (fun hv => he (hx.mpr hv)), dite_eq_right he]
    simp only [eraseWord, List.map_cons, List.map_nil]
    rw [ht, FamilyTables.swaps_fixed_eq, FamilyTables.tableIndex_ofPerm _ _ hm]

/-- The alternating orbit scan returns the certified bounded word. -/
theorem alternatingOrbit_eq {n : ℕ} (hn : 6 ≤ n)
    (i : Fin (CertificateWire.complement (@SuccessfulFamilies.fixedMask n)).length) :
    alternatingOrbit n (FamilyTables.triples n true)
      ((CertificateWire.complement (@SuccessfulFamilies.fixedMask n)).get i).val =
      eraseWord (SuccessfulFamilies.alternatingOrbit hn i) := by
  let x := (CertificateWire.complement (@SuccessfulFamilies.fixedMask n)).get i
  let b := SuccessfulFamilies.base (by omega : 4 ≤ n)
  let z := SuccessfulFamilies.auxiliary hn x
  have hb : b.val = 1 := rfl
  have hx : x = b ↔ x.val = 1 := by simp [Fin.ext_iff, hb]
  have hz : z.val = (bif decide (x.val = 2) then 3 else 2) := by
    simp only [z, SuccessfulFamilies.auxiliary, SuccessfulFamilies.third,
      SuccessfulFamilies.second, Bool.cond_decide]
    split_ifs <;> rfl
  unfold alternatingOrbit SuccessfulFamilies.alternatingOrbit
  change (bif decide (x.val = 1) then [] else
    [(FamilyTables.tableIndex (FamilyTables.triples n true)
      (FamilyTables.tripleTable n 1 x.val (bif decide (x.val = 2) then 3 else 2)),
      false)]) = _
  by_cases he : x = b
  · rw [Bool.cond_decide, ite_eq_left (hx.mp he), dite_eq_left he]
    rfl
  · have hm : Equiv.swap b x * Equiv.swap x z ∈
        SuccessfulFamilies.triples n SuccessfulFamilies.allowed :=
      (SuccessfulFamilies.mem_triples_iff _ _).mpr ⟨b, x, z,
        by simp [b, SuccessfulFamilies.base, SuccessfulFamilies.allowed,
          SuccessfulFamilies.fixedMask],
        by simpa [x, SuccessfulFamilies.allowed, SuccessfulFamilies.fixedMask] using
          SuccessfulFamilies.complement_ne_zero i,
        (SuccessfulFamilies.auxiliary_spec hn x).1, Ne.symm he,
        (SuccessfulFamilies.auxiliary_spec hn x).2.1,
        (SuccessfulFamilies.auxiliary_spec hn x).2.2, rfl⟩
    have ht : FamilyTables.tripleTable n 1 x.val
        (bif decide (x.val = 2) then 3 else 2) =
          ofPerm (Equiv.swap b x * Equiv.swap x z) := by
      simpa only [hb, hz] using FamilyTables.tripleTable_ofFin b x z
    rw [Bool.cond_decide, ite_eq_right (fun hv => he (hx.mpr hv)), dite_eq_right he]
    simp only [eraseWord, List.map_cons, List.map_nil]
    rw [ht, FamilyTables.triples_fixed_eq, FamilyTables.tableIndex_ofPerm _ _ hm]

/-- The symmetric prime-cycle scan returns the certified first transposition index. -/
theorem symmetricIndex_eq {n : ℕ} (hn : 5 ≤ n) :
    FamilyTables.tableIndex (FamilyTables.swaps n true) (FamilyTables.swapTable n 1 2) =
      (SuccessfulFamilies.symmetricIndex hn).val := by
  let b := SuccessfulFamilies.base (by omega : 4 ≤ n)
  let c := SuccessfulFamilies.second (by omega : 4 ≤ n)
  have ht : FamilyTables.swapTable n 1 2 = ofPerm (Equiv.swap b c) :=
    FamilyTables.swapTable_ofFin b c
  have hm : Equiv.swap b c ∈ SuccessfulFamilies.swaps n SuccessfulFamilies.allowed := by
    rw [← SuccessfulFamilies.symmetricIndex_spec hn]
    exact List.get_mem _ _
  rw [ht, FamilyTables.swaps_fixed_eq, FamilyTables.tableIndex_ofPerm _ _ hm]
  rfl

/-- The alternating prime-cycle scan returns the certified first three-cycle index. -/
theorem alternatingIndex_eq {n : ℕ} (hn : 6 ≤ n) :
    FamilyTables.tableIndex (FamilyTables.triples n true)
      (FamilyTables.tripleTable n 1 2 3) =
      (SuccessfulFamilies.alternatingIndex hn).val := by
  let b := SuccessfulFamilies.base (by omega : 4 ≤ n)
  let c := SuccessfulFamilies.second (by omega : 4 ≤ n)
  let d := SuccessfulFamilies.third (by omega : 4 ≤ n)
  have ht : FamilyTables.tripleTable n 1 2 3 =
      ofPerm (Equiv.swap b c * Equiv.swap c d) :=
    FamilyTables.tripleTable_ofFin b c d
  have hm : Equiv.swap b c * Equiv.swap c d ∈
      SuccessfulFamilies.triples n SuccessfulFamilies.allowed := by
    rw [← SuccessfulFamilies.alternatingIndex_spec hn]
    exact List.get_mem _ _
  rw [ht, FamilyTables.triples_fixed_eq, FamilyTables.tableIndex_ofPerm _ _ hm]
  rfl

/-- The uniform symmetric construction is the erasure of the valid dependent certificate. -/
theorem symmetricCertificate_eq {n : ℕ} (hn : 5 ≤ n) :
    symmetricCertificate n = eraseCertificate (SuccessfulFamilies.symmetricCertificate hn) := by
  have hwords := FamilyTables.wordsFor_ofPerm
    (SuccessfulFamilies.swaps n (fun _ => true))
    (SuccessfulFamilies.swaps n SuccessfulFamilies.allowed)
    (SuccessfulFamilies.swaps_subset SuccessfulFamilies.allowed)
  have horbits : (complement n).map (symmetricOrbit n (FamilyTables.swaps n true)) =
      List.ofFn (fun i => eraseWord (SuccessfulFamilies.symmetricOrbit hn i)) := by
    rw [complement_eq, List.map_map]
    conv_lhs =>
      rw [← List.ofFn_get (CertificateWire.complement (@SuccessfulFamilies.fixedMask n)),
        List.map_ofFn]
    congr 1
    funext i
    exact symmetricOrbit_eq hn i
  simp only [symmetricCertificate, SuccessfulFamilies.symmetricCertificate,
    CertificateConstruction.make, eraseCertificate, claimCode, erase_castWord,
    CertificateConstruction.oneFactor, CertificateWire.factorList, List.map_cons, List.map_nil,
    eraseFactor, Fin.val_cast]
  rw [mask_eq, horbits, symmetricIndex_eq hn, FamilyTables.swaps_all_eq,
    FamilyTables.swaps_fixed_eq, hwords]
  rfl

/-- The uniform alternating construction is the erasure of the valid dependent certificate. -/
theorem alternatingCertificate_eq {n : ℕ} (hn : 6 ≤ n) :
    alternatingCertificate n =
      eraseCertificate (SuccessfulFamilies.alternatingCertificate hn) := by
  have hwords := FamilyTables.wordsFor_ofPerm
    (SuccessfulFamilies.triples n (fun _ => true))
    (SuccessfulFamilies.triples n SuccessfulFamilies.allowed)
    (SuccessfulFamilies.triples_subset SuccessfulFamilies.allowed)
  have horbits : (complement n).map (alternatingOrbit n (FamilyTables.triples n true)) =
      List.ofFn (fun i => eraseWord (SuccessfulFamilies.alternatingOrbit hn i)) := by
    rw [complement_eq, List.map_map]
    conv_lhs =>
      rw [← List.ofFn_get (CertificateWire.complement (@SuccessfulFamilies.fixedMask n)),
        List.map_ofFn]
    congr 1
    funext i
    exact alternatingOrbit_eq hn i
  simp only [alternatingCertificate, SuccessfulFamilies.alternatingCertificate,
    CertificateConstruction.make, eraseCertificate, claimCode, erase_castWord,
    CertificateConstruction.oneFactor, CertificateWire.factorList, List.map_cons, List.map_nil,
    eraseFactor, Fin.val_cast]
  rw [mask_eq, horbits, alternatingIndex_eq hn, FamilyTables.triples_all_eq,
    FamilyTables.triples_fixed_eq, hwords]
  rfl

/-- The group wire begins with exactly its unary degree prefix. -/
theorem degreeOf_writeGroup (g : CertificateWire.GroupData) :
    degreeOf (CertificateWire.writeGroup g) = g.fst := by
  simp [degreeOf, CertificateWire.writeGroup, BinaryCodec.readUnary_writeUnary]

/-- One degree-reading machine produces the canonical symmetric witness for every seed. -/
theorem symmetricCandidate_eq {n : ℕ} (hn : 5 ≤ n) (seed : List Bool) :
    symmetricCandidate (EndToEnd.symmetricInput n) seed =
      CertificateWire.writeCertificate (SuccessfulFamilies.symmetricCertificate hn) := by
  simp only [symmetricCandidate, EndToEnd.symmetricInput, degreeOf_writeGroup]
  rw [symmetricCertificate_eq hn, FamilyTables.swaps_all_eq, List.length_map,
    writeCertificate_erase]

/-- One degree-reading machine produces the canonical alternating witness for every seed. -/
theorem alternatingCandidate_eq {n : ℕ} (hn : 6 ≤ n) (seed : List Bool) :
    alternatingCandidate (EndToEnd.alternatingInput n) seed =
      CertificateWire.writeCertificate (SuccessfulFamilies.alternatingCertificate hn) := by
  simp only [alternatingCandidate, EndToEnd.alternatingInput, degreeOf_writeGroup]
  rw [alternatingCertificate_eq hn, FamilyTables.triples_all_eq, List.length_map,
    writeCertificate_erase]

/-- Every seed is accepted on the symmetric family in degree at least five. -/
theorem symmetricCandidate_accepted {n : ℕ} (hn : 5 ≤ n) (seed : List Bool) :
    (CertificateWire.verify (EndToEnd.symmetricInput n)
      (symmetricCandidate (EndToEnd.symmetricInput n) seed)).isSome = true := by
  rw [symmetricCandidate_eq hn]
  exact EndToEnd.symmetric_accepted hn

/-- Every seed is accepted on the alternating family in degree at least six. -/
theorem alternatingCandidate_accepted {n : ℕ} (hn : 6 ≤ n) (seed : List Bool) :
    (CertificateWire.verify (EndToEnd.alternatingInput n)
      (alternatingCandidate (EndToEnd.alternatingInput n) seed)).isSome = true := by
  rw [alternatingCandidate_eq hn]
  exact EndToEnd.alternating_accepted hn

/-- Acceptance probability is one even with the empty seed used by the symmetric generator. -/
theorem symmetric_acceptance_probability {n : ℕ} (hn : 5 ≤ n) :
    FiniteSeeds.uniformProbability (Fin 0 → Bool) (fun seed =>
      (CertificateWire.verify (EndToEnd.symmetricInput n)
        (symmetricCandidate (EndToEnd.symmetricInput n) (List.ofFn seed))).isSome = true) = 1 := by
  classical
  simp [FiniteSeeds.uniformProbability, symmetricCandidate_accepted hn]

/-- Acceptance probability is one even with the empty seed used by the alternating generator. -/
theorem alternating_acceptance_probability {n : ℕ} (hn : 6 ≤ n) :
    FiniteSeeds.uniformProbability (Fin 0 → Bool) (fun seed =>
      (CertificateWire.verify (EndToEnd.alternatingInput n)
        (alternatingCandidate (EndToEnd.alternatingInput n)
          (List.ofFn seed))).isSome = true) = 1 := by
  classical
  simp [FiniteSeeds.uniformProbability, alternatingCandidate_accepted hn]

/-- With `R = 1` and no random bits, positive confidence returns a symmetric claim. -/
theorem symmetric_seededResult_accepts {n k : ℕ} (hn : 5 ≤ n) (hk : 0 < k)
    (seeds : Fin (k * (1 : Polynomial ℕ).eval (EndToEnd.symmetricInput n).length) →
      Fin ((0 : Polynomial ℕ).eval (EndToEnd.symmetricInput n).length) → Bool) :
    (seededResult symmetricCandidate 1 0 (EndToEnd.symmetricInput n) k seeds).isSome = true := by
  cases h : seededResult symmetricCandidate 1 0 (EndToEnd.symmetricInput n) k seeds with
  | none =>
    have hf := (seededResult_eq_none_iff _ _ _ _ _ seeds).mp h
    have hs := BoundedRunner.run_isSome_of_all_success
      (fun seed => CertificateWire.verify (EndToEnd.symmetricInput n)
        (symmetricCandidate (EndToEnd.symmetricInput n) (List.ofFn seed)))
      seeds (by simpa only [Polynomial.eval_one, Nat.mul_one] using hk)
      (fun seed => symmetricCandidate_accepted hn (List.ofFn seed))
    rw [show BoundedRunner.run _ seeds = none from hf] at hs
    cases hs
  | some value => rfl

/-- With `R = 1` and no random bits, positive confidence returns an alternating claim. -/
theorem alternating_seededResult_accepts {n k : ℕ} (hn : 6 ≤ n) (hk : 0 < k)
    (seeds : Fin (k * (1 : Polynomial ℕ).eval (EndToEnd.alternatingInput n).length) →
      Fin ((0 : Polynomial ℕ).eval (EndToEnd.alternatingInput n).length) → Bool) :
    (seededResult alternatingCandidate 1 0
      (EndToEnd.alternatingInput n) k seeds).isSome = true := by
  cases h : seededResult alternatingCandidate 1 0 (EndToEnd.alternatingInput n) k seeds with
  | none =>
    have hf := (seededResult_eq_none_iff _ _ _ _ _ seeds).mp h
    have hs := BoundedRunner.run_isSome_of_all_success
      (fun seed => CertificateWire.verify (EndToEnd.alternatingInput n)
        (alternatingCandidate (EndToEnd.alternatingInput n) (List.ofFn seed)))
      seeds (by simpa only [Polynomial.eval_one, Nat.mul_one] using hk)
      (fun seed => alternatingCandidate_accepted hn (List.ofFn seed))
    rw [show BoundedRunner.run _ seeds = none from hf] at hs
    cases hs
  | some value => rfl

/-- The symmetric family's exact failure probability is zero for positive confidence. -/
theorem symmetric_unknown_probability {n k : ℕ} (hn : 5 ≤ n) (hk : 0 < k) :
    FiniteSeeds.uniformProbability
      (Fin (k * (1 : Polynomial ℕ).eval (EndToEnd.symmetricInput n).length) →
        Fin ((0 : Polynomial ℕ).eval (EndToEnd.symmetricInput n).length) → Bool)
      (fun seeds => seededResult symmetricCandidate 1 0 (EndToEnd.symmetricInput n) k seeds =
        none) = 0 := by
  classical
  have hnone (seeds : Fin (k * (1 : Polynomial ℕ).eval (EndToEnd.symmetricInput n).length) →
      Fin ((0 : Polynomial ℕ).eval (EndToEnd.symmetricInput n).length) → Bool) :
      seededResult symmetricCandidate 1 0 (EndToEnd.symmetricInput n) k seeds ≠ none := by
    intro he
    have h := symmetric_seededResult_accepts hn hk seeds
    rw [he] at h
    cases h
  simp [FiniteSeeds.uniformProbability, hnone]

/-- The alternating family's exact failure probability is zero for positive confidence. -/
theorem alternating_unknown_probability {n k : ℕ} (hn : 6 ≤ n) (hk : 0 < k) :
    FiniteSeeds.uniformProbability
      (Fin (k * (1 : Polynomial ℕ).eval (EndToEnd.alternatingInput n).length) →
        Fin ((0 : Polynomial ℕ).eval (EndToEnd.alternatingInput n).length) → Bool)
      (fun seeds => seededResult alternatingCandidate 1 0 (EndToEnd.alternatingInput n) k seeds =
        none) = 0 := by
  classical
  have hnone (seeds : Fin (k * (1 : Polynomial ℕ).eval (EndToEnd.alternatingInput n).length) →
      Fin ((0 : Polynomial ℕ).eval (EndToEnd.alternatingInput n).length) → Bool) :
      seededResult alternatingCandidate 1 0 (EndToEnd.alternatingInput n) k seeds ≠ none := by
    intro he
    have h := alternating_seededResult_accepts hn hk seeds
    rw [he] at h
    cases h
  simp [FiniteSeeds.uniformProbability, hnone]

/-- One finite-control TM2 machine runs the symmetric generator and verifier in polynomial time,
uniformly in the raw input, its degree, and the unary confidence parameter. -/
theorem symmetric_tm2 :
    ∃ M : TM2ComputableAux Bool Bool, ∃ P : Polynomial ℕ,
      ∀ (input : List Bool) (k : ℕ)
        (seeds : Fin (k * (1 : Polynomial ℕ).eval input.length) →
          Fin ((0 : Polynomial ℕ).eval input.length) → Bool),
        Nonempty (TM2OutputsInTime M.tm
          ((enc (input, k, seedList seeds)).map M.inputAlphabet.symm)
          (some ((enc (seededResult symmetricCandidate 1 0 input k seeds)).map
            M.outputAlphabet.symm))
          (P.eval (input.length + k))) :=
  seededResult_tm2 symmetricCandidate 1 0 polyTime_symmetricCandidate

/-- One finite-control TM2 machine runs the alternating generator and verifier in polynomial time,
uniformly in the raw input, its degree, and the unary confidence parameter. -/
theorem alternating_tm2 :
    ∃ M : TM2ComputableAux Bool Bool, ∃ P : Polynomial ℕ,
      ∀ (input : List Bool) (k : ℕ)
        (seeds : Fin (k * (1 : Polynomial ℕ).eval input.length) →
          Fin ((0 : Polynomial ℕ).eval input.length) → Bool),
        Nonempty (TM2OutputsInTime M.tm
          ((enc (input, k, seedList seeds)).map M.inputAlphabet.symm)
          (some ((enc (seededResult alternatingCandidate 1 0 input k seeds)).map
            M.outputAlphabet.symm))
          (P.eval (input.length + k))) :=
  seededResult_tm2 alternatingCandidate 1 0 polyTime_alternatingCandidate

end TauCeti.UniformFamilies
