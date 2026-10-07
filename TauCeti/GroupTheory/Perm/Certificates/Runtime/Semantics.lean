/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Runtime.Check
public import TauCeti.GroupTheory.Perm.Certificates.Runtime.Wire.Erasure

/-!
# Agreement of the uniform machine checks with the classical certificate checker

Forward tables erase the proofs in permutations and bounded indices. The lemmas
below show that each check preserves its mathematical meaning under this erasure.
-/

@[expose] public section

namespace TauCeti.CertificateRuntime

open Equiv PermutationTables
open CertifiedPermutation

/-- Erase subgroup membership proofs and represent the generators by their point-image tables. -/
def subgroupTables {n : ℕ} {P : Subgroup (Perm (Fin n))} (hs : List P) : List Table :=
  hs.map fun h : P => ofPerm (h : Perm (Fin n))

theorem letter_subgroup {n : ℕ} {P : Subgroup (Perm (Fin n))} (hs : List P)
    (l : Fin hs.length × Bool) :
    letter n (subgroupTables hs) (l.1.val, l.2) =
      ofPerm (if l.2 then (hs.get l.1 : Perm (Fin n))⁻¹ else hs.get l.1) := by
  rcases l with ⟨i, b⟩
  cases b <;> simp [letter, subgroupTables, inv_ofPerm]

theorem word_subgroup {n : ℕ} {P : Subgroup (Perm (Fin n))} (hs : List P)
    (w : SignedWord hs) :
    word n (subgroupTables hs) (eraseWord w) =
      ofPerm (signedWordEval hs w : Perm (Fin n)) := by
  have h : ∀ (w : SignedWord hs) (g : Perm (Fin n)),
      (eraseWord w).foldl
        (fun t l => mul n t (letter n (subgroupTables hs) l))
        (ofPerm g) = ofPerm (g * (signedWordEval hs w : Perm (Fin n))) := by
    intro w
    induction w with
    | nil => intro g; simp [eraseWord, signedWordEval]
    | cons l w ih =>
      intro g
      rw [show eraseWord (l :: w) = (l.1.val, l.2) :: eraseWord w from rfl,
        List.foldl_cons]
      rw [letter_subgroup, mul_ofPerm, ih]
      cases hb : l.2 <;> simp [signedWordEval, hb, mul_assoc]
  have hu : ofPerm (1 : Perm (Fin n)) = List.range n := by
    simp [ofPerm, range_eq_ofFn]
  simpa only [word, ← hu, one_mul] using h w 1

theorem eraseWord_cast {a b : ℕ} (h : a = b) (w : FinitePermutation.Word a) :
    eraseWord (w.map fun l => (Fin.cast h l.1, l.2)) = eraseWord w := by
  simp [eraseWord, List.map_map]

theorem decodedTables_eq {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length) :
    decodedTables n (gs.map ofPerm) (c.generatorWords.map eraseWord) =
      subgroupTables (CertificateWire.decodedGenerators gs c) := by
  simp only [decodedTables, subgroupTables, CertificateWire.decodedGenerators,
    List.map_map]
  apply List.map_congr_left
  intro w _
  exact word_ofPerm gs w

theorem complementPoints_eq {n : ℕ} (mask : Fin n → Bool) :
    complementPoints n (List.ofFn mask) =
      (CertificateWire.complement mask).map Fin.val := by
  rw [complementPoints, range_eq_ofFn,
    List.ofFn_eq_map (f := fun x : Fin n => x.val), List.filter_map]
  simp [CertificateWire.complement, Function.comp_def, member_ofFn]

theorem fixedCount_eq {n : ℕ} (mask : Fin n → Bool) :
    fixedCount n (List.ofFn mask) = (Finset.univ.filter fun x => mask x).card := by
  have h := (List.nodup_finRange n).card_eq_countP (P := fun x => mask x = true)
  rw [List.toFinset_finRange] at h
  rw [fixedCount, range_eq_ofFn,
    List.ofFn_eq_map (f := fun x : Fin n => x.val), List.countP_map]
  simpa [Function.comp_def, member_ofFn] using h.symm

theorem fixes_eq {n : ℕ} {P : Subgroup (Perm (Fin n))} (hs : List P)
    (mask : Fin n → Bool) :
    fixes n (subgroupTables hs) (List.ofFn mask) =
      decide (∀ i : Fin hs.length, ∀ x : Fin n, mask x = true →
        (hs.get i : Perm (Fin n)) x = x) := by
  have hpoint (g : Perm (Fin n)) :
      (List.range n).all (fun x => !member (List.ofFn mask) x ||
        decide (lookup n (ofPerm g) x = x)) =
      decide (∀ x : Fin n, mask x = true → g x = x) := by
    apply Bool.eq_iff_iff.mpr
    rw [all_range, decide_eq_true_eq]
    simp [member_ofFn, lookup_ofPerm, Fin.ext_iff, or_iff_not_imp_left]
  simp only [fixes, subgroupTables, List.all_map, Function.comp_def, hpoint]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.forall_mem_iff_get, decide_eq_true_eq]
  simp only [decide_eq_true_eq]

theorem complement_nodup {n : ℕ} (mask : Fin n → Bool) :
    (CertificateWire.complement mask).Nodup :=
  (List.nodup_finRange n).filter _

theorem complementIndex_get {n : ℕ} (mask : Fin n → Bool)
    (i : Fin (CertificateWire.complement mask).length) :
    ∃ h : mask ((CertificateWire.complement mask).get i) = false,
      CertificateWire.complementIndex mask ((CertificateWire.complement mask).get i) h = i := by
  have hm := (CertificateWire.complement mask).get_mem i
  have h : mask ((CertificateWire.complement mask).get i) = false := by
    simpa [CertificateWire.complement] using (List.mem_filter.mp hm).2
  refine ⟨h, ?_⟩
  apply (complement_nodup mask).injective_get
  exact CertificateWire.complementIndex_spec mask _ h

theorem reaches_ofFn {n : ℕ} {P : Subgroup (Perm (Fin n))} (hs : List P)
    (mask : Fin n → Bool) (base : Fin n)
    (w : Fin (CertificateWire.complement mask).length → SignedWord hs) :
    reaches n (subgroupTables hs) (List.ofFn mask) base.val
      (List.ofFn fun i => eraseWord (w i)) =
    decide (∀ i, (signedWordEval hs (w i) : Perm (Fin n)) base =
      (CertificateWire.complement mask).get i) := by
  apply Bool.eq_iff_iff.mpr
  simp only [reaches, complementPoints_eq, List.length_map]
  rw [all_range, decide_eq_true_eq]
  apply forall_congr'
  intro i
  simp [i.isLt, word_subgroup, lookup_ofPerm, List.get_eq_getElem, Fin.ext_iff]

theorem eraseOrbitWord_get {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length)
    (i : Fin (CertificateWire.complement c.mask).length) :
    eraseWord ((CertificateWire.decode gs c).orbitWords
      ((CertificateWire.complement c.mask).get i)) = eraseWord (c.orbitWords i) := by
  obtain ⟨h, hi⟩ := complementIndex_get c.mask i
  simp only [CertificateWire.decode]
  rw [dite_eq_left h, hi]
  exact eraseWord_cast _ _

theorem reaches_decode {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length) :
    reaches n (subgroupTables (CertificateWire.decodedGenerators gs c))
      (List.ofFn c.mask) c.base.val (List.ofFn fun i => eraseWord (c.orbitWords i)) =
    decide (∀ x : Fin n, c.mask x = false →
      (signedWordEval (CertificateWire.decode gs c).generators
        ((CertificateWire.decode gs c).orbitWords x) : Perm (Fin n)) c.base = x) := by
  have he :
      (List.ofFn fun i => eraseWord (c.orbitWords i)) =
      List.ofFn (fun i => eraseWord ((CertificateWire.decode gs c).orbitWords
        ((CertificateWire.complement c.mask).get i))) := by
    congr 1
    funext i
    exact (eraseOrbitWord_get gs c i).symm
  rw [show CertificateWire.decodedGenerators gs c =
      (CertificateWire.decode gs c).generators from rfl,
    he, reaches_ofFn (CertificateWire.decode gs c).generators c.mask c.base
    (fun i => (CertificateWire.decode gs c).orbitWords
      ((CertificateWire.complement c.mask).get i))]
  congr 1
  apply propext
  constructor
  · intro h x hx
    simpa only [CertificateWire.complementIndex_spec] using
      h (CertificateWire.complementIndex c.mask x hx)
  · intro h i
    obtain ⟨hx, _⟩ := complementIndex_get c.mask i
    exact h _ hx

theorem factor_word {n : ℕ} (gs : List (Perm (Fin n)))
    (hs : List (FiniteAction.ambientGroup gs)) (w : FinitePermutation.Word gs.length)
    (i : Fin hs.length) (b : Bool) :
    factor n (gs.map ofPerm) (subgroupTables hs) (eraseWord w, i.val, b) =
      ofPerm (factorEval hs ⟨CertificateWire.wordToAmbient gs w, i, b⟩ :
        Perm (Fin n)) := by
  rw [factor, word_ofPerm, letter_subgroup hs (i, b), mul_ofPerm, inv_ofPerm,
    mul_ofPerm]
  cases b <;> simp [factorEval, CertificateWire.wordToAmbient]

theorem factor_decode {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length)
    (f : CertificateWire.RawFactor gs.length c.generatorWords.length) :
    factor n (gs.map ofPerm) (subgroupTables (CertificateWire.decodedGenerators gs c))
      (eraseFactor f) =
    ofPerm (factorEval (CertificateWire.decodedGenerators gs c)
      ⟨CertificateWire.wordToAmbient gs f.conjugator,
        Fin.cast (List.length_map ..).symm f.generatorIndex, f.inverted⟩ :
      Perm (Fin n)) := by
  exact factor_word gs (CertificateWire.decodedGenerators gs c) f.conjugator
    (Fin.cast (List.length_map ..).symm f.generatorIndex) f.inverted

theorem cycleTable_decode {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length) :
    cycleTable n (gs.map ofPerm) (subgroupTables (CertificateWire.decodedGenerators gs c))
      ((CertificateWire.factorList c.claim c.cycleFactors).map eraseFactor) =
      ofPerm (cycleValue (CertificateWire.decode gs c)) := by
  have h : ∀ (fs : List (CertificateWire.RawFactor gs.length c.generatorWords.length))
      (g : Perm (Fin n)),
      (fs.map eraseFactor).foldl (fun t f =>
        mul n t (factor n (gs.map ofPerm)
          (subgroupTables (CertificateWire.decodedGenerators gs c)) f)) (ofPerm g) =
      ofPerm (g * (((fs.map fun f =>
        factorEval (CertificateWire.decodedGenerators gs c)
          ⟨CertificateWire.wordToAmbient gs f.conjugator,
            Fin.cast (List.length_map ..).symm f.generatorIndex, f.inverted⟩).prod :
        FiniteAction.ambientGroup gs) : Perm (Fin n))) := by
    intro fs
    induction fs with
    | nil => intro g; simp
    | cons f fs ih =>
      intro g
      rw [List.map_cons, List.foldl_cons, factor_decode, mul_ofPerm, ih]
      simp [mul_assoc]
  have hu : ofPerm (1 : Perm (Fin n)) = List.range n := by
    simp [ofPerm, range_eq_ofFn]
  simpa only [cycleTable, ← hu, one_mul, cycleValue, CertificateWire.decode,
    conjugateProduct, List.map_map, Function.comp_def] using
    h (CertificateWire.factorList c.claim c.cycleFactors) 1

theorem all_even_subgroup {n : ℕ} {P : Subgroup (Perm (Fin n))} (hs : List P) :
    (subgroupTables hs).all (even n) =
      decide (∀ i : Fin hs.length, Perm.sign (hs.get i : Perm (Fin n)) = 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subgroupTables, List.all_map, List.all_eq_true, List.forall_mem_iff_get,
    Function.comp_apply, even_ofPerm, decide_eq_true_eq]

theorem any_odd_subgroup {n : ℕ} {P : Subgroup (Perm (Fin n))} (hs : List P) :
    (subgroupTables hs).any (fun h => !even n h) =
      decide (∃ i : Fin hs.length, Perm.sign (hs.get i : Perm (Fin n)) = -1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subgroupTables, List.any_map, List.any_eq_true, List.exists_mem_iff_get,
    Function.comp_apply, decide_eq_true_eq]
  apply exists_congr
  intro i
  rw [odd_ofPerm, decide_eq_true_eq]

theorem baseCheck_decode {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length) :
    baseCheck n (gs.map ofPerm) (subgroupTables (CertificateWire.decodedGenerators gs c))
      (List.ofFn c.mask) c.base.val (List.ofFn fun i => eraseWord (c.orbitWords i)) =
      CertifiedPermutation.baseCheck gs (CertificateWire.decode gs c) := by
  rw [baseCheck, primitive_ofPerm, fixedCount_eq,
    fixes_eq (CertificateWire.decodedGenerators gs c) c.mask, reaches_decode]
  apply Bool.eq_iff_iff.mpr
  simp only [CertifiedPermutation.baseCheck, Bool.and_eq_true, decide_eq_true_eq,
    member_ofFn, Bool.not_eq_true_eq_eq_false]
  change _ ↔
    FiniteAction.primitiveCheck gs c.base = true ∧
      (Finset.univ.filter fun x => c.mask x).Nonempty ∧
      (Finset.univ.filter fun x => c.mask x).card + 1 < Fintype.card (Fin n) ∧
      c.base ∉ (Finset.univ.filter fun x => c.mask x) ∧
      (∀ i : Fin (CertificateWire.decodedGenerators gs c).length,
        ∀ x ∈ (Finset.univ.filter fun x => c.mask x),
          (CertificateWire.decodedGenerators gs c |>.get i : Perm (Fin n)) x = x) ∧
      ∀ x ∉ (Finset.univ.filter fun x => c.mask x),
        (signedWordEval (CertificateWire.decode gs c).generators
          ((CertificateWire.decode gs c).orbitWords x) : Perm (Fin n)) c.base = x
  simp only [Finset.card_pos, Fintype.card_fin, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.not_eq_true, and_assoc]

theorem cycleValid_decode {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length) :
    cycleValid n (cycleTable n (gs.map ofPerm)
      (subgroupTables (CertificateWire.decodedGenerators gs c))
      ((CertificateWire.factorList c.claim c.cycleFactors).map eraseFactor)) =
      cycleValidCheck (CertificateWire.decode gs c) := by
  rw [cycleTable_decode, cycleValid, cycleCheck_ofPerm, supportCount_ofPerm]
  simp [cycleValidCheck, Bool.and_assoc]

theorem claimCheck_decode {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length) :
    claimCheck n (gs.map ofPerm) (subgroupTables (CertificateWire.decodedGenerators gs c))
      (claimCode c.claim)
      ((CertificateWire.factorList c.claim c.cycleFactors).map eraseFactor) =
      CertifiedPermutation.claimCheck (CertificateWire.decode gs c) := by
  unfold claimCheck
  rw [cycleValid_decode, all_even_subgroup, any_odd_subgroup]
  cases hc : c.claim <;>
    simp [claimCode, CertifiedPermutation.claimCheck, CertificateWire.decode, hc] <;>
    rfl

theorem check_eq {n : ℕ} (gs : List (Perm (Fin n)))
    (c : CertificateWire.RawCertificate n gs.length) :
    check n (gs.map ofPerm) (eraseCertificate c) =
      certificateCheck gs (CertificateWire.decode gs c) := by
  simp only [check, eraseCertificate, decodedTables_eq,
    baseCheck_decode, claimCheck_decode, certificateCheck]

end TauCeti.CertificateRuntime
