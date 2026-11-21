/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.EndToEnd

/-!
# Polynomial sizes of the explicit encoded families

These bounds concern the actual binary encoders. They count generator tables,
unary list lengths, signed words, masks, and conjugate factors. They are size
bounds; running-time witnesses for finite TM2 implementations are separate.
-/

open Equiv
open TauCeti.BinaryCodec TauCeti.CertificateWire TauCeti.CertificateConstruction
open TauCeti.FinitePermutation TauCeti.SuccessfulFamilies TauCeti.EndToEnd

@[expose] public section

namespace TauCeti.EncodingBounds

theorem flatMap_length_le {α β : Type*} (values : List α) (f : α → List β)
    (bound : ℕ) (h : ∀ x ∈ values, (f x).length ≤ bound) :
    (values.flatMap f).length ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      have hx := h x List.mem_cons_self
      have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      omega

theorem writeList_length_le {α : Type} (encoder : α → List Bool) (values : List α)
    (bound : ℕ) (h : ∀ x ∈ values, (encoder x).length ≤ bound) :
    (writeList encoder values).length ≤ values.length * (bound + 1) + 1 := by
  have hf := flatMap_length_le values encoder bound h
  simp only [writeList, writeUnary, List.length_append, List.length_replicate,
    List.length_singleton, Nat.mul_add, Nat.mul_one]
  omega

theorem writeVector_length_le {α : Type} {count : ℕ} (encoder : α → List Bool)
    (values : Fin count → α) (bound : ℕ) (h : ∀ i, (encoder (values i)).length ≤ bound) :
    (writeVector encoder values).length ≤ count * bound := by
  induction count with
  | zero => simp [writeVector]
  | succ count ih =>
      change (encoder (values 0) ++ writeVector encoder (Fin.tail values)).length ≤ _
      rw [List.length_append]
      have htail := ih (Fin.tail values) (fun i => h i.succ)
      have hhead := h 0
      rw [Nat.succ_mul]
      omega

theorem writeVector_length {α : Type} {count : ℕ} (encoder : α → List Bool)
    (values : Fin count → α) (size : ℕ) (h : ∀ i, (encoder (values i)).length = size) :
    (writeVector encoder values).length = count * size := by
  induction count with
  | zero => simp [writeVector]
  | succ count ih =>
      change (encoder (values 0) ++ writeVector encoder (Fin.tail values)).length = _
      rw [List.length_append, h 0, ih (Fin.tail values) (fun i => h i.succ), Nat.succ_mul]
      omega

theorem writeWord_length {size : ℕ} (word : Word size) :
    (writeWord word).length = word.length * (indexWidth size + 2) + 1 := by
  have hf : (word.flatMap writeLetter).length = word.length * (indexWidth size + 1) := by
    induction word with
    | nil => simp
    | cons letter word ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, writeLetter,
          writeIndex, List.length_nil, writeBits_length, ih, Nat.succ_mul]
        omega
  simp only [writeWord, writeList, writeUnary, List.length_append,
    List.length_replicate, List.length_singleton, hf]
  ring

theorem indexWidth_le (bound : ℕ) : indexWidth bound ≤ bound + 1 := by
  apply max_le
  · omega
  · apply Nat.size_le.mpr
    exact lt_of_le_of_lt (by omega : bound - 1 ≤ bound)
      (lt_of_lt_of_le (Nat.lt_two_pow_self : bound < 2 ^ bound)
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : bound ≤ bound + 1)))

theorem indexWidth_le_of_le_cube {bound degree : ℕ} (h : bound ≤ degree ^ 3) :
    indexWidth bound ≤ 3 * (degree + 1) := by
  apply max_le
  · omega
  · apply Nat.size_le.mpr
    have hdegree : degree < 2 ^ (degree + 1) :=
      lt_of_lt_of_le (Nat.lt_two_pow_self : degree < 2 ^ degree)
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : degree ≤ degree + 1))
    have hp := pow_lt_pow_left₀ hdegree (Nat.zero_le degree) (by decide : (3 : ℕ) ≠ 0)
    rw [← pow_mul, Nat.mul_comm (degree + 1) 3] at hp
    exact lt_of_le_of_lt (by omega : bound - 1 ≤ degree ^ 3) hp

theorem swaps_length_le (degree : ℕ) (allowed : Fin degree → Bool) :
    (swaps degree allowed).length ≤ degree ^ 2 := by
  have h := flatMap_length_le (List.finRange degree)
    (fun a => ((List.finRange degree).filter
      (fun b => allowed a && allowed b && decide (a ≠ b))).map fun b => swap a b)
    degree (by
      intro a _
      simpa using List.length_filter_le
        (fun b => allowed a && allowed b && decide (a ≠ b)) (List.finRange degree))
  simpa [swaps, pow_two] using h

theorem triples_length_le (degree : ℕ) (allowed : Fin degree → Bool) :
    (triples degree allowed).length ≤ degree ^ 3 := by
  have h := flatMap_length_le (List.finRange degree)
    (fun a => (List.finRange degree).flatMap fun b =>
      ((List.finRange degree).filter (fun c => allowed a && allowed b && allowed c &&
        decide (a ≠ b) && decide (a ≠ c) && decide (b ≠ c))).map
        fun c => swap a b * swap b c) (degree ^ 2) (by
          intro a _
          have hb := flatMap_length_le (List.finRange degree)
            (fun b => ((List.finRange degree).filter (fun c => allowed a && allowed b &&
              allowed c && decide (a ≠ b) && decide (a ≠ c) && decide (b ≠ c))).map
              fun c => swap a b * swap b c) degree (by
                intro b _
                simpa using List.length_filter_le _ (List.finRange degree))
          simpa [pow_two] using hb)
  simpa [triples, pow_succ, Nat.mul_comm] using h

theorem writePermutation_length {degree : ℕ} (g : Perm (Fin degree)) :
    (writePermutation g).length = degree * indexWidth degree :=
  writeVector_length writeIndex g (indexWidth degree) (fun _ => writeBits_length _ _)

theorem writeGroup_length_le {degree : ℕ} (gs : List (Perm (Fin degree))) :
    (writeGroup ⟨degree, gs⟩).length ≤
      degree + 2 + gs.length * (degree * indexWidth degree + 1) := by
  have h := writeList_length_le writePermutation gs (degree * indexWidth degree)
    (fun g _ => (writePermutation_length g).le)
  simp only [writeGroup, writeUnary, List.length_append, List.length_replicate,
    List.length_singleton]
  omega

theorem writeClaim_length (claim : CertifiedPermutation.Claim) :
    (writeClaim claim).length = 2 := by
  cases claim <;> rfl

theorem complement_length_le {degree : ℕ} (mask : Fin degree → Bool) :
    (complement mask).length ≤ degree := by
  simpa [complement] using List.length_filter_le (fun x => !mask x) (List.finRange degree)

theorem wordsFor_word_length {degree : ℕ} (gs hs : List (Perm (Fin degree)))
    (hmem : ∀ h ∈ hs, h ∈ gs) (word : Word gs.length)
    (hword : word ∈ wordsFor gs hs hmem) : word.length = 1 := by
  simp only [wordsFor, List.mem_ofFn] at hword
  obtain ⟨i, rfl⟩ := hword
  rfl

theorem writeFactors_oneFactor_length_le {ambientSize subgroupSize : ℕ}
    (claim : CertifiedPermutation.Claim) (index : Fin subgroupSize) :
    (writeFactors claim (oneFactor (ambientSize := ambientSize) claim index)).length ≤
      indexWidth subgroupSize + 4 := by
  cases claim <;>
    simp [oneFactor, writeFactors, writeList, writeFactor, writeUnary,
      writeWord_length, writeIndex, writeBits_length] <;> omega

theorem make_length_le {degree : ℕ} (gs hs : List (Perm (Fin degree)))
    (hmem : ∀ h ∈ hs, h ∈ gs) (claim : CertifiedPermutation.Claim)
    (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (index : Fin hs.length)
    (hwords : ∀ i, (orbitWords i).length ≤ 1) :
    (writeCertificate (make gs hs hmem claim mask base orbitWords index)).length ≤
      hs.length * (indexWidth gs.length + 4) + degree * (indexWidth hs.length + 4) +
        indexWidth degree + indexWidth hs.length + 7 := by
  have hgenerators := writeList_length_le writeWord (wordsFor gs hs hmem)
    (indexWidth gs.length + 3) (by
      intro word hword
      rw [writeWord_length, wordsFor_word_length gs hs hmem word hword]
      omega)
  rw [wordsFor_length] at hgenerators
  have hmask := writeVector_length (fun bit : Bool => [bit]) mask 1 (fun _ => rfl)
  have horbits := writeVector_length_le writeWord
    (fun i => castWord (wordsFor_length gs hs hmem).symm (orbitWords i))
    (indexWidth hs.length + 3) (by
      intro i
      rw [writeWord_length]
      simp only [castWord, List.length_map, wordsFor_length]
      calc
        _ ≤ 1 * (indexWidth hs.length + 2) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ (hwords i)) _
        _ = _ := by ring)
  have horbits' := horbits.trans (Nat.mul_le_mul_right _ (complement_length_le mask))
  have hfactors := writeFactors_oneFactor_length_le (ambientSize := gs.length) claim
    (Fin.cast (wordsFor_length gs hs hmem).symm index)
  conv_rhs at hfactors => rw [wordsFor_length]
  simp only [writeCertificate, make, List.length_append, writeClaim_length]
  rw [hmask, Nat.mul_one]
  rw [show (writeIndex base).length = indexWidth degree from writeBits_length _ _]
  simp only [Nat.mul_succ] at hgenerators horbits' ⊢
  omega

theorem writeGroup_polynomial {degree : ℕ} (gs : List (Perm (Fin degree)))
    (hsize : gs.length ≤ degree ^ 3) :
    (writeGroup ⟨degree, gs⟩).length ≤ 4 * (degree + 1) ^ 5 := by
  have hwidth := indexWidth_le degree
  calc
    _ ≤ degree + 2 + gs.length * (degree * indexWidth degree + 1) :=
      writeGroup_length_le gs
    _ ≤ degree + 2 + (degree + 1) ^ 3 * (2 * (degree + 1) ^ 2) := by
      gcongr
      · exact hsize.trans (Nat.pow_le_pow_left (by omega) 3)
      · nlinarith
    _ ≤ 4 * (degree + 1) ^ 5 := by
      have h1 : degree + 1 ≤ (degree + 1) ^ 5 :=
        by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ degree + 1) (by decide : 1 ≤ 5)
      nlinarith

theorem make_polynomial {degree : ℕ} (gs hs : List (Perm (Fin degree)))
    (hmem : ∀ h ∈ hs, h ∈ gs) (claim : CertifiedPermutation.Claim)
    (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (index : Fin hs.length)
    (hgs : gs.length ≤ degree ^ 3) (hhs : hs.length ≤ degree ^ 3)
    (hwords : ∀ i, (orbitWords i).length ≤ 1) :
    (writeCertificate (make gs hs hmem claim mask base orbitWords index)).length ≤
      32 * (degree + 1) ^ 4 := by
  have hwidthgs := indexWidth_le_of_le_cube hgs
  have hwidthhs := indexWidth_le_of_le_cube hhs
  have hwidth := indexWidth_le degree
  calc
    _ ≤ hs.length * (indexWidth gs.length + 4) + degree * (indexWidth hs.length + 4) +
        indexWidth degree + indexWidth hs.length + 7 :=
      make_length_le gs hs hmem claim mask base orbitWords index hwords
    _ ≤ (degree + 1) ^ 3 * (7 * (degree + 1)) +
        (degree + 1) * (7 * (degree + 1)) + 4 * (degree + 1) + 7 := by
      gcongr <;> nlinarith [Nat.pow_le_pow_left (by omega : degree ≤ degree + 1) 3]
    _ ≤ 32 * (degree + 1) ^ 4 := by
      have h1 : degree + 1 ≤ (degree + 1) ^ 4 :=
        by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ degree + 1) (by decide : 1 ≤ 4)
      have h2 : (degree + 1) ^ 2 ≤ (degree + 1) ^ 4 :=
        Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4)
      have h0 : 1 ≤ (degree + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      nlinarith

theorem symmetricOrbit_length_le {degree : ℕ} (hdegree : 5 ≤ degree)
    (i : Fin (complement (@fixedMask degree)).length) :
    (symmetricOrbit hdegree i).length ≤ 1 := by
  dsimp only [symmetricOrbit]
  split <;> simp

theorem alternatingOrbit_length_le {degree : ℕ} (hdegree : 6 ≤ degree)
    (i : Fin (complement (@fixedMask degree)).length) :
    (alternatingOrbit hdegree i).length ≤ 1 := by
  dsimp only [alternatingOrbit]
  split <;> simp

theorem symmetricInput_polynomial {degree : ℕ} (hdegree : 5 ≤ degree) :
    (symmetricInput degree).length ≤ 4 * (degree + 1) ^ 5 := by
  apply writeGroup_polynomial
  exact (swaps_length_le degree _).trans
    (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))

theorem alternatingInput_polynomial (degree : ℕ) :
    (alternatingInput degree).length ≤ 4 * (degree + 1) ^ 5 :=
  writeGroup_polynomial _ (triples_length_le degree _)

theorem symmetricCertificate_polynomial {degree : ℕ} (hdegree : 5 ≤ degree) :
    (writeCertificate (symmetricCertificate hdegree)).length ≤ 32 * (degree + 1) ^ 4 := by
  apply make_polynomial
  · exact (swaps_length_le degree _).trans
      (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))
  · exact (swaps_length_le degree _).trans
      (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))
  · exact symmetricOrbit_length_le hdegree

theorem alternatingCertificate_polynomial {degree : ℕ} (hdegree : 6 ≤ degree) :
    (writeCertificate (alternatingCertificate hdegree)).length ≤ 32 * (degree + 1) ^ 4 := by
  apply make_polynomial
  · exact triples_length_le degree _
  · exact triples_length_le degree _
  · exact alternatingOrbit_length_le hdegree


end TauCeti.EncodingBounds
