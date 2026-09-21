/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Hexacode.Basic
public import TauCeti.InformationTheory.Coding.Weight.Enumerator

import Mathlib.Tactic.FinCases

/-!
# Hexacode weights

Exact enumeration of the 64 messages gives the hexacode weight distribution:
one word of weight zero, 45 of weight four, and 18 of weight six. Consequently its
minimum distance is four and its homogeneous enumerator is `X⁶ + 45X²Y⁴ + 18Y⁶`.

The calculations use the alphabet labelling `0, 1, ω, ω²` in any field of four elements.
The reference is Huffman and Pless, *Fundamentals of Error-Correcting Codes*,
Example 1.3.4.
-/

public section

namespace TauCeti.Hexacode

open Matrix

section

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]
  (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

-- The rows and columns list the second and third message symbols, respectively;
-- the four matrices correspond to the first message symbol.
private def messageWeight : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![0, 4, 4, 4], ![4, 4, 4, 4], ![4, 4, 4, 4], ![4, 4, 4, 4]],
    ![![4, 4, 4, 4], ![4, 6, 4, 6], ![4, 4, 6, 6], ![4, 6, 6, 4]],
    ![![4, 4, 4, 4], ![4, 4, 6, 6], ![4, 6, 6, 4], ![4, 6, 4, 6]],
    ![![4, 4, 4, 4], ![4, 6, 6, 4], ![4, 6, 4, 6], ![4, 4, 6, 6]]]

include hF hω

private theorem hammingNorm_encoding_labels (a b c : Fin 4) :
    hammingNorm (encodingEquiv ω ![finFourEquiv hF hω a,
      finFourEquiv hF hω b, finFourEquiv hF hω c] : Fin 6 → F) = messageWeight a b c := by
  classical
  let := Fintype.ofFinite F
  let := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa only [Nat.card_eq_fintype_card, Nat.reducePow] using hF)
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have h0 : ω ≠ 0 := by rintro rfl; simp at hω
  have h1 : ω ≠ 1 := by intro h; grind
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [coe_encodingEquiv_apply, vecMul_generatorMatrix, finFourEquiv_apply,
      hammingNorm, Finset.card_filter, Fin.sum_univ_succ, messageWeight] <;> grind

private theorem weightDistribution_eq_card_messageWeight (w : ℕ) :
    (code ω : Set (Fin 6 → F)).weightDistribution w =
      Fintype.card {a : Fin 3 → Fin 4 // messageWeight (a 0) (a 1) (a 2) = w} := by
  classical
  let e : (Fin 3 → Fin 4) ≃ code ω :=
    (Equiv.piCongrRight fun _ ↦ finFourEquiv hF hω).trans (encodingEquiv ω).toEquiv
  have he (a : Fin 3 → Fin 4) :
      hammingNorm (e a : Fin 6 → F) = messageWeight (a 0) (a 1) (a 2) := by
    have ha : (Equiv.piCongrRight fun _ : Fin 3 ↦ finFourEquiv hF hω) a =
        ![finFourEquiv hF hω (a 0), finFourEquiv hF hω (a 1), finFourEquiv hF hω (a 2)] := by
      ext i
      fin_cases i <;> rfl
    simpa only [e, Equiv.trans_apply, ha,
      LinearEquiv.coe_toEquiv] using hammingNorm_encoding_labels hF hω (a 0) (a 1) (a 2)
  rw [Set.weightDistribution_def, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact (Equiv.subtypeSubtypeEquivSubtypeInter (fun x ↦ x ∈ code ω)
    (fun x ↦ hammingNorm x = w)).symm.trans
      (e.subtypeEquiv (fun a ↦ by rw [he])).symm

end

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (hF : Fintype.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

include hF hω

/-- The hexacode has one word of weight zero, 45 of weight four, and 18 of weight six. -/
@[simp]
theorem weightDistribution_code (w : ℕ) :
    (code ω : Set (Fin 6 → F)).weightDistribution w =
      if w = 0 then 1 else if w = 4 then 45 else if w = 6 then 18 else 0 := by
  rw [weightDistribution_eq_card_messageWeight (Nat.card_eq_fintype_card.trans hF) hω]
  have hcounts : ∀ w : Fin 7,
      Fintype.card {a : Fin 3 → Fin 4 // messageWeight (a 0) (a 1) (a 2) = w.val} =
        if w.val = 0 then 1 else if w.val = 4 then 45 else if w.val = 6 then 18 else 0 := by
    decide
  by_cases hw : w < 7
  · exact hcounts ⟨w, hw⟩
  · have hbound : ∀ a b c, messageWeight a b c ≤ 6 := by decide
    have hempty : IsEmpty {a : Fin 3 → Fin 4 // messageWeight (a 0) (a 1) (a 2) = w} :=
      ⟨fun a ↦ by have := hbound (a.val 0) (a.val 1) (a.val 2); omega⟩
    have hw0 : w ≠ 0 := by omega
    have hw4 : w ≠ 4 := by omega
    have hw6 : w ≠ 6 := by omega
    simp [hw0, hw4, hw6]

/-- Only weights zero, four and six occur in the hexacode. -/
theorem hammingNorm_eq_zero_or_eq_four_or_eq_six_of_mem_code
    {x : Fin 6 → F} (hx : x ∈ code ω) :
    hammingNorm x = 0 ∨ hammingNorm x = 4 ∨ hammingNorm x = 6 := by
  have h := (Set.weightDistribution_ne_zero_iff (Set.toFinite (code ω : Set (Fin 6 → F)))).mpr
    ⟨x, hx, rfl⟩
  rw [weightDistribution_code hF hω] at h
  split_ifs at h <;> simp_all

/-- The homogeneous weight enumerator of the hexacode. -/
@[simp]
theorem weightEnumerator_code :
    (code ω : Set (Fin 6 → F)).weightEnumerator =
      MvPolynomial.X 0 ^ 6 + 45 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
        18 * MvPolynomial.X 1 ^ 6 := by
  simp [Set.weightEnumerator_def, weightDistribution_code hF hω, Finset.sum_range_succ]

/-- The one-variable weight enumerator of the hexacode. -/
@[simp]
theorem weightPolynomial_code :
    (code ω : Set (Fin 6 → F)).weightPolynomial =
      1 + 45 * Polynomial.X ^ 4 + 18 * Polynomial.X ^ 6 := by
  rw [← Set.aeval_weightEnumerator, weightEnumerator_code hF hω]
  simp

/-- The hexacode has minimum Hamming distance four. -/
@[simp]
theorem hammingMinDist_code : (code ω : Set (Fin 6 → F)).hammingMinDist = 4 := by
  have hmin := Set.hammingMinDist_eq_sInf_weightDistribution
    (E := (code ω).toAddSubgroup) (Set.toFinite _)
  simp only [Submodule.coe_toAddSubgroup] at hmin
  rw [hmin]
  have hweights : {w : ℕ | 0 < w ∧
      (code ω : Set (Fin 6 → F)).weightDistribution w ≠ 0} = {4, 6} := by
    ext w
    simp only [weightDistribution_code hF hω, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    split_ifs <;> omega
  rw [hweights]
  simp

omit hF hω in
/-- The named hexacode has one word of weight zero, 45 of weight four, and 18 of weight six. -/
@[simp]
theorem weightDistribution_galoisFieldCode [DecidableEq (GaloisField 2 2)] (w : ℕ) :
    (galoisFieldCode : Set (Fin 6 → GaloisField 2 2)).weightDistribution w =
      if w = 0 then 1 else if w = 4 then 45 else if w = 6 then 18 else 0 := by
  let := Fintype.ofFinite (GaloisField 2 2)
  rw [galoisFieldCode_def]
  exact weightDistribution_code
    card_galoisField_two_two
    omega_sq_add_omega_add_one w

omit hF hω in
/-- The homogeneous weight enumerator of the named hexacode. -/
@[simp]
theorem weightEnumerator_galoisFieldCode [DecidableEq (GaloisField 2 2)] :
    (galoisFieldCode : Set (Fin 6 → GaloisField 2 2)).weightEnumerator =
      MvPolynomial.X 0 ^ 6 + 45 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
        18 * MvPolynomial.X 1 ^ 6 := by
  let := Fintype.ofFinite (GaloisField 2 2)
  rw [galoisFieldCode_def]
  exact weightEnumerator_code
    card_galoisField_two_two
    omega_sq_add_omega_add_one

omit hF hω in
/-- The one-variable weight enumerator of the named hexacode. -/
@[simp]
theorem weightPolynomial_galoisFieldCode [DecidableEq (GaloisField 2 2)] :
    (galoisFieldCode : Set (Fin 6 → GaloisField 2 2)).weightPolynomial =
      1 + 45 * Polynomial.X ^ 4 + 18 * Polynomial.X ^ 6 := by
  let := Fintype.ofFinite (GaloisField 2 2)
  rw [galoisFieldCode_def]
  exact weightPolynomial_code
    card_galoisField_two_two
    omega_sq_add_omega_add_one

omit hF hω in
/-- The named hexacode has minimum Hamming distance four. -/
@[simp]
theorem hammingMinDist_galoisFieldCode [DecidableEq (GaloisField 2 2)] :
    (galoisFieldCode : Set (Fin 6 → GaloisField 2 2)).hammingMinDist = 4 := by
  let := Fintype.ofFinite (GaloisField 2 2)
  rw [galoisFieldCode_def]
  exact hammingMinDist_code
    card_galoisField_two_two
    omega_sq_add_omega_add_one

end TauCeti.Hexacode
