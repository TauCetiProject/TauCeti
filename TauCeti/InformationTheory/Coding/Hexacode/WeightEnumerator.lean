/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Hexacode.Basic
public import TauCeti.InformationTheory.Coding.WeightEnumerator

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

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (hF : Fintype.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

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
  let : CharP F 2 := ringChar.of_eq
    ((FiniteField.even_card_iff_char_two (F := F)).mpr (by omega))
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

/-- The hexacode has one word of weight zero, 45 of weight four, and 18 of weight six. -/
@[simp]
theorem weightDistribution_code (w : ℕ) :
    (code ω : Set (Fin 6 → F)).weightDistribution w =
      if w = 0 then 1 else if w = 4 then 45 else if w = 6 then 18 else 0 := by
  rw [weightDistribution_eq_card_messageWeight hF hω]
  have hcounts : ∀ w : Fin 7,
      Fintype.card {a : Fin 3 → Fin 4 // messageWeight (a 0) (a 1) (a 2) = w.val} =
        if w.val = 0 then 1 else if w.val = 4 then 45 else if w.val = 6 then 18 else 0 := by
    decide
  by_cases hw : w < 7
  · exact hcounts ⟨w, hw⟩
  · have hbound : ∀ a b c, messageWeight a b c ≤ 6 := by decide
    have hempty : IsEmpty {a : Fin 3 → Fin 4 // messageWeight (a 0) (a 1) (a 2) = w} :=
      ⟨fun a ↦ by have := hbound (a.val 0) (a.val 1) (a.val 2); omega⟩
    simp [show w ≠ 0 by omega, show w ≠ 4 by omega,
      show w ≠ 6 by omega]

/-- Only weights zero, four and six occur in the hexacode. -/
theorem hammingNorm_mem_zero_four_six {x : Fin 6 → F} (hx : x ∈ code ω) :
    hammingNorm x = 0 ∨ hammingNorm x = 4 ∨ hammingNorm x = 6 := by
  have h := (Set.weightDistribution_ne_zero_iff (Set.toFinite (code ω : Set (Fin 6 → F)))).mpr
    ⟨x, hx, rfl⟩
  rw [weightDistribution_code hF hω] at h
  split_ifs at h <;> simp_all

/-- The homogeneous hexacode enumerator, obtained by counting all messages. -/
theorem weightEnumerator_code :
    (code ω : Set (Fin 6 → F)).weightEnumerator =
      MvPolynomial.X 0 ^ 6 + 45 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
        18 * MvPolynomial.X 1 ^ 6 := by
  simp [Set.weightEnumerator_def, weightDistribution_code hF hω, Finset.sum_range_succ]

/-- The hexacode has minimum Hamming distance four. -/
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

end TauCeti.Hexacode
