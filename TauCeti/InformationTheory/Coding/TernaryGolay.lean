/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.GeneratorParityCheck
public import TauCeti.InformationTheory.Coding.WeightEnumerator
public import Mathlib.Algebra.Field.ZMod

/-!
# The extended ternary Golay code

The extended ternary Golay code is the row space of the systematic matrix `[I₆ | A]`
over `ZMod 3` displayed below. Its first six coordinates recover the message. We verify
self-duality independently through the generator/parity-check interface, and compute its
weight distribution by finite enumeration. These give parameters `[12,6,6]`, divisibility
of every weight by three, and the homogeneous enumerator
`X^12 + 264 X^6 Y^6 + 440 X^3 Y^9 + 24 Y^12`.

The matrix convention and code are those of Huffman and Pless,
*Fundamentals of Error-Correcting Codes* (2003), §1.9 and Chapter 9.
-/

public section

open Matrix

namespace TauCeti
namespace TernaryGolay

/-- The systematic generator of the extended ternary Golay code, with information
coordinates first. -/
def generator : Matrix (Fin 6) (Fin 12) (ZMod 3) :=
  !![1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 0, 1, 0, 1, 2, 2, 1;
     0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 2, 2;
     0, 0, 0, 1, 0, 0, 1, 2, 1, 0, 1, 2;
     0, 0, 0, 0, 1, 0, 1, 2, 2, 1, 0, 1;
     0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 0]

/-- The entries of the systematic generator. -/
theorem generator_def : generator =
    !![1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1;
       0, 1, 0, 0, 0, 0, 1, 0, 1, 2, 2, 1;
       0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 2, 2;
       0, 0, 0, 1, 0, 0, 1, 2, 1, 0, 1, 2;
       0, 0, 0, 0, 1, 0, 1, 2, 2, 1, 0, 1;
       0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 0] := (rfl)

/-- The extended ternary Golay code on twelve ordered coordinates. -/
noncomputable def code : Submodule (ZMod 3) (Fin 12 → ZMod 3) := generator.generatedBy

/-- The code is the row space of its displayed generator. -/
theorem code_def : code = generator.generatedBy := (rfl)

@[simp]
theorem mem_code {x : Fin 12 → ZMod 3} :
    x ∈ code ↔ ∃ a : Fin 6 → ZMod 3, a ᵥ* generator = x := by
  rw [code_def, Matrix.mem_generatedBy_iff]

/-- Encoding a message by the generator, written in coordinates. -/
theorem vecMul_generator (a : Fin 6 → ZMod 3) :
    a ᵥ* generator =
      ![a 0, a 1, a 2, a 3, a 4, a 5,
        a 1 + a 2 + a 3 + a 4 + a 5,
        a 0 + a 2 + 2 * a 3 + 2 * a 4 + a 5,
        a 0 + a 1 + a 3 + 2 * a 4 + 2 * a 5,
        a 0 + 2 * a 1 + a 2 + a 4 + 2 * a 5,
        a 0 + 2 * a 1 + 2 * a 2 + a 3 + a 5,
        a 0 + a 1 + 2 * a 2 + 2 * a 3 + a 4] := by
  ext i
  fin_cases i <;> simp [generator_def, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Reading the first six coordinates recovers the message. -/
@[simp]
theorem vecMul_generator_castAdd (a : Fin 6 → ZMod 3) (i : Fin 6) :
    (a ᵥ* generator) (i.castAdd 6) = a i := by
  rw [vecMul_generator]
  fin_cases i <;> rfl

/-- Encoding is injective because the generator is systematic. -/
theorem vecMul_generator_injective : Function.Injective (fun a ↦ a ᵥ* generator) := by
  intro a b h
  ext i
  simpa only [vecMul_generator_castAdd] using congrFun h (i.castAdd 6)

/-- The generator has rank six. -/
@[simp]
theorem rank_generator : generator.rank = 6 := by
  rw [← Matrix.finrank_generatedBy, Matrix.generatedBy_def]
  exact (LinearMap.finrank_range_of_inj vecMul_generator_injective).trans
    (Module.finrank_fintype_fun_eq_card (R := ZMod 3))

/-- The code has dimension six. -/
@[simp]
theorem finrank_code : Module.finrank (ZMod 3) code = 6 := by
  rw [code_def, Matrix.finrank_generatedBy, rank_generator]

/-- Encoding is a linear equivalence between messages and codewords. -/
noncomputable def encodeEquiv : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] code :=
  LinearEquiv.ofBijective
    (generator.vecMulLinear.codRestrict code (fun a ↦ mem_code.mpr ⟨a, rfl⟩))
    ⟨fun _ _ h ↦ vecMul_generator_injective (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨a, ha⟩ := mem_code.mp x.property
      exact ⟨a, Subtype.ext ha⟩⟩

@[simp]
theorem coe_encodeEquiv_apply (a : Fin 6 → ZMod 3) : (encodeEquiv a : Fin 12 → ZMod 3) =
    a ᵥ* generator := (rfl)

@[simp]
theorem encodeEquiv_symm_apply (x : code) (i : Fin 6) :
    encodeEquiv.symm x i = x.1 (i.castAdd 6) := by
  have h := congrArg (fun y : code ↦ y.1 (i.castAdd 6)) (encodeEquiv.apply_symm_apply x)
  simpa only [coe_encodeEquiv_apply, vecMul_generator_castAdd] using h

/-- The code has 729 words. -/
@[simp↓]
theorem card_code : Nat.card code = 729 := by
  rw [← Nat.card_congr encodeEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The generator rows are mutually orthogonal. -/
@[simp]
theorem generator_mul_transpose : generator * generatorᵀ = 0 := by decide

/-- The generator is also a parity-check matrix of the same code. -/
@[simp↓]
theorem checkedBy_generator : generator.checkedBy = code := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [code_def, Matrix.generatedBy_le_checkedBy_iff]
    exact generator_mul_transpose
  · rw [Matrix.finrank_checkedBy, rank_generator, finrank_code]
    decide

/-- The extended ternary Golay code is Euclidean self-dual. -/
@[simp]
theorem euclideanDual_code : code.euclideanDual = code := by
  rw [code_def, ← Matrix.checkedBy_eq_euclideanDual_generatedBy]
  exact checkedBy_generator

/-- Every word has weight zero, six, nine, or twelve. -/
theorem hammingNorm_mem {x : Fin 12 → ZMod 3} (hx : x ∈ code) :
    hammingNorm x ∈ ({0, 6, 9, 12} : Finset ℕ) := by
  obtain ⟨a, rfl⟩ := mem_code.mp hx
  exact (by decide +kernel : ∀ a : Fin 6 → ZMod 3,
    hammingNorm (a ᵥ* generator) ∈ ({0, 6, 9, 12} : Finset ℕ)) a

private theorem message_count_six :
    Fintype.card {a : Fin 6 → ZMod 3 // hammingNorm (a ᵥ* generator) = 6} = 264 := by
  decide +kernel

private theorem message_count_nine :
    Fintype.card {a : Fin 6 → ZMod 3 // hammingNorm (a ᵥ* generator) = 9} = 440 := by
  decide +kernel

private theorem message_count_twelve :
    Fintype.card {a : Fin 6 → ZMod 3 // hammingNorm (a ᵥ* generator) = 12} = 24 := by
  decide +kernel

/-- The full weight distribution of the extended ternary Golay code. -/
@[simp]
theorem weightDistribution_code (w : ℕ) :
    (code : Set (Fin 12 → ZMod 3)).weightDistribution w =
      if w = 0 then 1 else if w = 6 then 264 else if w = 9 then 440
      else if w = 12 then 24 else 0 := by
  classical
  by_cases h0 : w = 0
  · subst w
    simp [Set.weightDistribution_zero code.zero_mem]
  have hc : (code : Set (Fin 12 → ZMod 3)).weightDistribution w =
      Fintype.card {a : Fin 6 → ZMod 3 // hammingNorm (a ᵥ* generator) = w} := by
    rw [Set.weightDistribution_def, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun x ↦ x ∈ code)
        (fun x ↦ hammingNorm x = w)).symm.trans
        (encodeEquiv.toEquiv.subtypeEquiv (fun x ↦ by simp)).symm)
  rw [hc]
  by_cases h6 : w = 6
  · subst w
    simpa using message_count_six
  by_cases h9 : w = 9
  · subst w
    simpa using message_count_nine
  by_cases h12 : w = 12
  · subst w
    simpa using message_count_twelve
  simp only [h0, h6, h9, h12, ↓reduceIte]
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun ⟨a, ha⟩ ↦ ?_⟩
  have h := hammingNorm_mem (mem_code.mpr ⟨a, rfl⟩)
  simp only [ha, Finset.mem_insert, Finset.mem_singleton] at h
  tauto

/-- Every weight of the extended ternary Golay code is divisible by three. -/
theorem three_dvd_hammingNorm {x : Fin 12 → ZMod 3} (hx : x ∈ code) :
    3 ∣ hammingNorm x := by
  have h := hammingNorm_mem hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h <;> simp [h]

/-- The minimum distance of the extended ternary Golay code is six. -/
@[simp]
theorem hammingMinDist_code : (code : Set (Fin 12 → ZMod 3)).hammingMinDist = 6 := by
  have h6 : ∃ x ∈ code, hammingNorm x = 6 := by
    apply (Set.weightDistribution_ne_zero_iff (Set.toFinite (code : Set (Fin 12 → ZMod 3)))).1
    simp
  obtain ⟨x, hx, hw⟩ := h6
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hw
  have hbot : code.toAddSubgroup ≠ ⊥ := by
    intro h
    have : x ∈ (⊥ : AddSubgroup (Fin 12 → ZMod 3)) := h ▸ hx
    exact hx0 this
  apply le_antisymm
  · exact hw ▸ Set.hammingMinDist_le_hammingNorm (E := code.toAddSubgroup) hx hx0
  · apply (Set.le_hammingMinDist_iff_hammingNorm hbot).2
    intro y hy hy0
    have h := hammingNorm_mem hy
    have : hammingNorm y ≠ 0 := by simpa using hy0
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    omega

/-- The homogeneous weight enumerator, computed by enumerating all messages. -/
@[simp]
theorem weightEnumerator_code :
    (code : Set (Fin 12 → ZMod 3)).weightEnumerator =
      MvPolynomial.X 0 ^ 12 + 264 * MvPolynomial.X 0 ^ 6 * MvPolynomial.X 1 ^ 6 +
        440 * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 9 + 24 * MvPolynomial.X 1 ^ 12 := by
  rw [Set.weightEnumerator_def]
  simp [Finset.sum_range_succ]

end TernaryGolay
end TauCeti
