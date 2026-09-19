/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Generators
public import TauCeti.InformationTheory.Coding.WeightEnumerator

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The extended binary Golay code

The extended binary Golay code is the row space of the systematic matrix `[I₁₂ | B]`,
where `B` is the bordered reverse-circulant matrix over `ZMod 2`. The first twelve
coordinates recover the message. The generator is also a parity-check matrix.

This doubly-even self-dual binary code has parameters `[24, 12, 8]`. Its self-duality and
divisibility of weights by four make it an input to Construction A, which associates an even
unimodular lattice to such a code. The weight distribution and homogeneous weight enumerator
describe the numbers of codewords of each weight.

The matrix convention is that of Huffman and Pless, *Fundamentals of Error-Correcting
Codes*, §1.9.1 and Chapter 9.
-/

public section

namespace TauCeti.BinaryGolay

open Matrix

/-- The bordered reverse-circulant block in the binary Golay generator. Its interior is
indexed by sums modulo eleven in `{0, 1, 3, 4, 5, 9}`. -/
def block : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0;
     1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1;
     1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1;
     1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0;
     1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1;
     1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1;
     1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1;
     1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0;
     1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0;
     1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0;
     1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1]

/-- The entries of the border and of the reverse-circulant interior. -/
@[simp]
theorem block_apply (i j : Fin 12) :
    block i j = if i = 0 then (if j = 0 then 0 else 1) else if j = 0 then 1 else
      if (i.val + j.val - 2) % 11 ∈ ({0, 1, 3, 4, 5, 9} : Finset ℕ) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- The systematic generator `[I₁₂ | B]`, in the conventional coordinate order. -/
def generator : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  fun i ↦ Fin.append ((1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) i) (block i)

/-- The extended binary Golay code, with twenty-four ordered coordinates. -/
noncomputable def code : LinearCode (ZMod 2) (Fin 24) := generator.generatedBy

/-- The code is the row space of its displayed generator. -/
theorem code_def : code = generator.generatedBy := (rfl)

/-- The generator has the systematic block form `[I₁₂ | B]`. -/
theorem generator_def : generator = fun i ↦
    Fin.append ((1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) i) (block i) := (rfl)

/-- The information columns of the generator form the identity matrix. -/
@[simp]
theorem generator_castAdd (i j : Fin 12) :
    generator i (j.castAdd 12) = if i = j then 1 else 0 := by
  simp [generator, Matrix.one_apply]

/-- The last twelve columns of the generator form `block`. -/
@[simp]
theorem generator_addNat (i j : Fin 12) : generator i (j.addNat 12) = block i j := by
  simpa only [generator, Fin.natAdd_eq_addNat] using
    (Fin.append_right ((1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) i) (block i) j)

/-- Encoding a message keeps it in the first twelve coordinates and appends its product with
`block`. -/
@[simp]
theorem vecMul_generator (a : Fin 12 → ZMod 2) :
    a ᵥ* generator = Fin.append a (a ᵥ* block) := by
  ext j
  refine Fin.addCases (m := 12) (n := 12) (fun i ↦ ?_) (fun i ↦ ?_) j
  · simp [Matrix.vecMul, dotProduct]
  · rw [Fin.append_right]
    simp only [Matrix.vecMul, dotProduct, Fin.natAdd_eq_addNat, generator_addNat]

/-- Membership in the extended Golay code is systematic encoding of a message. -/
@[simp]
theorem mem_code_iff {x : Fin 24 → ZMod 2} :
    x ∈ code ↔ ∃ a : Fin 12 → ZMod 2, Fin.append a (a ᵥ* block) = x := by
  simp only [code_def, Matrix.mem_generatedBy_iff, vecMul_generator]

/-- The generator has zero Euclidean Gram matrix. -/
@[simp]
theorem generator_mul_transpose : generator * generator.transpose = 0 := by
  decide +kernel

/-- Systematic encoding gives a linear equivalence between messages and codewords. -/
noncomputable def encodingEquiv : (Fin 12 → ZMod 2) ≃ₗ[ZMod 2] code :=
  (LinearEquiv.ofInjective generator.vecMulLinear (by
    intro a b hab
    have h := congrArg (fun x : Fin 24 → ZMod 2 ↦ fun i : Fin 12 ↦ x (i.castAdd 12)) hab
    simpa only [Matrix.vecMulLinear_apply, vecMul_generator, Fin.append_left] using h)).trans
    (LinearEquiv.ofEq _ _ (by rw [code_def, Matrix.generatedBy_def]))

/-- The encoding equivalence sends a message to its systematic encoding. -/
@[simp]
theorem encodingEquiv_apply (a : Fin 12 → ZMod 2) :
    (encodingEquiv a : Fin 24 → ZMod 2) = Fin.append a (a ᵥ* block) := by
  simp only [encodingEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact (LinearEquiv.ofInjective_apply (f := generator.vecMulLinear) a).trans
    (vecMul_generator a)

/-- Decoding reads the first twelve coordinates. -/
@[simp]
theorem encodingEquiv_symm_apply (x : code) (i : Fin 12) :
    encodingEquiv.symm x i = x.val (i.castAdd 12) := by
  obtain ⟨a, rfl⟩ := encodingEquiv.surjective x
  simp

/-- The extended binary Golay code has dimension twelve. -/
@[simp]
theorem finrank_code : Module.finrank (ZMod 2) code = 12 := by
  rw [← encodingEquiv.finrank_eq]
  simp

/-- Its displayed generator has rank twelve. -/
@[simp]
theorem rank_generator : generator.rank = 12 := by
  rw [← Matrix.finrank_generatedBy, ← code_def, finrank_code]

/-- The extended binary Golay code has 4096 words. -/
@[simp↓]
theorem natCard_code : Nat.card code = 4096 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_code]
  norm_num [Nat.card_eq_fintype_card]

/-- The extended binary Golay code is Euclidean self-dual. -/
@[simp]
theorem euclideanDual_code : code.euclideanDual = code := by
  symm
  apply Submodule.eq_euclideanDual_of_le_of_card_le_two_mul_finrank
  · rw [code_def, ← Matrix.checkedBy_eq_euclideanDual_generatedBy,
      Matrix.generatedBy_le_checkedBy_iff]
    exact generator_mul_transpose
  · simp

/-- The same matrix is a parity-check matrix for the extended Golay code. -/
@[simp↓]
theorem checkedBy_generator : generator.checkedBy = code := by
  rw [Matrix.checkedBy_eq_euclideanDual_generatedBy, ← code_def, euclideanDual_code]

private def messageEquiv : Fin 16 × Fin 256 ≃ (Fin 12 → ZMod 2) :=
  (Equiv.prodCongr finFunctionFinEquiv.symm finFunctionFinEquiv.symm).trans
    ((Fin.appendEquiv 4 8).trans (Equiv.piCongrRight fun _ ↦ (ZMod.finEquiv 2).toEquiv))

private def weightTable (i : Fin 16) (j : Fin 256) : ℕ :=
  (((#[
    #[
      #[0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 12, 8, 12],
      #[8, 8, 8, 8, 8, 8, 8, 8, 8, 12, 12, 8, 8, 8, 12, 12],
      #[8, 8, 8, 12, 8, 8, 8, 12, 8, 12, 8, 8, 8, 8, 8, 12],
      #[8, 8, 12, 8, 12, 12, 8, 12, 8, 8, 8, 12, 12, 8, 12, 12],
      #[8, 8, 8, 8, 8, 12, 12, 8, 8, 8, 8, 8, 8, 8, 12, 12],
      #[8, 8, 12, 12, 8, 12, 8, 12, 8, 12, 8, 12, 8, 12, 12, 8],
      #[8, 8, 8, 12, 12, 8, 8, 8, 12, 8, 12, 12, 8, 12, 12, 12],
      #[8, 8, 8, 12, 8, 12, 12, 12, 12, 12, 8, 12, 12, 12, 12, 16],
      #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 12, 12, 12, 8, 8, 12],
      #[8, 8, 8, 8, 8, 8, 8, 16, 8, 12, 8, 12, 12, 12, 12, 12],
      #[8, 12, 8, 8, 12, 8, 12, 12, 8, 8, 12, 8, 8, 12, 12, 12],
      #[8, 12, 12, 12, 8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 8, 12],
      #[8, 12, 8, 12, 8, 8, 12, 12, 12, 8, 8, 12, 8, 12, 8, 12],
      #[12, 8, 8, 12, 12, 12, 12, 12, 8, 8, 12, 12, 12, 12, 12, 12],
      #[8, 8, 8, 12, 8, 12, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12],
      #[12, 12, 12, 8, 8, 12, 12, 12, 12, 12, 12, 16, 12, 12, 16, 12]],
    #[
      #[12, 8, 8, 8, 8, 8, 8, 12, 8, 8, 8, 12, 8, 8, 12, 8],
      #[8, 8, 8, 12, 8, 12, 12, 12, 8, 8, 8, 12, 12, 12, 8, 12],
      #[8, 8, 8, 8, 8, 12, 12, 8, 8, 8, 12, 12, 12, 12, 12, 12],
      #[8, 12, 8, 12, 8, 8, 12, 12, 12, 12, 12, 12, 8, 16, 12, 12],
      #[8, 8, 8, 12, 8, 8, 8, 12, 8, 12, 12, 12, 12, 12, 8, 12],
      #[8, 12, 8, 8, 12, 8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 16],
      #[8, 12, 12, 8, 8, 12, 12, 16, 8, 12, 8, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 16, 12, 12, 12, 12, 12],
      #[8, 8, 8, 12, 8, 12, 12, 12, 8, 12, 8, 8, 8, 12, 12, 12],
      #[8, 12, 12, 12, 12, 12, 12, 8, 12, 8, 12, 12, 8, 12, 12, 12],
      #[8, 8, 12, 12, 8, 12, 8, 12, 12, 12, 8, 16, 12, 12, 12, 12],
      #[12, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16],
      #[8, 8, 12, 8, 12, 12, 8, 12, 8, 12, 12, 12, 12, 12, 16, 12],
      #[8, 12, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 12, 12, 12, 16],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 16],
      #[8, 12, 12, 16, 16, 12, 12, 16, 12, 12, 12, 12, 12, 16, 12, 16]],
    #[
      #[8, 8, 8, 12, 8, 12, 8, 8, 8, 8, 8, 12, 8, 8, 8, 12],
      #[8, 8, 8, 12, 12, 8, 12, 12, 12, 8, 8, 8, 8, 12, 12, 12],
      #[8, 8, 8, 8, 8, 12, 8, 12, 8, 12, 8, 12, 8, 12, 16, 12],
      #[8, 8, 12, 12, 8, 12, 12, 8, 12, 12, 12, 12, 12, 12, 12, 12],
      #[8, 8, 12, 8, 8, 8, 8, 12, 12, 12, 8, 12, 12, 8, 12, 12],
      #[8, 8, 8, 12, 12, 12, 8, 12, 8, 12, 12, 12, 12, 12, 12, 16],
      #[8, 8, 12, 12, 12, 12, 12, 12, 8, 12, 12, 8, 12, 12, 12, 12],
      #[8, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 12, 16],
      #[8, 8, 12, 8, 8, 12, 12, 12, 8, 8, 8, 12, 12, 12, 12, 8],
      #[12, 12, 8, 12, 8, 12, 12, 12, 8, 12, 12, 12, 8, 12, 12, 12],
      #[12, 8, 8, 12, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[8, 12, 8, 12, 12, 12, 12, 12, 12, 8, 12, 16, 12, 16, 12, 16],
      #[8, 12, 8, 8, 8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 12, 16],
      #[8, 12, 12, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 16, 12, 12],
      #[12, 12, 12, 12, 12, 12, 8, 16, 8, 12, 12, 16, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 12, 16, 16, 12, 12, 12, 12, 16, 12, 12, 16]],
    #[
      #[8, 8, 8, 8, 8, 8, 12, 12, 8, 12, 12, 8, 12, 12, 12, 12],
      #[8, 12, 12, 8, 8, 12, 8, 12, 8, 12, 12, 16, 12, 12, 12, 12],
      #[8, 12, 12, 12, 12, 8, 12, 12, 12, 8, 12, 12, 12, 12, 8, 12],
      #[12, 12, 8, 12, 12, 12, 12, 16, 8, 12, 12, 12, 12, 12, 12, 16],
      #[8, 12, 8, 12, 12, 12, 12, 12, 8, 8, 12, 12, 8, 16, 12, 12],
      #[12, 12, 12, 12, 8, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[12, 12, 8, 12, 8, 12, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16],
      #[12, 8, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16, 16, 16, 16, 12],
      #[8, 12, 8, 12, 12, 8, 8, 12, 12, 12, 12, 12, 8, 12, 12, 16],
      #[8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 12, 12, 16],
      #[8, 12, 12, 12, 12, 16, 12, 12, 8, 12, 12, 12, 12, 12, 12, 16],
      #[12, 12, 16, 12, 12, 12, 12, 16, 12, 16, 12, 12, 12, 12, 16, 12],
      #[12, 8, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 16, 12, 16, 12, 12, 8, 16, 12, 12, 16, 16],
      #[8, 12, 12, 12, 12, 12, 16, 12, 16, 12, 12, 12, 12, 16, 16, 16],
      #[12, 12, 12, 16, 12, 16, 12, 12, 12, 16, 16, 16, 12, 16, 16, 16]],
    #[
      #[8, 8, 8, 12, 8, 8, 12, 8, 8, 8, 12, 8, 8, 12, 8, 8],
      #[8, 12, 8, 8, 8, 12, 12, 12, 8, 8, 8, 12, 8, 12, 12, 12],
      #[8, 8, 8, 8, 8, 8, 12, 12, 12, 8, 8, 12, 12, 12, 12, 12],
      #[12, 8, 8, 12, 8, 12, 8, 12, 8, 12, 12, 16, 12, 12, 12, 12],
      #[8, 12, 8, 8, 8, 8, 8, 12, 8, 12, 12, 12, 8, 12, 12, 12],
      #[8, 8, 12, 8, 8, 12, 12, 12, 8, 12, 12, 12, 16, 12, 12, 12],
      #[8, 12, 8, 12, 12, 12, 12, 12, 8, 8, 12, 12, 12, 12, 8, 16],
      #[12, 12, 12, 12, 12, 8, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12],
      #[8, 8, 8, 12, 12, 12, 8, 12, 8, 8, 8, 12, 8, 12, 12, 12],
      #[12, 8, 12, 12, 8, 12, 12, 12, 12, 12, 8, 12, 12, 8, 12, 12],
      #[8, 12, 8, 12, 8, 12, 12, 8, 12, 12, 12, 12, 8, 12, 12, 16],
      #[8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 12],
      #[8, 8, 8, 12, 12, 8, 12, 12, 12, 12, 12, 8, 12, 12, 12, 16],
      #[8, 12, 12, 12, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 12, 16],
      #[8, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 16, 12, 16, 8, 16, 12, 12, 12, 12, 16, 16]],
    #[
      #[8, 8, 8, 8, 8, 12, 8, 12, 8, 12, 8, 12, 12, 8, 12, 16],
      #[8, 8, 12, 12, 12, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[8, 12, 12, 12, 12, 12, 8, 12, 8, 12, 12, 12, 8, 12, 12, 12],
      #[8, 12, 12, 12, 12, 12, 16, 12, 12, 12, 12, 8, 12, 12, 12, 16],
      #[8, 8, 12, 12, 12, 12, 12, 12, 12, 8, 8, 12, 12, 12, 12, 12],
      #[12, 12, 8, 16, 12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 12, 16],
      #[12, 8, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 12, 12, 16, 12],
      #[8, 12, 12, 12, 12, 16, 12, 12, 12, 12, 12, 16, 12, 16, 16, 16],
      #[8, 12, 12, 8, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[8, 12, 8, 12, 12, 12, 12, 12, 8, 12, 16, 12, 12, 16, 12, 16],
      #[12, 8, 12, 12, 12, 12, 12, 16, 8, 12, 12, 12, 16, 12, 12, 12],
      #[12, 16, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16, 12, 12, 12, 16],
      #[12, 12, 12, 12, 8, 16, 12, 12, 8, 12, 12, 16, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 12, 16, 16, 12, 12, 12, 12, 12, 16, 16, 12],
      #[12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 12, 16, 12, 16, 16, 16],
      #[12, 12, 12, 16, 12, 12, 16, 12, 16, 12, 16, 16, 16, 16, 12, 16]],
    #[
      #[8, 8, 8, 8, 12, 8, 8, 12, 8, 8, 12, 12, 12, 12, 12, 12],
      #[8, 12, 8, 12, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 8, 16],
      #[12, 12, 12, 8, 8, 12, 12, 12, 8, 12, 12, 12, 12, 8, 12, 12],
      #[8, 12, 12, 12, 12, 12, 12, 16, 8, 12, 12, 12, 12, 16, 12, 12],
      #[12, 8, 8, 12, 8, 12, 12, 16, 8, 12, 8, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 16, 12, 12, 12, 12],
      #[8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 12, 16, 12, 16, 12, 12],
      #[12, 12, 8, 12, 12, 12, 16, 12, 12, 12, 16, 12, 12, 16, 16, 16],
      #[8, 8, 12, 12, 8, 12, 8, 12, 8, 16, 12, 12, 12, 12, 12, 12],
      #[8, 12, 12, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16],
      #[8, 12, 12, 12, 12, 12, 12, 16, 12, 12, 8, 12, 12, 12, 12, 16],
      #[12, 12, 12, 16, 16, 12, 12, 12, 12, 12, 16, 12, 12, 12, 12, 16],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 16, 12],
      #[8, 12, 12, 16, 12, 16, 16, 12, 12, 12, 12, 12, 12, 16, 12, 16],
      #[12, 8, 12, 12, 12, 16, 12, 12, 12, 12, 12, 16, 16, 12, 16, 16],
      #[12, 12, 12, 16, 12, 12, 12, 16, 16, 16, 12, 16, 12, 16, 16, 16]],
    #[
      #[8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 8, 12, 8, 12, 12, 12],
      #[12, 8, 12, 12, 12, 16, 12, 12, 8, 12, 12, 12, 12, 12, 16, 12],
      #[8, 8, 8, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 12, 16],
      #[12, 12, 12, 12, 12, 12, 12, 12, 16, 12, 12, 16, 12, 12, 16, 16],
      #[8, 12, 12, 12, 12, 12, 12, 8, 12, 12, 16, 12, 12, 12, 12, 16],
      #[8, 12, 12, 12, 12, 12, 12, 16, 12, 16, 12, 12, 12, 16, 16, 16],
      #[12, 12, 12, 12, 16, 12, 12, 16, 12, 12, 12, 12, 12, 12, 16, 16],
      #[12, 12, 16, 16, 12, 16, 12, 16, 12, 16, 12, 16, 16, 12, 12, 16],
      #[12, 12, 8, 12, 12, 12, 16, 12, 12, 8, 12, 12, 12, 12, 12, 16],
      #[12, 12, 12, 16, 12, 12, 12, 16, 12, 12, 12, 16, 12, 16, 12, 12],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 12, 16, 16, 12],
      #[12, 12, 12, 12, 8, 16, 16, 16, 12, 16, 12, 16, 16, 16, 16, 16],
      #[8, 12, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16, 16, 16, 12, 16],
      #[16, 12, 12, 12, 12, 12, 12, 16, 12, 16, 16, 16, 16, 12, 16, 16],
      #[12, 16, 12, 16, 12, 12, 16, 16, 12, 16, 16, 12, 12, 16, 12, 16],
      #[12, 16, 16, 12, 16, 16, 16, 16, 12, 12, 16, 16, 16, 16, 16, 16]],
    #[
      #[8, 8, 8, 8, 8, 8, 12, 12, 8, 8, 8, 8, 12, 8, 8, 12],
      #[8, 12, 8, 12, 12, 8, 8, 12, 8, 8, 12, 12, 8, 12, 8, 12],
      #[8, 8, 12, 8, 8, 8, 8, 12, 8, 12, 12, 12, 12, 12, 12, 8],
      #[8, 12, 8, 8, 8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 12, 16],
      #[8, 8, 8, 8, 8, 12, 8, 12, 8, 8, 8, 16, 12, 12, 12, 12],
      #[12, 8, 8, 12, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[12, 12, 8, 12, 8, 12, 12, 12, 8, 12, 12, 12, 8, 12, 12, 12],
      #[8, 12, 12, 12, 12, 12, 16, 12, 12, 8, 12, 12, 12, 16, 12, 12],
      #[8, 12, 12, 8, 8, 12, 8, 12, 8, 12, 8, 12, 8, 8, 12, 12],
      #[8, 8, 12, 12, 12, 12, 12, 12, 8, 12, 12, 8, 12, 12, 12, 12],
      #[8, 8, 8, 12, 12, 12, 8, 12, 8, 12, 12, 12, 12, 12, 12, 16],
      #[8, 12, 12, 12, 12, 8, 12, 12, 16, 12, 12, 12, 12, 12, 12, 16],
      #[8, 8, 12, 12, 8, 12, 12, 8, 12, 12, 12, 12, 12, 12, 12, 12],
      #[8, 12, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 16, 16, 16],
      #[12, 8, 12, 12, 12, 12, 12, 16, 12, 12, 8, 12, 12, 12, 16, 12],
      #[12, 12, 12, 16, 12, 16, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16]],
    #[
      #[8, 8, 8, 12, 8, 12, 8, 8, 8, 12, 12, 12, 8, 12, 12, 12],
      #[8, 8, 12, 8, 8, 12, 12, 12, 12, 12, 8, 12, 12, 12, 16, 12],
      #[8, 12, 8, 12, 12, 12, 12, 12, 12, 8, 8, 12, 8, 12, 12, 16],
      #[12, 8, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[8, 12, 12, 12, 12, 8, 12, 12, 12, 12, 12, 8, 8, 12, 12, 12],
      #[8, 12, 12, 12, 12, 16, 12, 12, 8, 12, 12, 12, 12, 12, 12, 16],
      #[8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 12, 12, 16],
      #[12, 12, 12, 12, 12, 12, 8, 16, 12, 16, 12, 16, 12, 12, 16, 16],
      #[8, 8, 8, 12, 12, 8, 12, 12, 12, 8, 12, 12, 12, 16, 12, 12],
      #[12, 12, 8, 12, 8, 12, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16],
      #[12, 12, 12, 12, 8, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 16, 12, 16, 8, 12, 12, 16, 12, 16, 16, 12],
      #[12, 12, 8, 12, 12, 12, 12, 16, 8, 12, 12, 12, 12, 12, 12, 16],
      #[12, 12, 16, 12, 12, 12, 12, 16, 12, 12, 12, 16, 16, 12, 12, 12],
      #[8, 16, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 12, 16, 12, 16],
      #[12, 12, 12, 12, 12, 12, 16, 16, 12, 16, 16, 12, 16, 16, 16, 16]],
    #[
      #[8, 12, 8, 8, 8, 8, 12, 8, 12, 8, 12, 12, 8, 12, 12, 12],
      #[8, 8, 8, 12, 8, 12, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12],
      #[12, 8, 8, 12, 12, 12, 12, 12, 8, 8, 12, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 8, 12, 12, 16, 12, 12, 8, 16, 12, 12, 12, 12],
      #[8, 12, 12, 12, 8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 8, 12],
      #[12, 12, 12, 8, 12, 12, 12, 16, 8, 12, 12, 12, 12, 12, 16, 12],
      #[8, 12, 8, 12, 12, 8, 12, 16, 12, 12, 12, 12, 12, 16, 12, 16],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 16, 12, 12, 16],
      #[8, 8, 8, 12, 8, 12, 12, 12, 12, 12, 8, 12, 12, 12, 12, 16],
      #[12, 8, 12, 12, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 16, 12],
      #[8, 12, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12, 8, 16, 12, 12],
      #[12, 12, 12, 12, 12, 16, 16, 12, 12, 12, 12, 12, 12, 12, 16, 16],
      #[8, 12, 12, 12, 16, 12, 12, 12, 12, 8, 12, 12, 12, 12, 12, 16],
      #[12, 12, 12, 16, 12, 12, 12, 16, 12, 16, 12, 12, 12, 12, 12, 16],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 12, 12, 12, 16, 16],
      #[8, 12, 16, 12, 12, 16, 12, 16, 12, 16, 12, 16, 16, 16, 16, 16]],
    #[
      #[8, 8, 12, 12, 12, 12, 8, 16, 8, 12, 8, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 16],
      #[8, 12, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 12, 12, 12, 16],
      #[8, 12, 12, 12, 16, 12, 12, 12, 12, 12, 16, 12, 12, 16, 16, 16],
      #[12, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16],
      #[8, 12, 12, 16, 12, 12, 12, 12, 16, 12, 12, 16, 12, 16, 12, 16],
      #[12, 12, 16, 12, 12, 16, 12, 12, 12, 12, 12, 16, 12, 12, 16, 12],
      #[12, 12, 12, 16, 12, 16, 16, 16, 12, 16, 12, 12, 12, 16, 16, 16],
      #[12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 16, 12, 12, 12, 12, 12],
      #[8, 16, 12, 12, 12, 12, 16, 16, 12, 12, 12, 12, 12, 16, 12, 16],
      #[12, 12, 12, 8, 12, 12, 12, 16, 12, 12, 12, 16, 16, 12, 16, 16],
      #[12, 12, 12, 16, 12, 12, 12, 16, 12, 16, 16, 16, 16, 16, 12, 16],
      #[12, 12, 12, 12, 8, 12, 12, 16, 12, 16, 12, 16, 12, 16, 16, 12],
      #[12, 12, 12, 12, 12, 16, 16, 12, 12, 12, 16, 16, 16, 16, 16, 16],
      #[12, 12, 12, 16, 12, 16, 16, 16, 12, 12, 12, 16, 16, 16, 12, 16],
      #[16, 16, 12, 16, 16, 12, 16, 16, 16, 12, 16, 16, 12, 16, 16, 16]],
    #[
      #[8, 8, 8, 12, 8, 8, 8, 12, 12, 12, 8, 12, 8, 12, 12, 12],
      #[8, 8, 8, 12, 12, 12, 12, 8, 12, 8, 12, 12, 12, 12, 12, 16],
      #[8, 8, 12, 12, 8, 16, 12, 12, 8, 12, 8, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 16, 12],
      #[12, 8, 12, 12, 12, 12, 8, 12, 8, 12, 12, 12, 12, 8, 12, 12],
      #[8, 12, 12, 12, 12, 12, 12, 16, 12, 12, 8, 12, 12, 12, 12, 16],
      #[8, 12, 12, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16],
      #[8, 12, 12, 16, 12, 12, 12, 12, 12, 16, 16, 12, 12, 16, 12, 16],
      #[12, 8, 8, 8, 8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 16, 12],
      #[8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 12, 16, 12, 16, 12, 12],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 12, 16, 12, 12, 12, 12],
      #[12, 12, 8, 16, 12, 12, 16, 16, 12, 12, 12, 12, 12, 16, 12, 16],
      #[8, 12, 12, 12, 12, 12, 12, 16, 8, 12, 12, 12, 12, 16, 12, 12],
      #[12, 16, 12, 12, 12, 12, 16, 12, 12, 12, 16, 12, 12, 12, 12, 16],
      #[12, 12, 12, 12, 8, 12, 12, 16, 12, 16, 12, 16, 16, 12, 12, 16],
      #[12, 12, 12, 12, 16, 12, 12, 16, 12, 12, 16, 16, 16, 16, 16, 16]],
    #[
      #[8, 12, 12, 8, 12, 12, 12, 12, 8, 8, 12, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 8, 12, 12, 16, 8, 16, 12, 12, 12, 12, 12, 12],
      #[12, 12, 8, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 12, 12, 16],
      #[8, 12, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16, 16, 16, 12, 16],
      #[8, 12, 8, 12, 8, 12, 16, 12, 12, 12, 12, 12, 12, 16, 12, 16],
      #[12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 12, 16, 16, 12],
      #[12, 12, 12, 16, 12, 12, 12, 16, 12, 12, 12, 16, 12, 16, 12, 12],
      #[16, 12, 12, 12, 12, 16, 16, 16, 12, 12, 12, 16, 16, 12, 16, 16],
      #[8, 12, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 8, 16],
      #[12, 12, 12, 12, 16, 12, 12, 16, 12, 12, 12, 12, 12, 12, 16, 16],
      #[8, 12, 12, 12, 12, 12, 12, 16, 12, 16, 12, 12, 12, 16, 16, 16],
      #[12, 12, 16, 12, 12, 16, 12, 12, 12, 16, 16, 16, 16, 12, 16, 16],
      #[12, 12, 12, 12, 12, 12, 12, 12, 16, 12, 12, 16, 12, 12, 16, 16],
      #[12, 8, 12, 16, 12, 16, 12, 16, 12, 16, 12, 16, 16, 16, 16, 16],
      #[12, 12, 12, 16, 16, 16, 16, 12, 12, 12, 16, 12, 12, 16, 16, 16],
      #[12, 16, 16, 16, 12, 16, 16, 16, 16, 16, 12, 16, 12, 16, 16, 16]],
    #[
      #[8, 12, 8, 12, 12, 12, 12, 12, 8, 12, 12, 8, 8, 12, 12, 16],
      #[8, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
      #[8, 12, 12, 12, 12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 12, 16],
      #[12, 8, 12, 12, 12, 12, 12, 16, 12, 16, 12, 12, 16, 12, 16, 16],
      #[8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 12],
      #[12, 12, 12, 12, 8, 16, 12, 12, 12, 16, 12, 16, 12, 12, 16, 16],
      #[12, 12, 12, 16, 12, 12, 16, 12, 16, 12, 12, 12, 12, 12, 12, 16],
      #[12, 12, 12, 16, 16, 16, 12, 16, 12, 12, 12, 16, 12, 16, 16, 16],
      #[12, 12, 12, 12, 12, 8, 12, 16, 12, 12, 12, 12, 12, 12, 12, 12],
      #[12, 12, 12, 12, 12, 16, 12, 16, 8, 12, 12, 16, 16, 12, 12, 16],
      #[8, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16, 12, 16, 16, 12, 16],
      #[12, 16, 12, 12, 12, 12, 12, 16, 12, 16, 16, 16, 12, 16, 16, 16],
      #[12, 12, 8, 16, 12, 12, 12, 12, 12, 12, 16, 16, 12, 16, 12, 16],
      #[12, 12, 12, 12, 12, 12, 16, 16, 16, 12, 12, 16, 16, 16, 16, 16],
      #[12, 16, 12, 12, 12, 16, 16, 16, 12, 12, 12, 16, 12, 16, 16, 16],
      #[16, 12, 16, 16, 12, 16, 16, 16, 12, 16, 16, 16, 16, 16, 16, 12]],
    #[
      #[12, 8, 12, 12, 8, 12, 12, 12, 12, 12, 12, 16, 16, 12, 12, 12],
      #[12, 12, 8, 12, 12, 12, 12, 16, 12, 12, 12, 16, 12, 16, 16, 16],
      #[12, 12, 12, 12, 12, 12, 16, 16, 12, 12, 12, 12, 12, 16, 16, 12],
      #[12, 16, 12, 16, 12, 16, 16, 12, 12, 12, 16, 16, 12, 16, 12, 16],
      #[12, 16, 12, 12, 12, 12, 12, 16, 12, 12, 12, 16, 12, 12, 12, 16],
      #[12, 12, 12, 16, 16, 12, 16, 16, 12, 12, 16, 12, 16, 16, 12, 16],
      #[12, 12, 12, 12, 12, 16, 12, 16, 8, 16, 16, 16, 16, 16, 16, 16],
      #[12, 16, 16, 12, 12, 12, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16],
      #[8, 12, 12, 12, 12, 16, 12, 12, 12, 12, 12, 16, 12, 16, 16, 16],
      #[12, 12, 12, 16, 12, 12, 16, 12, 16, 16, 16, 12, 12, 16, 16, 16],
      #[16, 12, 12, 16, 12, 16, 12, 16, 12, 16, 12, 16, 12, 12, 16, 16],
      #[12, 12, 16, 16, 16, 16, 16, 16, 16, 12, 12, 16, 16, 16, 16, 16],
      #[12, 12, 16, 12, 12, 16, 16, 16, 12, 16, 12, 12, 16, 12, 16, 16],
      #[12, 16, 16, 16, 16, 16, 12, 16, 12, 16, 16, 16, 12, 16, 16, 16],
      #[12, 12, 16, 16, 16, 12, 12, 16, 16, 16, 16, 16, 16, 16, 16, 16],
      #[12, 16, 12, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 24]]]
  )[i.val]!)[j.val / 16]!)[j.val % 16]!

-- Separate certificates keep each kernel computation within the default resource limits.
private theorem weightTable_correct_0 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (0, j) ᵥ* generator) = weightTable 0 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_1 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (1, j) ᵥ* generator) = weightTable 1 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_2 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (2, j) ᵥ* generator) = weightTable 2 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_3 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (3, j) ᵥ* generator) = weightTable 3 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_4 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (4, j) ᵥ* generator) = weightTable 4 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_5 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (5, j) ᵥ* generator) = weightTable 5 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_6 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (6, j) ᵥ* generator) = weightTable 6 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_7 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (7, j) ᵥ* generator) = weightTable 7 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_8 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (8, j) ᵥ* generator) = weightTable 8 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_9 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (9, j) ᵥ* generator) = weightTable 9 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_10 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (10, j) ᵥ* generator) = weightTable 10 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_11 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (11, j) ᵥ* generator) = weightTable 11 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_12 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (12, j) ᵥ* generator) = weightTable 12 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_13 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (13, j) ᵥ* generator) = weightTable 13 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_14 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (14, j) ᵥ* generator) = weightTable 14 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct_15 :
    ∀ j : Fin 256, hammingNorm (messageEquiv (15, j) ᵥ* generator) = weightTable 15 j := by
  simp only [vecMul_generator]
  decide +kernel

private theorem weightTable_correct (i : Fin 16) :
    ∀ j : Fin 256, hammingNorm (messageEquiv (i, j) ᵥ* generator) = weightTable i j := by
  fin_cases i
  · exact weightTable_correct_0
  · exact weightTable_correct_1
  · exact weightTable_correct_2
  · exact weightTable_correct_3
  · exact weightTable_correct_4
  · exact weightTable_correct_5
  · exact weightTable_correct_6
  · exact weightTable_correct_7
  · exact weightTable_correct_8
  · exact weightTable_correct_9
  · exact weightTable_correct_10
  · exact weightTable_correct_11
  · exact weightTable_correct_12
  · exact weightTable_correct_13
  · exact weightTable_correct_14
  · exact weightTable_correct_15

/-- The only weights of the extended binary Golay code are `0`, `8`, `12`, `16`, and `24`. -/
theorem hammingNorm_mem {x : Fin 24 → ZMod 2} (hx : x ∈ code) :
    hammingNorm x ∈ ({0, 8, 12, 16, 24} : Finset ℕ) := by
  obtain ⟨a, rfl⟩ := Matrix.mem_generatedBy_iff.mp (code_def ▸ hx)
  obtain ⟨⟨i, j⟩, rfl⟩ := messageEquiv.surjective a
  rw [weightTable_correct]
  exact (by decide +kernel : ∀ i j, weightTable i j ∈ ({0, 8, 12, 16, 24} : Finset ℕ)) i j

/-- The extended binary Golay code is doubly even. -/
@[simp]
theorem isDoublyEven_code : BinaryCode.IsDoublyEven code := by
  rw [code_def, BinaryCode.isDoublyEven_generatedBy_iff]
  exact ⟨by decide +kernel, generator_mul_transpose⟩

private theorem weightDistribution_eq_card (w : ℕ) :
    (code : Set (Fin 24 → ZMod 2)).weightDistribution w =
      Fintype.card {p : Fin 16 × Fin 256 // weightTable p.1 p.2 = w} := by
  rw [Set.weightDistribution_def, ← Nat.card_eq_fintype_card]
  symm
  apply Nat.card_congr
  let e := messageEquiv.trans encodingEquiv.toEquiv
  refine (e.subtypeEquiv (q := fun x : code ↦ hammingNorm (x : Fin 24 → ZMod 2) = w)
    (fun p ↦ ?_)).trans (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : Fin 24 → ZMod 2 ↦ x ∈ code)
      (fun x ↦ hammingNorm x = w))
  rcases p with ⟨i, j⟩
  simp only [e, Equiv.trans_apply, LinearEquiv.coe_toEquiv, encodingEquiv_apply,
    ← vecMul_generator, weightTable_correct]

private theorem weightTable_counts :
    ∀ w : Fin 25, Fintype.card {p : Fin 16 × Fin 256 // weightTable p.1 p.2 = w.val} =
      if w.val = 0 ∨ w.val = 24 then 1 else
      if w.val = 8 ∨ w.val = 16 then 759 else if w.val = 12 then 2576 else 0 := by
  decide +kernel

/-- The full weight distribution of the extended binary Golay code. -/
@[simp]
theorem weightDistribution_code (w : ℕ) :
    (code : Set (Fin 24 → ZMod 2)).weightDistribution w =
      if w = 0 ∨ w = 24 then 1 else
      if w = 8 ∨ w = 16 then 759 else if w = 12 then 2576 else 0 := by
  by_cases hw : w < 25
  · rw [weightDistribution_eq_card]
    exact weightTable_counts ⟨w, hw⟩
  · rw [Set.weightDistribution_eq_zero_of_card_lt (by simpa using (by omega : 24 < w))]
    simp only [show w ≠ 0 by omega, show w ≠ 24 by omega, show w ≠ 8 by omega,
      show w ≠ 16 by omega, show w ≠ 12 by omega, or_self, ite_false]

/-- The homogeneous weight enumerator is
`X²⁴ + 759 X¹⁶Y⁸ + 2576 X¹²Y¹² + 759 X⁸Y¹⁶ + Y²⁴`. -/
@[simp]
theorem weightEnumerator_code :
    (code : Set (Fin 24 → ZMod 2)).weightEnumerator =
      MvPolynomial.X 0 ^ 24 + 759 * MvPolynomial.X 0 ^ 16 * MvPolynomial.X 1 ^ 8 +
      2576 * MvPolynomial.X 0 ^ 12 * MvPolynomial.X 1 ^ 12 +
      759 * MvPolynomial.X 0 ^ 8 * MvPolynomial.X 1 ^ 16 + MvPolynomial.X 1 ^ 24 := by
  simp [Set.weightEnumerator_def, Finset.sum_range_succ]

/-- The extended binary Golay code has minimum distance eight. -/
@[simp]
theorem hammingMinDist_code : Set.hammingMinDist (code : Set (Fin 24 → ZMod 2)) = 8 := by
  rw [← Submodule.coe_toAddSubgroup, Set.hammingMinDist_eq_sInf_weightDistribution
    (Set.toFinite _), Submodule.coe_toAddSubgroup]
  apply IsLeast.csInf_eq
  constructor
  · norm_num
  · intro w hw
    simp only [Set.mem_ofPred_eq, weightDistribution_code] at hw
    split_ifs at hw <;> omega

end TauCeti.BinaryGolay
