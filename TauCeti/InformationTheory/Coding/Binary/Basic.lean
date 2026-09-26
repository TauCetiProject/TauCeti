/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Basic
public import TauCeti.InformationTheory.Coding.Elementary.Basic
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.Field.ZMod

import Mathlib.Tactic.FinCases

/-!
# Even and doubly-even binary codes

Binary Hamming weights detect Euclidean orthogonality: the dot product is the parity of the
intersection of supports, and the weight of a sum subtracts twice that intersection. Consequently,
a binary linear code whose weights are all divisible by four is self-orthogonal.

An even code is characterized by membership of the all-ones word in its dual. In particular,
a binary self-dual code is even and contains the all-ones word. These facts supply the elementary
parity constraints used in the study of doubly-even self-dual codes.

The conventions and weight-intersection argument follow Huffman and Pless,
*Fundamentals of Error-Correcting Codes*, Chapters 1 and 9.
-/

public section

namespace TauCeti

open Matrix

variable {ι : Type*} [Fintype ι]

/-- For binary words, the weight of a sum plus twice the size of the support intersection is
the sum of the weights. -/
theorem hammingNorm_add_add_two_mul_card_support_inter (x y : ι → ZMod 2) :
    hammingNorm (x + y) +
        2 * (Finset.univ.filter (fun i ↦ x i ≠ 0 ∧ y i ≠ 0)).card =
      hammingNorm x + hammingNorm y := by
  simp only [hammingNorm, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h (a b : ZMod 2) :
      (if a + b ≠ 0 then 1 else 0) + 2 * (if a ≠ 0 ∧ b ≠ 0 then 1 else 0) =
        (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0 : ℕ) := by
    fin_cases a <;> fin_cases b <;> decide
  exact h (x i) (y i)

/-- The binary dot product is the cardinality of the support intersection, reduced modulo two. -/
theorem dotProduct_eq_card_support_inter (x y : ι → ZMod 2) :
    x ⬝ᵥ y = ((Finset.univ.filter (fun i ↦ x i ≠ 0 ∧ y i ≠ 0)).card : ZMod 2) := by
  simp only [dotProduct, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  generalize x i = a, y i = b
  fin_cases a <;> fin_cases b <;> decide

/-- A binary word has self-dot-product equal to its weight modulo two. -/
@[simp]
theorem dotProduct_self_eq_hammingNorm (x : ι → ZMod 2) :
    x ⬝ᵥ x = (hammingNorm x : ZMod 2) := by
  simp [dotProduct_eq_card_support_inter, hammingNorm]

/-- Pairing a binary word with the all-ones word gives its weight modulo two. -/
@[simp]
theorem dotProduct_one_eq_hammingNorm (x : ι → ZMod 2) :
    x ⬝ᵥ (1 : ι → ZMod 2) = (hammingNorm x : ZMod 2) := by
  simp [dotProduct_eq_card_support_inter, hammingNorm]

/-- The sum of two binary words of weights divisible by four again has weight divisible by
four exactly when the two words are orthogonal. -/
@[simp]
theorem four_dvd_hammingNorm_add_iff {x y : ι → ZMod 2}
    (hx : 4 ∣ hammingNorm x) (hy : 4 ∣ hammingNorm y) :
    4 ∣ hammingNorm (x + y) ↔ x ⬝ᵥ y = 0 := by
  rw [dotProduct_eq_card_support_inter, ZMod.natCast_eq_zero_iff]
  have h := hammingNorm_add_add_two_mul_card_support_inter x y
  omega

namespace BinaryCode

/-- A binary code is even if all its words have even Hamming weight. -/
def IsEven (C : LinearCode (ZMod 2) ι) : Prop :=
  ∀ x ∈ C, Even (hammingNorm x)

/-- A binary code is doubly even if all its Hamming weights are divisible by four. -/
def IsDoublyEven (C : LinearCode (ZMod 2) ι) : Prop :=
  ∀ x ∈ C, 4 ∣ hammingNorm x

variable {C D : LinearCode (ZMod 2) ι}

/-- Evenness can be checked word by word. -/
theorem isEven_iff : IsEven C ↔ ∀ x ∈ C, Even (hammingNorm x) :=
  Iff.rfl

/-- Double evenness can be checked by divisibility of the weight of each word by four. -/
theorem isDoublyEven_iff : IsDoublyEven C ↔ ∀ x ∈ C, 4 ∣ hammingNorm x :=
  Iff.rfl

/-- Every doubly-even code is even. -/
theorem IsDoublyEven.isEven (hC : IsDoublyEven C) : IsEven C := by
  intro x hx
  exact even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 4) (hC x hx))

/-- Evenness passes to subcodes. -/
theorem IsEven.mono (hD : IsEven D) (hCD : C ≤ D) : IsEven C :=
  fun x hx ↦ hD x (hCD hx)

/-- Double evenness passes to subcodes. -/
theorem IsDoublyEven.mono (hD : IsDoublyEven D) (hCD : C ≤ D) : IsDoublyEven C :=
  fun x hx ↦ hD x (hCD hx)

/-- An even binary code is precisely one whose dual contains the all-ones word. -/
theorem isEven_iff_one_mem_euclideanDual :
    IsEven C ↔ (1 : ι → ZMod 2) ∈ C.euclideanDual := by
  simp [IsEven, Submodule.mem_euclideanDual, ZMod.natCast_eq_zero_iff_even]

/-- For binary codes, evenness is exactly containment in the single-parity-check code. -/
theorem isEven_iff_le_singleParityCheckCode :
    IsEven C ↔ C ≤ singleParityCheckCode (ZMod 2) ι := by
  rw [isEven_iff]
  simp only [SetLike.le_def, mem_singleParityCheckCode]
  have hsum (x : ι → ZMod 2) : ∑ i, x i = (hammingNorm x : ZMod 2) := by
    simpa [dotProduct] using dotProduct_one_eq_hammingNorm x
  simp only [hsum, ZMod.natCast_eq_zero_iff_even]

/-- Every self-orthogonal binary code is even. -/
theorem isEven_of_le_euclideanDual (hC : C ≤ C.euclideanDual) : IsEven C := by
  intro x hx
  have h := Submodule.mem_euclideanDual.mp (hC hx) x hx
  simpa [ZMod.natCast_eq_zero_iff_even] using h

/-- A doubly-even binary linear code is self-orthogonal. -/
theorem IsDoublyEven.le_euclideanDual (hC : IsDoublyEven C) : C ≤ C.euclideanDual := by
  rw [Submodule.le_euclideanDual_self_iff]
  intro x hx y hy
  rw [dotProduct_eq_card_support_inter, ZMod.natCast_eq_zero_iff]
  have hxy := hammingNorm_add_add_two_mul_card_support_inter x y
  have hx4 := hC x hx
  have hy4 := hC y hy
  have hsum4 := hC (x + y) (C.add_mem hx hy)
  omega

/-- A self-dual binary code contains the all-ones word. -/
theorem one_mem_of_eq_euclideanDual (hC : C = C.euclideanDual) :
    (1 : ι → ZMod 2) ∈ C := by
  rw [hC]
  exact isEven_iff_one_mem_euclideanDual.mp (isEven_of_le_euclideanDual hC.le)

end BinaryCode

end TauCeti
