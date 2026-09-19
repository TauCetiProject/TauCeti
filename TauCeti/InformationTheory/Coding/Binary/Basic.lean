/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Basic
public import TauCeti.InformationTheory.Coding.EuclideanDual
public import TauCeti.InformationTheory.Coding.WeightEnumerator
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

open Matrix MvPolynomial

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

/-- A self-dual binary code has `2^(n/2)` words, where `n` is its length. -/
theorem natCard_of_eq_euclideanDual (hC : C = C.euclideanDual) :
    Nat.card C = 2 ^ (Fintype.card ι / 2) := by
  have hdim := Submodule.two_mul_finrank_eq_card_of_eq_euclideanDual hC
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  congr 1
  omega

/-- The weight enumerator of a doubly-even code is unchanged when its second argument is
multiplied by a fourth root of unity. Taking `R = ℂ[X,Y]` gives the polynomial symmetry. -/
@[simp]
theorem IsDoublyEven.aeval_weightEnumerator_mul {R : Type*} [CommRing R]
    (hC : IsDoublyEven C) {ζ : R} (hζ : ζ ^ 4 = 1) (x y : R) :
    aeval ![x, ζ * y] (C : Set (ι → ZMod 2)).weightEnumerator =
      aeval ![x, y] (C : Set (ι → ZMod 2)).weightEnumerator := by
  classical
  rw [Set.weightEnumerator_eq_sum (Set.toFinite _)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨k, hk⟩ := isDoublyEven_iff.mp hC c (by simpa using hc)
  simp [hk, mul_pow, pow_mul, hζ]

end BinaryCode

end TauCeti
