/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.EuclideanDual

/-!
# Repetition and single-parity-check codes

The repetition code consists of constant words, and the single-parity-check code consists of
words whose coordinate sum is zero. They are Euclidean duals. A positive-length repetition
code has as many words as its alphabet; at length zero it has only one word.
Over a finite field with `q` elements, the parity-check code has `q^(n - 1)` words at length `n`,
including length zero, where the natural-number subtraction gives exponent zero.

Their weight enumerators are computed in
`TauCeti.InformationTheory.Coding.Elementary.WeightEnumerator`.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §§1.2–1.4.
-/

public section

namespace TauCeti

open Finset

variable (R ι : Type*)

/-- The repetition code is the submodule of constant words. -/
def repetitionCode [Semiring R] : Submodule R (ι → R) :=
  LinearMap.range (LinearMap.const (R := R) (ι := ι) (M₂ := R))

/-- Membership in the repetition code means being constant. -/
@[simp]
theorem mem_repetitionCode [Semiring R] {x : ι → R} :
    x ∈ repetitionCode R ι ↔ ∃ a, Function.const ι a = x := by
  simp [repetitionCode, LinearMap.mem_range]

/-- The single-parity-check code is the kernel of the coordinate-sum map. -/
def singleParityCheckCode [Semiring R] [Fintype ι] : Submodule R (ι → R) :=
  LinearMap.ker (∑ i, LinearMap.proj i)

/-- Membership in the single-parity-check code means having coordinate sum zero. -/
@[simp]
theorem mem_singleParityCheckCode [Semiring R] [Fintype ι] {x : ι → R} :
    x ∈ singleParityCheckCode R ι ↔ ∑ i, x i = 0 := by
  simp [singleParityCheckCode, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply]

/-- The dual of the repetition code is the single-parity-check code. -/
@[simp]
theorem euclideanDual_repetitionCode [CommSemiring R] [Fintype ι] :
    Submodule.euclideanDual (repetitionCode R ι) = singleParityCheckCode R ι := by
  ext y
  simp only [Submodule.mem_euclideanDual, mem_repetitionCode, mem_singleParityCheckCode]
  constructor
  · intro h
    simpa [dotProduct] using h (Function.const ι 1) ⟨1, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    simp [dotProduct, ← mul_sum, h]

/-- The dual of the single-parity-check code over a field is the repetition code. -/
@[simp]
theorem euclideanDual_singleParityCheckCode [Field R] [Fintype ι] :
    Submodule.euclideanDual (singleParityCheckCode R ι) = repetitionCode R ι := by
  rw [← euclideanDual_repetitionCode, Submodule.euclideanDual_euclideanDual]

/-- With no coordinates, the repetition code is zero. -/
@[simp]
theorem repetitionCode_eq_bot_of_isEmpty [Semiring R] [IsEmpty ι] : repetitionCode R ι = ⊥ :=
  Subsingleton.elim _ _

/-- With no coordinates, the parity-check code is the whole word space. -/
@[simp]
theorem singleParityCheckCode_eq_top_of_isEmpty [Semiring R] [Fintype ι] [IsEmpty ι] :
    singleParityCheckCode R ι = ⊤ := by
  ext x
  simp

/-- A positive-length repetition code has as many words as its alphabet. -/
@[simp↓]
theorem natCard_repetitionCode [Semiring R] [Nonempty ι] :
    Nat.card (repetitionCode R ι) = Nat.card R := by
  unfold repetitionCode
  exact Nat.card_range_of_injective (Function.const_injective (α := ι) (β := R))

/-- Over a finite field, the parity-check code has `q^(n - 1)` words, including at length zero. -/
@[simp↓]
theorem natCard_singleParityCheckCode [Field R] [Finite R] [Fintype ι] :
    Nat.card (singleParityCheckCode R ι) = Nat.card R ^ (Fintype.card ι - 1) := by
  cases isEmpty_or_nonempty ι with
  | inl hι => simp [Fintype.card_eq_zero]
  | inr hι =>
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := R))
    rw [mul_pow_sub_one (ne_of_gt (Fintype.card_pos))]
    simpa only [natCard_repetitionCode, euclideanDual_repetitionCode] using
      Submodule.natCard_mul_natCard_euclideanDual (repetitionCode R ι)

end TauCeti
