/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.MacWilliams

/-!
# Repetition and single-parity-check codes

The repetition code consists of constant words, and the single-parity-check code consists of
words whose coordinate sum is zero. They are Euclidean duals. Their homogeneous weight
enumerators give explicit examples of the MacWilliams transform, alongside the zero code and
the whole word space.

For a nonempty coordinate type of cardinality `n` over a finite field with `q` elements, the
repetition enumerator is `X^n + (q - 1) Y^n`, and the parity-check enumerator satisfies
`q W(X,Y) = (X + (q - 1) Y)^n + (q - 1) (X - Y)^n` over the integers. The nonempty hypothesis
matters: at length zero the repetition code has one word, rather than `q` words.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §§1.2–1.4 and §7.2.
-/

public section

namespace TauCeti

open Finset MvPolynomial

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
theorem repetitionCode_of_isEmpty [Semiring R] [IsEmpty ι] : repetitionCode R ι = ⊥ :=
  Subsingleton.elim _ _

/-- With no coordinates, the parity-check code is the whole word space. -/
@[simp]
theorem singleParityCheckCode_of_isEmpty [Semiring R] [Fintype ι] [IsEmpty ι] :
    singleParityCheckCode R ι = ⊤ := by
  ext x
  simp

/-- A positive-length repetition code has as many words as its alphabet. -/
@[simp↓]
theorem natCard_repetitionCode [Semiring R] [Nonempty ι] :
    Nat.card (repetitionCode R ι) = Nat.card R := by
  unfold repetitionCode
  exact Nat.card_range_of_injective (Function.const_injective (α := ι) (β := R))

section Enumerators

variable [Fintype ι] [Semiring R] [DecidableEq R]

/-- The positive-length repetition code has enumerator `X^n + (q - 1) Y^n`. -/
@[simp]
theorem weightEnumerator_repetitionCode [Finite R] [Nonempty ι] :
    (repetitionCode R ι : Set (ι → R)).weightEnumerator =
      X 0 ^ Fintype.card ι + (Nat.card R - 1 : MvPolynomial (Fin 2) ℤ) *
        X 1 ^ Fintype.card ι := by
  classical
  let _ : Fintype R := .ofFinite R
  rw [Set.weightEnumerator_eq_sum (Set.toFinite _)]
  have hset : (Set.toFinite (repetitionCode R ι : Set (ι → R))).toFinset =
      univ.image (Function.const ι) := by
    ext x
    simp
  rw [hset, sum_image (fun _ _ _ _ h ↦ Function.const_injective h)]
  simp_rw [hammingNorm_const]
  have hs (a : R) :
      (X 0 : MvPolynomial (Fin 2) ℤ) ^ (Fintype.card ι - if a = 0 then 0 else Fintype.card ι) *
        X 1 ^ (if a = 0 then 0 else Fintype.card ι) =
      X 1 ^ Fintype.card ι + if a = 0 then X 0 ^ Fintype.card ι - X 1 ^ Fintype.card ι
        else 0 := by
    split_ifs <;> simp
  simp_rw [hs]
  simp [sum_add_distrib, Nat.card_eq_fintype_card]
  ring

/-- The integral weight-enumerator formula for a positive-length single-parity-check code. -/
theorem natCard_mul_weightEnumerator_singleParityCheckCode {F : Type*} [Field F] [Finite F]
    [DecidableEq F] [Nonempty ι] :
    (Nat.card F : MvPolynomial (Fin 2) ℤ) *
        (singleParityCheckCode F ι : Set (ι → F)).weightEnumerator =
      (X 0 + (Nat.card F - 1 : MvPolynomial (Fin 2) ℤ) * X 1) ^ Fintype.card ι +
        (Nat.card F - 1 : MvPolynomial (Fin 2) ℤ) * (X 0 - X 1) ^ Fintype.card ι := by
  have h := Submodule.natCard_mul_weightEnumerator_euclideanDual (repetitionCode F ι)
  rw [natCard_repetitionCode, euclideanDual_repetitionCode, weightEnumerator_repetitionCode] at h
  simpa only [map_add, map_mul, map_pow, map_sub, map_natCast, map_one, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

end Enumerators

end TauCeti
