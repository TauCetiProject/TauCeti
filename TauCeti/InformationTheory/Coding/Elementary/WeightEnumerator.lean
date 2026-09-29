/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Elementary.Basic
public import TauCeti.InformationTheory.Coding.Weight.Enumerator

/-!
# Weight enumerators of repetition and single-parity-check codes

The repetition code consists of constant words, and the single-parity-check code consists of
words whose coordinate sum is zero. They are Euclidean duals. Their homogeneous weight
enumerators give explicit examples of the MacWilliams transform, alongside the zero code and
the whole word space.

For a coordinate type of cardinality `n` over a finite alphabet with `q` letters, the
positive-length repetition enumerator is `X^n + (q - 1) Y^n`, and the parity-check enumerator
satisfies `q W(X,Y) = (X + (q - 1) Y)^n + (q - 1) (X - Y)^n` over the integers at every length.
The nonempty hypothesis for the repetition formula matters: at length zero the repetition code
has one word, rather than `q` words.

The parity-check enumerator is computed by counting, without the MacWilliams identity, so that
comparing the two enumerators is an independent check of that identity. More generally, over a
finite additive group `A` with `q` elements, the words with coordinate sum `a` have enumerator

```text
q W(X,Y) = (X + (q - 1) Y)^n + (q - 1) (X - Y)^n    if a = 0,
q W(X,Y) = (X + (q - 1) Y)^n - (X - Y)^n            if a ≠ 0.
```

Splitting off one coordinate `c` reduces the sum `a` to `a - c` on the remaining coordinates,
and both formulas follow together by induction on the coordinate type.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §§1.2–1.4 and §7.2.
-/

public section

namespace TauCeti

open Finset MvPolynomial

variable (R ι : Type*)

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

end Enumerators

section CosetEnumerators

variable [Fintype ι] {A : Type*} [AddCommGroup A] [DecidableEq A]

/-- The coset enumerator in summed form: over a finite additive group with `q`
elements, `q` times the sum of the weight monomials `∏ i, (X or Y)` of the words with coordinate
sum `a` is `(X + (q - 1) Y)^n + (q [a = 0] - 1) (X - Y)^n`. -/
private theorem card_mul_sum_ite_sum_eq [Fintype A] [DecidableEq ι] (a : A) :
    (Nat.card A : MvPolynomial (Fin 2) ℤ) *
        ∑ x : ι → A, (if ∑ i, x i = a then ∏ i, (if x i = 0 then X 0 else X 1) else 0) =
      (X 0 + (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) * X 1) ^ Fintype.card ι +
        (if a = 0 then (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) else -1) *
          (X 0 - X 1) ^ Fintype.card ι := by
  revert a
  refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ [DecidableEq ι] (a : A),
    (Nat.card A : MvPolynomial (Fin 2) ℤ) *
        ∑ x : ι → A, (if ∑ i, x i = a then ∏ i, (if x i = 0 then X 0 else X 1) else 0) =
      (X 0 + (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) * X 1) ^ Fintype.card ι +
        (if a = 0 then (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) else -1) *
          (X 0 - X 1) ^ Fintype.card ι) ?_ ?_ ?_ ι
  · -- Relabelling the coordinates along an equivalence does not change either side.
    intro α β _ e h _ a
    let _ := Fintype.ofEquiv β e.symm
    classical
    rw [← Fintype.card_congr e, ← h a]
    congr 1
    refine (Fintype.sum_equiv (e.arrowCongr (Equiv.refl A)) _ _ fun x ↦ ?_).symm
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl]
    rw [← Fintype.sum_equiv e (fun i ↦ x i) _ (fun i ↦ by simp),
      ← Fintype.prod_equiv e (fun i ↦ if x i = 0 then X 0 else X 1) _ (fun i ↦ by simp)]
  · -- With no coordinates, the empty word is the only word, and its sum is zero.
    intro _ a
    simp [eq_comm (a := (0 : A))]
    split_ifs <;> simp
  · -- A word on `Option α` is a letter `c` at `none` and a word on `α` with sum `a - c`.
    intro α _ h _ a
    classical
    rw [← Fintype.sum_equiv Equiv.piOptionEquivProd.symm _ _ (fun _ ↦ rfl),
      Fintype.sum_prod_type]
    simp only [Fintype.sum_option, Fintype.prod_option, Equiv.piOptionEquivProd_symm_apply,
      Fintype.card_option]
    have hc (c : A) : (∑ y : α → A, if c + ∑ i, y i = a then
        (if c = 0 then (X 0 : MvPolynomial (Fin 2) ℤ) else X 1) *
          ∏ i, (if y i = 0 then X 0 else X 1) else 0) =
        (if c = 0 then X 0 else X 1) *
          ∑ y : α → A, if ∑ i, y i = a - c then ∏ i, (if y i = 0 then X 0 else X 1) else 0 := by
      rw [mul_sum]
      refine sum_congr rfl fun y _ ↦ ?_
      simp only [eq_sub_iff_add_eq', mul_ite, mul_zero]
    rw [sum_congr rfl fun c _ ↦ hc c, mul_sum]
    simp_rw [mul_left_comm (Nat.card A : MvPolynomial (Fin 2) ℤ), h]
    -- Only the letter `c = a` contributes the correction term `q (X or Y) (X - Y)^n`.
    have hs (c : A) : (if c = 0 then (X 0 : MvPolynomial (Fin 2) ℤ) else X 1) *
        ((X 0 + (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) * X 1) ^ Fintype.card α +
          (if a - c = 0 then (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) else -1) *
            (X 0 - X 1) ^ Fintype.card α) =
        (if c = 0 then X 0 else X 1) *
            ((X 0 + (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) * X 1) ^ Fintype.card α -
              (X 0 - X 1) ^ Fintype.card α) +
          if a = c then (Nat.card A : MvPolynomial (Fin 2) ℤ) *
            (if a = 0 then X 0 else X 1) * (X 0 - X 1) ^ Fintype.card α else 0 := by
      by_cases hac : a = c
      · subst hac
        simp only [sub_self, ite_true]
        ring
      · simp only [sub_eq_zero, hac, ite_false]
        ring
    simp_rw [hs, sum_add_distrib, ← sum_mul, sum_ite_eq, ite_eq_left (mem_univ _),
      sum_ite_eq_zero_X_zero_X_one]
    split_ifs <;> ring

/-- **The weight enumerator of a coset of the parity-check code.** Over a finite additive group
with `q` elements, the words of length `n` with coordinate sum `a` have enumerator `W` with
`q W(X,Y) = (X + (q - 1) Y)^n + (q - 1) (X - Y)^n` when `a = 0`, and
`q W(X,Y) = (X + (q - 1) Y)^n - (X - Y)^n` otherwise. -/
theorem natCard_mul_weightEnumerator_setOf_sum_eq [Finite A] (a : A) :
    (Nat.card A : MvPolynomial (Fin 2) ℤ) * {x : ι → A | ∑ i, x i = a}.weightEnumerator =
      (X 0 + (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) * X 1) ^ Fintype.card ι +
        (if a = 0 then (Nat.card A - 1 : MvPolynomial (Fin 2) ℤ) else -1) *
          (X 0 - X 1) ^ Fintype.card ι := by
  classical
  let _ : Fintype A := .ofFinite A
  have hset : (Set.toFinite {x : ι → A | ∑ i, x i = a}).toFinset =
      univ.filter fun x ↦ ∑ i, x i = a := by
    ext x
    simp
  rw [Set.weightEnumerator_eq_sum (Set.toFinite _), hset, sum_filter]
  simp_rw [← prod_ite_eq_zero_eq_pow_mul_pow_hammingNorm]
  exact card_mul_sum_ite_sum_eq ι a

/-- The integral weight-enumerator formula for a single-parity-check code at any length. -/
theorem natCard_mul_weightEnumerator_singleParityCheckCode [Ring R] [Finite R] [DecidableEq R] :
    (Nat.card R : MvPolynomial (Fin 2) ℤ) *
        (singleParityCheckCode R ι : Set (ι → R)).weightEnumerator =
      (X 0 + (Nat.card R - 1 : MvPolynomial (Fin 2) ℤ) * X 1) ^ Fintype.card ι +
        (Nat.card R - 1 : MvPolynomial (Fin 2) ℤ) * (X 0 - X 1) ^ Fintype.card ι := by
  have hset : (singleParityCheckCode R ι : Set (ι → R)) = {x : ι → R | ∑ i, x i = 0} := by
    ext x
    simp
  simp only [hset, natCard_mul_weightEnumerator_setOf_sum_eq, ↓reduceIte]

end CosetEnumerators

end TauCeti
