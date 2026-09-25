/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Popa–Zagier's explicit Hecke element

Popa and Zagier prove the Eichler–Selberg trace formula with an explicit element of
`ℛₙ = ℚ[ℳₙ]` (written `Tₙ` with a tilde in their paper), given by their eq. (15) as
`T₁ - T₂ - T₃ - T₄` with
* `T₁ = ⟨a - d ≤ -b ≤ c; 0 ≤ c < a⟩`,
* `T₂ = ⟨-b ≤ a - d ≤ c; b < d ≤ 0⟩`,
* `T₃ = ⟨0 ≤ a - d ≤ c ≤ -b; a ≤ 0 < c⟩`,
* `T₄ = ⟨0 ≤ a - d ≤ -b ≤ c; d ≤ 0 < -b⟩`.

Here `⟨#⟩` is the sum of the classes of the integral matrices `M = (a b; c d)` of determinant `n`
satisfying the inequalities `#`, written in two lines (separated here by `;`), each counted with a
coefficient `c(M)` fixed by the inequalities of the first line that are equalities for `M`: it is
`1` if there are none, `1/2` if there is one, and `1/4`, `1/3` or `1/6` if there are two and they
are independent (`A ≤ B`, `C ≤ D`), overlapping (`A ≤ B`, `A ≤ C`) or nested (`A ≤ B ≤ C`).
Popa and Zagier represent classes by matrices with `c ≥ 0`. Every matrix occurring in (15) has
`c > 0`, or `c = 0 < a`, so at most one of the representatives `±M` of a class occurs, and the
coefficient of the class of `M` is the sum of the weights of `M` and `-M`.

## Main definitions

* `TauCeti.TraceFormulaMatrixModule.ofWeight n w B hw`: the element of `k[ℳₙ]` in which the class
  of `A` has coefficient `w A + w (-A)`, for a weight `w` on integral matrices that vanishes on
  every determinant-`n` matrix with an entry larger than `B` in absolute value.
* `TauCeti.PopaZagier.weight M`: twelve times the coefficient of `M` in (15);
  `TauCeti.PopaZagier.weight₁`, ..., `TauCeti.PopaZagier.weight₄`: the same for `T₁`, ..., `T₄`.
* `TauCeti.TraceFormulaMatrixModule.popaZagierElement k n`: Popa–Zagier's element of `k[ℳₙ]`,
  for a division ring `k`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.coeff_ofWeight_mk`: the coefficient of the class of `A` in
  `ofWeight n w B hw` is `w A + w (-A)`.
* `TauCeti.PopaZagier.det_pos_of_weight_ne_zero`, `TauCeti.PopaZagier.abs_le_of_weight_ne_zero`:
  every matrix occurring in (15) has positive determinant `n` and entries at most `2n` in absolute
  value, so only finitely many occur for each `n` (Popa–Zagier, Lemma 4(a)).
* `TauCeti.PopaZagier.weight₂_eq_weight₁`: `T₂ = T₁·U`, where `U = T S = (1 -1; 1 0)`.
* `TauCeti.TraceFormulaMatrixModule.coeff_popaZagierElement_mk`: the coefficient of the class of
  `A` is `(weight A + weight (-A)) / 12`; it is `weight A / 12` if `c > 0` or `c = 0 < a`
  (`TauCeti.TraceFormulaMatrixModule.coeff_popaZagierElement_mk_of_pos`).

## Implementation notes

Popa and Zagier define their element by eq. (14) and prove that it equals (15) (Lemma 4(b)); we
define it by (15).

The weights are integers, twelve times Popa–Zagier's coefficients, so that identities between
them are statements of integer linear arithmetic. Their definitions are exposed (`@[expose]`) so
that other modules can unfold them in such identities and evaluate them by `decide +kernel`.

Elements of `k[ℳₙ]` given by a weight on integral matrices, over any semiring `k`, are built by
`ofWeight`: the class of `A` gets `w A + w (-A)`, and a bound `B` on the entries of the
determinant-`n` matrices of nonzero weight makes the support finite. The element
`popaZagierElement k n` is `ofWeight` applied to the weight divided by `12` in `k`; when `12` is
invertible in `k`, for instance for `k = ℚ`, its coefficients are Popa–Zagier's.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4.
-/

public section

open MonoidAlgebra
open scoped MatrixGroups

namespace TauCeti

namespace PopaZagier

/-! ### The weights -/

/-- Twelve times Popa–Zagier's coefficient `c(M)` for a first line `x ≤ y ≤ z`: `12`, `6` or `2`
according as none, one or both of the two (nested) inequalities are equalities, and `0` if
the line fails. -/
@[expose] def chainWeight₃ (x y z : ℤ) : ℤ :=
  if x < y ∧ y < z then 12 else if x = y ∧ y = z then 2 else if x ≤ y ∧ y ≤ z then 6 else 0

/-- Twelve times Popa–Zagier's coefficient `c(M)` for a first line `w ≤ x ≤ y ≤ z`: `12` or `6`
according as none or one of the three inequalities is an equality, `3` if the outer two are
(independent), `2` if two adjacent ones are (nested), and `0` if the line fails. The value when
all three are equalities is not covered by the rule; it does not occur in (15). -/
@[expose] def chainWeight₄ (w x y z : ℤ) : ℤ :=
  if w < x ∧ x < y ∧ y < z then 12
  else if w ≤ x ∧ x ≤ y ∧ y ≤ z then
    if w = x ∧ y = z then 3 else if w = x ∧ x = y ∨ x = y ∧ y = z then 2 else 6
  else 0

/-- Twelve times the coefficient of `(a b; c d)` in `T₁ = ⟨a - d ≤ -b ≤ c; 0 ≤ c < a⟩`. -/
@[expose] def weight₁ (a b c d : ℤ) : ℤ :=
  if 0 ≤ c ∧ c < a then chainWeight₃ (a - d) (-b) c else 0

/-- Twelve times the coefficient of `(a b; c d)` in `T₂ = ⟨-b ≤ a - d ≤ c; b < d ≤ 0⟩`. -/
@[expose] def weight₂ (a b c d : ℤ) : ℤ :=
  if b < d ∧ d ≤ 0 then chainWeight₃ (-b) (a - d) c else 0

/-- Twelve times the coefficient of `(a b; c d)` in `T₃ = ⟨0 ≤ a - d ≤ c ≤ -b; a ≤ 0 < c⟩`. -/
@[expose] def weight₃ (a b c d : ℤ) : ℤ :=
  if a ≤ 0 ∧ 0 < c then chainWeight₄ 0 (a - d) c (-b) else 0

/-- Twelve times the coefficient of `(a b; c d)` in `T₄ = ⟨0 ≤ a - d ≤ -b ≤ c; d ≤ 0 < -b⟩`. -/
@[expose] def weight₄ (a b c d : ℤ) : ℤ :=
  if d ≤ 0 ∧ 0 < -b then chainWeight₄ 0 (a - d) (-b) c else 0

/-- Twelve times the coefficient of the matrix `M` in Popa–Zagier's eq. (15),
`T₁ - T₂ - T₃ - T₄`. -/
@[expose] def weight (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  weight₁ (M 0 0) (M 0 1) (M 1 0) (M 1 1) - weight₂ (M 0 0) (M 0 1) (M 1 0) (M 1 1) -
    weight₃ (M 0 0) (M 0 1) (M 1 0) (M 1 1) - weight₄ (M 0 0) (M 0 1) (M 1 0) (M 1 1)

/-- **`T₂ = T₁·U`**: the weight of `M = (a b; c d)` in `T₂` is the weight of
`M U⁻¹ = (-b, a + b; -d, c + d)` in `T₁`, where `U = T S = (1 -1; 1 0)`. -/
theorem weight₂_eq_weight₁ (a b c d : ℤ) : weight₂ a b c d = weight₁ (-b) (a + b) (-d) (c + d) := by
  grind [weight₁, weight₂, chainWeight₃]

/-! ### Finiteness -/

/-- A matrix `(a b; c d)` of nonzero weight satisfies the inequalities of one of the four sums of
(15). -/
private theorem cases_of_weight_ne_zero {a b c d : ℤ}
    (h : weight₁ a b c d - weight₂ a b c d - weight₃ a b c d - weight₄ a b c d ≠ 0) :
    0 ≤ c ∧ c < a ∧ a - d ≤ -b ∧ -b ≤ c ∨ b < d ∧ d ≤ 0 ∧ -b ≤ a - d ∧ a - d ≤ c ∨
      a ≤ 0 ∧ 0 < c ∧ 0 ≤ a - d ∧ a - d ≤ c ∧ c ≤ -b ∨
      d ≤ 0 ∧ 0 < -b ∧ 0 ≤ a - d ∧ a - d ≤ -b ∧ -b ≤ c := by
  simp only [weight₁, weight₂, weight₃, weight₄] at h
  split_ifs at h <;> grind [chainWeight₃, chainWeight₄]

/-- Every matrix `(a b; c d)` satisfying the inequalities of `T₁` has positive determinant
`n = ad - bc` and entries at most `2n` in absolute value. -/
private theorem bounds_of_T₁ {a b c d : ℤ} (hc : 0 ≤ c) (hca : c < a) (hd : a - d ≤ -b)
    (hb : -b ≤ c) :
    0 < a * d - b * c ∧ |a| ≤ 2 * (a * d - b * c) ∧ |b| ≤ 2 * (a * d - b * c) ∧
      |c| ≤ 2 * (a * d - b * c) ∧ |d| ≤ 2 * (a * d - b * c) := by
  simp only [abs_le]
  have h₁ := mul_nonneg (by omega : 0 ≤ d - a - b) hc
  have : d ≤ a * d - b * c := by
    linear_combination h₁ + mul_nonneg (by omega : 0 ≤ d) (by omega : 0 ≤ a - 1 - c) +
      mul_nonneg (by omega : 0 ≤ a) hc
  have : a ≤ a * d - b * c := by
    linear_combination h₁ + mul_nonneg (by omega : 0 ≤ d - 1) (by omega : 0 ≤ a - c) +
      mul_nonneg hc (by omega : 0 ≤ a - 1)
  omega

/-- Every matrix `(a b; c d)` satisfying the inequalities of `T₂` has positive determinant
`n = ad - bc` and entries at most `2n` in absolute value. -/
private theorem bounds_of_T₂ {a b c d : ℤ} (hbd : b < d) (hd : d ≤ 0) (hb : -b ≤ a - d)
    (hc : a - d ≤ c) :
    0 < a * d - b * c ∧ |a| ≤ 2 * (a * d - b * c) ∧ |b| ≤ 2 * (a * d - b * c) ∧
      |c| ≤ 2 * (a * d - b * c) ∧ |d| ≤ 2 * (a * d - b * c) := by
  simp only [abs_le]
  have h₁ := mul_nonneg (by omega : 0 ≤ -b) (by omega : 0 ≤ c - a + d)
  have : a ≤ a * d - b * c := by
    linear_combination h₁ + mul_nonneg (by omega : 0 ≤ a) (by omega : 0 ≤ d - b - 1) +
      mul_nonneg (by omega : 0 ≤ -d) (by omega : 0 ≤ -b)
  have : -b ≤ a * d - b * c := by
    linear_combination h₁ + mul_nonneg (by omega : 0 ≤ a + b - d) (by omega : 0 ≤ d - b) +
      mul_nonneg (by omega : 0 ≤ -b) (by omega : 0 ≤ d - b - 1) + mul_self_nonneg d
  have : c ≤ 2 * (a * d - b * c) := by
    linear_combination mul_nonneg (by omega : 0 ≤ c - a + d) (by omega : 0 ≤ -2 * b - 1) +
      2 * mul_nonneg (by omega : 0 ≤ a - d) (by omega : 0 ≤ -b - 1 + d) +
      (by omega : 0 ≤ a - d) + 2 * mul_self_nonneg d
  omega

/-- Every matrix `(a b; c d)` satisfying the inequalities of `T₃` has positive determinant
`n = ad - bc` and entries at most `2n` in absolute value. -/
private theorem bounds_of_T₃ {a b c d : ℤ} (ha : a ≤ 0) (hc : 0 < c) (hd : 0 ≤ a - d)
    (hdc : a - d ≤ c) (hcb : c ≤ -b) :
    0 < a * d - b * c ∧ |a| ≤ 2 * (a * d - b * c) ∧ |b| ≤ 2 * (a * d - b * c) ∧
      |c| ≤ 2 * (a * d - b * c) ∧ |d| ≤ 2 * (a * d - b * c) := by
  simp only [abs_le]
  have : -b ≤ a * d - b * c := by
    linear_combination mul_nonneg (by omega : 0 ≤ -a) (by omega : 0 ≤ -d) +
      mul_nonneg (by omega : 0 ≤ -b) (by omega : 0 ≤ c - 1)
  have : -a ≤ a * d - b * c := by
    linear_combination mul_nonneg (by omega : 0 ≤ -a) (by omega : 0 ≤ a - d) +
      Int.le_self_sq (-a) + mul_nonneg (by omega : 0 ≤ -b) hc.le
  omega

/-- Every matrix `(a b; c d)` satisfying the inequalities of `T₄` has positive determinant
`n = ad - bc` and entries at most `2n` in absolute value. -/
private theorem bounds_of_T₄ {a b c d : ℤ} (hd : d ≤ 0) (hb : 0 < -b) (had : 0 ≤ a - d)
    (hab : a - d ≤ -b) (hbc : -b ≤ c) :
    0 < a * d - b * c ∧ |a| ≤ 2 * (a * d - b * c) ∧ |b| ≤ 2 * (a * d - b * c) ∧
      |c| ≤ 2 * (a * d - b * c) ∧ |d| ≤ 2 * (a * d - b * c) := by
  simp only [abs_le]
  have h₁ := mul_nonneg_of_nonpos_of_nonpos hd (by omega : a + b - d ≤ 0)
  have h₂ := mul_nonneg (by omega : 0 ≤ -b) (by omega : 0 ≤ c + b)
  have h₃ := mul_nonneg (by omega : 0 ≤ -b) (by omega : 0 ≤ -b - 1)
  have : -b ≤ 2 * (a * d - b * c) := by
    linear_combination 2 * h₁ + 2 * h₂ + sq_nonneg (d - b) + mul_self_nonneg d + h₃
  have : -d ≤ 2 * (a * d - b * c) := by
    linear_combination 2 * h₁ + 2 * h₂ + 2 * sq_nonneg (d - b) +
      mul_nonneg (by omega : 0 ≤ -d) (by omega : 0 ≤ -2 * b - 1)
  have : c ≤ 2 * (a * d - b * c) := by
    linear_combination 2 * h₁ + mul_nonneg (by omega : 0 ≤ c + b) (by omega : 0 ≤ -2 * b - 1) +
      sq_nonneg (d - b) + mul_self_nonneg d + h₃
  omega

/-- Every matrix `(a b; c d)` of nonzero weight has positive determinant `ad - bc` and entries at
most twice its determinant in absolute value. -/
private theorem bounds_of_weight_ne_zero {a b c d : ℤ}
    (h : weight₁ a b c d - weight₂ a b c d - weight₃ a b c d - weight₄ a b c d ≠ 0) :
    0 < a * d - b * c ∧ |a| ≤ 2 * (a * d - b * c) ∧ |b| ≤ 2 * (a * d - b * c) ∧
      |c| ≤ 2 * (a * d - b * c) ∧ |d| ≤ 2 * (a * d - b * c) := by
  rcases cases_of_weight_ne_zero h with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ |
    ⟨h₁, h₂, h₃, h₄, h₅⟩ | ⟨h₁, h₂, h₃, h₄, h₅⟩
  exacts [bounds_of_T₁ h₁ h₂ h₃ h₄, bounds_of_T₂ h₁ h₂ h₃ h₄, bounds_of_T₃ h₁ h₂ h₃ h₄ h₅,
    bounds_of_T₄ h₁ h₂ h₃ h₄ h₅]

/-- **Popa–Zagier, Lemma 4(a)**, positivity: every matrix of nonzero weight has positive
determinant. -/
theorem det_pos_of_weight_ne_zero {M : Matrix (Fin 2) (Fin 2) ℤ} (h : weight M ≠ 0) : 0 < M.det :=
  M.det_fin_two ▸ (bounds_of_weight_ne_zero h).1

/-- **Popa–Zagier, Lemma 4(a)**, finiteness: every matrix of nonzero weight has entries at most
twice its determinant in absolute value. -/
theorem abs_le_of_weight_ne_zero {M : Matrix (Fin 2) (Fin 2) ℤ} (h : weight M ≠ 0) (i j : Fin 2) :
    |M i j| ≤ 2 * M.det := by
  obtain ⟨-, h⟩ := bounds_of_weight_ne_zero h
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, h]

/-- Every matrix `M = (a b; c d)` of nonzero weight has `c > 0`, or `c = 0 < a`. -/
theorem pos_or_eq_zero_and_pos_of_weight_ne_zero {M : Matrix (Fin 2) (Fin 2) ℤ} (h : weight M ≠ 0) :
    0 < M 1 0 ∨ M 1 0 = 0 ∧ 0 < M 0 0 := by
  have := cases_of_weight_ne_zero h
  lia

end PopaZagier

/-! ### The element -/

namespace TraceFormulaMatrixModule

variable {k : Type*} {n : ℤ}

section Semiring

variable [Semiring k]

/-- The element of `k[ℳₙ]` in which the class of `A` has coefficient `w A + w (-A)`, for a weight
`w` on integral matrices that vanishes on every determinant-`n` matrix with an entry larger than
`B` in absolute value. Its coefficients are given by `coeff_ofWeight_mk`. -/
noncomputable def ofWeight (n : ℤ) (w : Matrix (Fin 2) (Fin 2) ℤ → k) (B : ℤ)
    (hw : ∀ A : TraceFormulaMatrix n, w A.1 ≠ 0 → ∀ i j, |A.1 i j| ≤ B) :
    k[TraceFormulaMatrixModule n] :=
  .ofCoeff <| .ofSupportFinite
    (Quotient.lift (fun A : TraceFormulaMatrix n ↦ w A.1 + w (-A.1))
      fun _ _ ↦ by rintro (rfl | rfl) <;> simp [add_comm]) <| by
    -- a class in the support has a representative of nonzero weight
    refine ((FixedDetMatrices.finite_setOf_abs_le n B).image mk).subset fun x hx ↦ ?_
    induction x using TraceFormulaMatrixModule.induction with | h A => ?_
    obtain h | h : w A.1 ≠ 0 ∨ w (-A.1) ≠ 0 := by
      by_contra! h
      simp [h] at hx
    exacts [⟨A, hw A h, rfl⟩, ⟨-A, hw (-A) h, mk_neg A⟩]

/-- The coefficient of the class of `A` in `ofWeight n w B hw` is `w A + w (-A)`. -/
@[simp]
theorem coeff_ofWeight_mk (w : Matrix (Fin 2) (Fin 2) ℤ → k) (B : ℤ)
    (hw : ∀ A : TraceFormulaMatrix n, w A.1 ≠ 0 → ∀ i j, |A.1 i j| ≤ B)
    (A : TraceFormulaMatrix n) :
    (ofWeight n w B hw).coeff (mk A) = w A.1 + w (-A.1) := by
  simp [ofWeight, Finsupp.ofSupportFinite_coe]

end Semiring

section DivisionRing

variable [DivisionRing k]

variable (k) in
/-- **Popa–Zagier's explicit Hecke element** of `k[ℳₙ]` (written `Tₙ` with a tilde in their
paper), their eq. (15): `T₁ - T₂ - T₃ - T₄` (see `TauCeti.PopaZagier.weight`), with the weights
divided by `12` in `k`. Its coefficients are given by `coeff_popaZagierElement_mk`. -/
noncomputable def popaZagierElement (n : ℤ) : k[TraceFormulaMatrixModule n] :=
  ofWeight n (fun M ↦ (PopaZagier.weight M : k) / 12) (2 * n) fun A h i j ↦ by
    have h : PopaZagier.weight A.1 ≠ 0 := fun h' ↦ h (by simp [h'])
    simpa [A.2] using PopaZagier.abs_le_of_weight_ne_zero h i j

/-- The coefficient of the class of `A` in Popa–Zagier's element is
`(weight A + weight (-A)) / 12`. -/
@[simp]
theorem coeff_popaZagierElement_mk (A : TraceFormulaMatrix n) :
    (popaZagierElement k n).coeff (mk A) =
      ((PopaZagier.weight A.1 : k) + PopaZagier.weight (-A.1)) / 12 := by
  simp [popaZagierElement, add_div]

/-- With Popa–Zagier's representatives, `c > 0` or `c = 0 < a`, the coefficient of the class of
`A = (a b; c d)` is `weight A / 12`. -/
theorem coeff_popaZagierElement_mk_of_pos (A : TraceFormulaMatrix n)
    (hA : 0 < A.1 1 0 ∨ A.1 1 0 = 0 ∧ 0 < A.1 0 0) :
    (popaZagierElement k n).coeff (mk A) = PopaZagier.weight A.1 / 12 := by
  have : PopaZagier.weight (-A.1) = 0 := by
    by_contra h
    have := PopaZagier.pos_or_eq_zero_and_pos_of_weight_ne_zero h
    simp only [Matrix.neg_apply] at this
    lia
  simp [this]

end DivisionRing

end TraceFormulaMatrixModule

end TauCeti
