/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule
public import Mathlib.Algebra.MonoidAlgebra.Defs

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

* `TauCeti.PopaZagier.weight M`: twelve times the coefficient of `M` in (15);
  `TauCeti.PopaZagier.weight₁`, ..., `TauCeti.PopaZagier.weight₄`: the same for `T₁`, ..., `T₄`.
* `TauCeti.TraceFormulaMatrixModule.popaZagierElement n`: Popa–Zagier's element of `ℚ[ℳₙ]`.

## Main results

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
  rcases (by lia : weight₁ a b c d ≠ 0 ∨ weight₂ a b c d ≠ 0 ∨ weight₃ a b c d ≠ 0 ∨
      weight₄ a b c d ≠ 0) with h | h | h | h <;>
    simp only [weight₁, weight₂, weight₃, weight₄, ite_ne_right_iff] at h <;>
    grind [chainWeight₃, chainWeight₄]

/-- Every matrix `(a b; c d)` of nonzero weight has positive determinant `n` and entries at most
`2n` in absolute value. -/
private theorem bounds_of_weight_ne_zero {a b c d : ℤ}
    (h : weight₁ a b c d - weight₂ a b c d - weight₃ a b c d - weight₄ a b c d ≠ 0) :
    0 < a * d - b * c ∧ |a| ≤ 2 * (a * d - b * c) ∧ |b| ≤ 2 * (a * d - b * c) ∧
      |c| ≤ 2 * (a * d - b * c) ∧ |d| ≤ 2 * (a * d - b * c) := by
  simp only [abs_le]
  rcases cases_of_weight_ne_zero h with h | h | h | h
  · -- `T₁`: `d ≥ a - c ≥ 1` and `n ≥ d (a - c) + a c`
    have : d ≤ a * d - b * c := by nlinarith
    have : a ≤ a * d - b * c := by nlinarith
    lia
  · -- `T₂`: `n ≥ a (d - b) + b d` with `d - b ≥ 1` and `b d ≥ 0`
    have : a ≤ a * d - b * c := by nlinarith
    have : -b ≤ a * d - b * c := by nlinarith
    have : c ≤ 2 * (a * d - b * c) := by nlinarith
    lia
  · -- `T₃`: `n = c (-b) - a (a - d) + a² ≥ c² + a²`
    have : -b ≤ a * d - b * c := by nlinarith
    have : -a ≤ a * d - b * c := by nlinarith
    lia
  · -- `T₄`: `n = c (-b) + d (a - d) + d² ≥ b² + d (-b) + d²`
    have : d * -b + d * d ≤ a * d := by nlinarith
    have : b * b ≤ -b * c := by nlinarith
    have : -b ≤ 2 * (a * d - b * c) := by nlinarith [sq_nonneg (2 * d - b)]
    have : -d ≤ 2 * (a * d - b * c) := by nlinarith [sq_nonneg (d - 2 * b)]
    have : c ≤ 2 * (a * d - b * c) := by nlinarith [sq_nonneg (d - b)]
    lia

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

variable {n : ℤ}

/-- The coefficients of Popa–Zagier's element: the class of `A` gets
`(weight A + weight (-A)) / 12`. -/
private def popaZagierCoeff (n : ℤ) : TraceFormulaMatrixModule n → ℚ :=
  Quotient.lift (fun A ↦ ((PopaZagier.weight A.1 : ℚ) + PopaZagier.weight (-A.1)) / 12)
    fun _ _ ↦ by rintro (rfl | rfl) <;> simp [add_comm]

/-- The coefficients of Popa–Zagier's element have finite support. -/
private theorem finite_support_popaZagierCoeff (n : ℤ) :
    (Function.support (popaZagierCoeff n)).Finite := by
  -- matrices of nonzero weight have entries in `[-2n, 2n]`
  have hbox (A : TraceFormulaMatrix n) (h : PopaZagier.weight A.1 ≠ 0) (i j : Fin 2) :
      A.1 i j ∈ Set.Icc (-(2 * n)) (2 * n) := by
    have := PopaZagier.abs_le_of_weight_ne_zero h i j
    rwa [A.2, abs_le] at this
  refine (((Set.Finite.pi' fun _ ↦ Set.Finite.pi' fun _ ↦
    Set.finite_Icc (-(2 * n)) (2 * n)).preimage (f := fun A : TraceFormulaMatrix n ↦ A.1)
    fun A _ B _ ↦ FixedDetMatrices.ext' _ _).image mk).subset fun x hx ↦ ?_
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  -- a class in the support has a representative of nonzero weight
  obtain h | h : PopaZagier.weight A.1 ≠ 0 ∨ PopaZagier.weight (-A.1) ≠ 0 := by
    by_contra! h
    simp [popaZagierCoeff, h] at hx
  exacts [⟨A, hbox A h, rfl⟩, ⟨-A, hbox (-A) h, mk_neg A⟩]

/-- **Popa–Zagier's explicit Hecke element** of `ℚ[ℳₙ]` (written `Tₙ` with a tilde in their
paper), their eq. (15): `T₁ - T₂ - T₃ - T₄`, where `T₁ = ⟨a - d ≤ -b ≤ c; 0 ≤ c < a⟩`,
`T₂ = ⟨-b ≤ a - d ≤ c; b < d ≤ 0⟩`, `T₃ = ⟨0 ≤ a - d ≤ c ≤ -b; a ≤ 0 < c⟩` and
`T₄ = ⟨0 ≤ a - d ≤ -b ≤ c; d ≤ 0 < -b⟩`. See `coeff_popaZagierElement_mk` for its
coefficients. -/
noncomputable def popaZagierElement (n : ℤ) : ℚ[TraceFormulaMatrixModule n] :=
  .ofCoeff (.ofSupportFinite (popaZagierCoeff n) (finite_support_popaZagierCoeff n))

/-- The coefficient of the class of `A` in Popa–Zagier's element is
`(weight A + weight (-A)) / 12`. -/
@[simp]
theorem coeff_popaZagierElement_mk (A : TraceFormulaMatrix n) :
    (popaZagierElement n).coeff (mk A) =
      ((PopaZagier.weight A.1 : ℚ) + PopaZagier.weight (-A.1)) / 12 := by
  simp [popaZagierElement, popaZagierCoeff, Finsupp.ofSupportFinite_coe]

/-- With Popa–Zagier's representatives, `c > 0` or `c = 0 < a`, the coefficient of the class of
`A = (a b; c d)` is `weight A / 12`. -/
theorem coeff_popaZagierElement_mk_of_pos (A : TraceFormulaMatrix n)
    (hA : 0 < A.1 1 0 ∨ A.1 1 0 = 0 ∧ 0 < A.1 0 0) :
    (popaZagierElement n).coeff (mk A) = PopaZagier.weight A.1 / 12 := by
  have : PopaZagier.weight (-A.1) = 0 := by
    by_contra h
    have := PopaZagier.pos_or_eq_zero_and_pos_of_weight_ne_zero h
    simp only [Matrix.neg_apply] at this
    lia
  simp [this]

end TraceFormulaMatrixModule

end TauCeti
