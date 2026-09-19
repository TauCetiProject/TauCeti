/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.SplittingCriterion

/-!
# The norm-equation Hilbert symbol

`TauCeti.hilbertSymbol a b` is the sign `+1` when `b = x² - a y²` is solvable, and
`-1` otherwise. The definition makes sense over any field. This file supplies the
field-generic part of its theory: the quadratic-algebra norm and quaternion splitting
criteria, symmetry, square rescaling, and the elementary split values.

The comparison theorems reuse the four-fold splitting criterion in
`TauCeti.Algebra.Quaternion.SplittingCriterion`. No local classification enters the
definition. In particular, no bimultiplicativity is asserted over an arbitrary field:
that property needs a local norm-index theorem.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Proposition 1.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, §2.7.
-/

public section
noncomputable section

open scoped Quaternion

namespace TauCeti

variable {K : Type*} [Field K]

open Classical in
/-- The norm-equation Hilbert symbol, with values in the two integer units. -/
def hilbertSymbol (a b : Kˣ) : ℤˣ :=
  if ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 then 1 else -1

open Classical in
/-- The defining norm equation for the Hilbert symbol. -/
theorem hilbertSymbol_def (a b : Kˣ) :
    hilbertSymbol a b = if ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 then 1 else -1 :=
  (rfl)

/-- The symbol is positive exactly when the norm equation has a solution. -/
theorem hilbertSymbol_eq_one_iff (a b : Kˣ) :
    hilbertSymbol a b = 1 ↔ ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 := by
  classical
  simp [hilbertSymbol_def]

/-- The symbol is negative exactly when the norm equation has no solution. -/
theorem hilbertSymbol_eq_neg_one_iff (a b : Kˣ) :
    hilbertSymbol a b = -1 ↔ ¬∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 := by
  classical
  simp [hilbertSymbol_def]

/-- The symbol is positive exactly when the second parameter is a norm from the
quadratic algebra, including the split case. -/
theorem hilbertSymbol_eq_one_iff_exists_norm_eq (a b : Kˣ) :
    hilbertSymbol a b = 1 ↔ ∃ z : QuadraticAlgebra K (a : K) 0, z.norm = b := by
  rw [hilbertSymbol_eq_one_iff]
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨⟨x, y⟩, by simpa [QuadraticAlgebra.norm_def, pow_two, mul_assoc] using h.symm⟩
  · rintro ⟨z, h⟩
    exact ⟨z.re, z.im, by simpa [QuadraticAlgebra.norm_def, pow_two, mul_assoc] using h.symm⟩

/-- The second parameter is a nonzero norm exactly when it is the norm of a unit. -/
theorem hilbertSymbol_eq_one_iff_exists_unit_norm_eq (a b : Kˣ) :
    hilbertSymbol a b = 1 ↔
      ∃ z : (QuadraticAlgebra K (a : K) 0)ˣ, (z : QuadraticAlgebra K (a : K) 0).norm = b := by
  rw [hilbertSymbol_eq_one_iff_exists_norm_eq]
  constructor
  · rintro ⟨z, h⟩
    have hz := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (h ▸ b.isUnit)
    exact ⟨hz.unit, by simpa using h⟩
  · rintro ⟨z, h⟩
    exact ⟨z, h⟩

/-- A square second parameter has positive symbol. -/
theorem hilbertSymbol_eq_one_of_isSquare_right (a : Kˣ) {b : Kˣ} (hb : IsSquare b) :
    hilbertSymbol a b = 1 := by
  obtain ⟨c, rfl⟩ := hb
  exact (hilbertSymbol_eq_one_iff _ _).mpr ⟨c, 0, by simp [pow_two]⟩

/-- The second parameter `1` has positive symbol. -/
@[simp] theorem hilbertSymbol_one_right (a : Kˣ) : hilbertSymbol a 1 = 1 :=
  hilbertSymbol_eq_one_of_isSquare_right a (by simp)

/-- The norm of the square-root generator is `-a`. -/
@[simp] theorem hilbertSymbol_neg_self (a : Kˣ) : hilbertSymbol a (-a) = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr ⟨0, 1, by simp⟩

/-- The Steinberg relation follows from the norm of `1 + √a`. -/
@[simp] theorem hilbertSymbol_one_sub (a : Kˣ) (h : (1 : K) - a ≠ 0) :
    hilbertSymbol a (Units.mk0 (1 - a) h) = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr ⟨1, 1, by simp⟩

/-- Multiplying the second parameter by a square does not change the symbol. -/
@[simp] theorem hilbertSymbol_mul_sq_right (a b c : Kˣ) :
    hilbertSymbol a (b * c ^ 2) = hilbertSymbol a b := by
  classical
  have he : (∃ x y : K, ((b * c ^ 2 : Kˣ) : K) = x ^ 2 - a * y ^ 2) ↔
      ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    constructor
    · rintro ⟨x, y, h⟩
      refine ⟨x / c, y / c, ?_⟩
      field_simp
      linear_combination h
    · rintro ⟨x, y, h⟩
      refine ⟨x * c, y * c, ?_⟩
      rw [h]
      ring
  simp only [hilbertSymbol_def, he]

/-- Multiplying the first parameter by a square does not change the symbol. -/
@[simp] theorem hilbertSymbol_mul_sq_left (a b c : Kˣ) :
    hilbertSymbol (a * c ^ 2) b = hilbertSymbol a b := by
  classical
  have he : (∃ x y : K, (b : K) = x ^ 2 - (a * c ^ 2 : Kˣ) * y ^ 2) ↔
      ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    constructor
    · rintro ⟨x, y, h⟩
      refine ⟨x, c * y, ?_⟩
      rw [h]
      ring
    · rintro ⟨x, y, h⟩
      refine ⟨x, y / c, ?_⟩
      rw [h]
      field_simp
  simp only [hilbertSymbol_def, he]

/-- The Hilbert symbol depends only on the square classes of its parameters. -/
theorem hilbertSymbol_congr_sq (a a' b b' : Kˣ)
    (ha : IsSquare (a * a')) (hb : IsSquare (b * b')) :
    hilbertSymbol a b = hilbertSymbol a' b' := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  have ha' : a = a' * (c / a') ^ 2 := by
    rw [div_pow, pow_two c, ← hc]
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm]
  have hb' : b = b' * (d / b') ^ 2 := by
    rw [div_pow, pow_two d, ← hd]
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm]
  rw [ha', hb', hilbertSymbol_mul_sq_left, hilbertSymbol_mul_sq_right]

variable [Invertible (2 : K)]

/-- The positive sign is equivalent to splitting the associated quaternion algebra. -/
theorem hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix (a b : Kˣ) :
    hilbertSymbol a b = 1 ↔
      Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  rw [hilbertSymbol_eq_one_iff,
    QuaternionAlgebra.nonempty_algEquiv_matrix_iff_exists_eq_sq_sub_mul_sq]

/-- The positive sign is equivalent to isotropy of the ternary form `⟨1,-a,-b⟩`. -/
theorem hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares (a b : Kˣ) :
    hilbertSymbol a b = 1 ↔
      ¬(QuadraticMap.weightedSumSquares K ![1, -(a : K), -(b : K)]).Anisotropic := by
  rw [hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix,
    QuaternionAlgebra.nonempty_algEquiv_matrix_iff_not_anisotropic_weightedSumSquares]

/-- Isomorphic quaternion algebras have the same norm-equation sign. -/
theorem hilbertSymbol_eq_of_nonempty_algEquiv {a b c d : Kˣ}
    (h : Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] ℍ[K,(c : K),(d : K)])) :
    hilbertSymbol a b = hilbertSymbol c d := by
  classical
  obtain ⟨e⟩ := h
  have he : (∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2) ↔
      ∃ x y : K, (d : K) = x ^ 2 - c * y ^ 2 := by
    rw [← QuaternionAlgebra.nonempty_algEquiv_matrix_iff_exists_eq_sq_sub_mul_sq,
      ← QuaternionAlgebra.nonempty_algEquiv_matrix_iff_exists_eq_sq_sub_mul_sq]
    exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩
  simp only [hilbertSymbol_def, he]

/-- Symmetry of the norm-equation Hilbert symbol. -/
theorem hilbertSymbol_comm (a b : Kˣ) : hilbertSymbol a b = hilbertSymbol b a :=
  hilbertSymbol_eq_of_nonempty_algEquiv ⟨_root_.QuaternionAlgebra.swapEquiv _ _⟩

/-- A square first parameter has positive symbol. -/
theorem hilbertSymbol_eq_one_of_isSquare_left {a : Kˣ} (ha : IsSquare a) (b : Kˣ) :
    hilbertSymbol a b = 1 := by
  rw [hilbertSymbol_comm]
  exact hilbertSymbol_eq_one_of_isSquare_right b ha

/-- The first parameter `1` has positive symbol. -/
@[simp] theorem hilbertSymbol_one_left (b : Kˣ) : hilbertSymbol 1 b = 1 :=
  hilbertSymbol_eq_one_of_isSquare_left (by simp) b

end TauCeti
