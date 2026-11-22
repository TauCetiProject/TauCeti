/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import TauCeti.Analysis.CStarAlgebra.CauchySchwarz

/-!
# Column and row square functions in C⋆-algebras

For a finite family `a : ι → A` in a non-unital C⋆-algebra `A` with its `StarOrderedRing` order,
`columnSquare a = (∑ k, star (a k) * a k)^(1/2)` and `rowSquare a = (∑ k, a k * star (a k))^(1/2)`.
This file develops their positivity, uniqueness, star duality, algebraic symmetries, C⋆-norm
formulas, and operator Cauchy–Schwarz inequality.

## Main declarations

* `TauCeti.columnSquare`, `TauCeti.rowSquare`: column and row square functions.
* `TauCeti.columnSquare_eq_of_mul_self`, `TauCeti.rowSquare_eq_of_mul_self`: uniqueness from square.
* `TauCeti.norm_columnSquare`, `TauCeti.norm_rowSquare`: C⋆-norm formulas.
* `TauCeti.norm_sum_mul_le_norm_rowSquare_mul_norm_columnSquare`: operator Cauchy–Schwarz.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, CUP, 1995, Ch. 1.
* G. Pisier and Q. Xu, *Non-commutative `Lᵖ`-spaces*, *Handbook of the Geometry of Banach Spaces*,
  Vol. 2, North-Holland, 2003, §2.
-/

public section

noncomputable section

open scoped BigOperators ComplexStarModule

namespace TauCeti

variable {ι A : Type*} [Fintype ι] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The column square function `(∑ k, star (a k) * a k)^(1/2)` of a finite family. -/
def columnSquare (a : ι → A) : A := CFC.sqrt (∑ k, star (a k) * a k)

/-- Unfolding definition of `columnSquare`. -/
theorem columnSquare_def (a : ι → A) : columnSquare a = CFC.sqrt (∑ k, star (a k) * a k) := (rfl)

/-- The row square function `(∑ k, a k * star (a k))^(1/2)` of a finite family. -/
def rowSquare (a : ι → A) : A := CFC.sqrt (∑ k, a k * star (a k))

/-- Unfolding definition of `rowSquare`. -/
theorem rowSquare_def (a : ι → A) : rowSquare a = CFC.sqrt (∑ k, a k * star (a k)) := (rfl)

/-- `columnSquare a` is nonnegative in the C⋆-algebra order. -/
theorem columnSquare_nonneg (a : ι → A) : 0 ≤ columnSquare a := CFC.sqrt_nonneg _

/-- `rowSquare a` is nonnegative in the C⋆-algebra order. -/
theorem rowSquare_nonneg (a : ι → A) : 0 ≤ rowSquare a := CFC.sqrt_nonneg _

/-- `columnSquare a` is self-adjoint. -/
theorem isSelfAdjoint_columnSquare (a : ι → A) : IsSelfAdjoint (columnSquare a) :=
  (columnSquare_nonneg a).isSelfAdjoint

/-- `rowSquare a` is self-adjoint. -/
theorem isSelfAdjoint_rowSquare (a : ι → A) : IsSelfAdjoint (rowSquare a) :=
  (rowSquare_nonneg a).isSelfAdjoint

/-- The adjoint of `columnSquare a` is `columnSquare a`. -/
@[simp] theorem star_columnSquare (a : ι → A) : star (columnSquare a) = columnSquare a :=
  (isSelfAdjoint_columnSquare a).star_eq

/-- The adjoint of `rowSquare a` is `rowSquare a`. -/
@[simp] theorem star_rowSquare (a : ι → A) : star (rowSquare a) = rowSquare a :=
  (isSelfAdjoint_rowSquare a).star_eq

/-- Squaring `columnSquare a` recovers `∑ k, star (a k) * a k`. -/
@[simp] theorem columnSquare_mul_self (a : ι → A) :
    columnSquare a * columnSquare a = ∑ k, star (a k) * a k :=
  CFC.sqrt_mul_sqrt_self _ (Finset.sum_nonneg fun k _ => star_mul_self_nonneg (a k))

/-- Squaring `rowSquare a` recovers `∑ k, a k * star (a k)`. -/
@[simp] theorem rowSquare_mul_self (a : ι → A) :
    rowSquare a * rowSquare a = ∑ k, a k * star (a k) :=
  CFC.sqrt_mul_sqrt_self _ (Finset.sum_nonneg fun k _ => mul_star_self_nonneg (a k))

/-- Uniqueness of `columnSquare`: any nonnegative square root of `∑ k, star (a k) * a k` equals
`columnSquare a`. -/
theorem columnSquare_eq_of_mul_self {a : ι → A} {b : A}
    (hsq : b * b = ∑ k, star (a k) * a k) (hb : 0 ≤ b) : columnSquare a = b :=
  CFC.sqrt_unique hsq hb

/-- Uniqueness of `rowSquare`: any nonnegative square root of `∑ k, a k * star (a k)` equals
`rowSquare a`. -/
theorem rowSquare_eq_of_mul_self {a : ι → A} {b : A}
    (hsq : b * b = ∑ k, a k * star (a k)) (hb : 0 ≤ b) : rowSquare a = b :=
  CFC.sqrt_unique hsq hb

/-- The row square function of `a` is the column square function of `fun k => star (a k)`. -/
theorem rowSquare_eq_columnSquare_star (a : ι → A) :
    rowSquare a = columnSquare (fun k => star (a k)) := by simp [rowSquare_def, columnSquare_def]

/-- The column square function of `a` is the row square function of `fun k => star (a k)`. -/
theorem columnSquare_eq_rowSquare_star (a : ι → A) :
    columnSquare a = rowSquare (fun k => star (a k)) := by simp [rowSquare_def, columnSquare_def]

/-- At `0`, `columnSquare` vanishes. -/
@[simp] theorem columnSquare_zero : columnSquare (0 : ι → A) = 0 := by simp [columnSquare_def]

/-- At `0`, `rowSquare` vanishes. -/
@[simp] theorem rowSquare_zero : rowSquare (0 : ι → A) = 0 := by simp [rowSquare_def]

/-- On an empty index type, `columnSquare` vanishes. -/
@[simp] theorem columnSquare_of_isEmpty [IsEmpty ι] (a : ι → A) : columnSquare a = 0 := by
  simp [columnSquare_def]

/-- On an empty index type, `rowSquare` vanishes. -/
@[simp] theorem rowSquare_of_isEmpty [IsEmpty ι] (a : ι → A) : rowSquare a = 0 := by
  simp [rowSquare_def]

/-- `columnSquare` is invariant under negation. -/
@[simp] theorem columnSquare_neg (a : ι → A) : columnSquare (-a) = columnSquare a := by
  simp [columnSquare_def]

/-- `rowSquare` is invariant under negation. -/
@[simp] theorem rowSquare_neg (a : ι → A) : rowSquare (-a) = rowSquare a := by simp [rowSquare_def]

/-- `columnSquare` is absolutely homogeneous under complex scalar multiplication. -/
theorem columnSquare_smul (c : ℂ) (a : ι → A) : columnSquare (c • a) = ‖c‖ • columnSquare a := by
  refine columnSquare_eq_of_mul_self ?_ (smul_nonneg (norm_nonneg c) (columnSquare_nonneg a))
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← sq, columnSquare_mul_self, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Pi.smul_apply, star_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← Complex.coe_smul, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

/-- `rowSquare` is absolutely homogeneous under complex scalar multiplication. -/
theorem rowSquare_smul (c : ℂ) (a : ι → A) : rowSquare (c • a) = ‖c‖ • rowSquare a := by
  rw [rowSquare_eq_columnSquare_star, rowSquare_eq_columnSquare_star, ← Pi.star_def, star_smul,
    Pi.star_def, columnSquare_smul, norm_star]

/-- Reindexing a family along an equivalence preserves `columnSquare`. -/
theorem columnSquare_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (a : ι → A) :
    columnSquare (a ∘ e) = columnSquare a := by
  simp only [columnSquare_def, Function.comp_apply]
  rw [Fintype.sum_equiv e _ (fun i => star (a i) * a i) fun _ => rfl]

/-- Reindexing a family along an equivalence preserves `rowSquare`. -/
theorem rowSquare_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (a : ι → A) :
    rowSquare (a ∘ e) = rowSquare a := by
  simp only [rowSquare_def, Function.comp_apply]
  rw [Fintype.sum_equiv e _ (fun i => a i * star (a i)) fun _ => rfl]

/-- Flipping signs by `δ : ι → ℤˣ` preserves `columnSquare`. -/
@[simp] theorem columnSquare_units_smul (δ : ι → ℤˣ) (a : ι → A) :
    columnSquare (fun k => δ k • a k) = columnSquare a := by
  simp only [columnSquare_def]; congr 1
  exact Finset.sum_congr rfl fun k _ => by rcases Int.units_eq_one_or (δ k) with h | h <;> simp [h]

/-- Flipping signs by `δ : ι → ℤˣ` preserves `rowSquare`. -/
@[simp] theorem rowSquare_units_smul (δ : ι → ℤˣ) (a : ι → A) :
    rowSquare (fun k => δ k • a k) = rowSquare a := by
  simp only [rowSquare_def]; congr 1
  exact Finset.sum_congr rfl fun k _ => by rcases Int.units_eq_one_or (δ k) with h | h <;> simp [h]

/-- The norm of `columnSquare a` is `√‖∑ k, star (a k) * a k‖`. -/
theorem norm_columnSquare (a : ι → A) : ‖columnSquare a‖ = √‖∑ k, star (a k) * a k‖ :=
  CFC.norm_sqrt _ (Finset.sum_nonneg fun k _ => star_mul_self_nonneg (a k))

/-- The norm of `rowSquare a` is `√‖∑ k, a k * star (a k)‖`. -/
theorem norm_rowSquare (a : ι → A) : ‖rowSquare a‖ = √‖∑ k, a k * star (a k)‖ :=
  CFC.norm_sqrt _ (Finset.sum_nonneg fun k _ => mul_star_self_nonneg (a k))

/-- Squaring `‖columnSquare a‖` gives `‖∑ k, star (a k) * a k‖`. -/
theorem norm_columnSquare_sq (a : ι → A) : ‖columnSquare a‖ ^ 2 = ‖∑ k, star (a k) * a k‖ := by
  rw [norm_columnSquare, Real.sq_sqrt (norm_nonneg _)]

/-- Squaring `‖rowSquare a‖` gives `‖∑ k, a k * star (a k)‖`. -/
theorem norm_rowSquare_sq (a : ι → A) : ‖rowSquare a‖ ^ 2 = ‖∑ k, a k * star (a k)‖ := by
  rw [norm_rowSquare, Real.sq_sqrt (norm_nonneg _)]

/-- Each entry of `a` is bounded in norm by `‖columnSquare a‖`. -/
theorem norm_apply_le_norm_columnSquare (a : ι → A) (i : ι) : ‖a i‖ ≤ ‖columnSquare a‖ := by
  rw [norm_columnSquare, ← Real.sqrt_sq (norm_nonneg (a i)), sq, ← CStarRing.norm_star_mul_self]
  exact Real.sqrt_le_sqrt <| CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (Finset.single_le_sum (fun k _ => star_mul_self_nonneg (a k)) (Finset.mem_univ i))
    (star_mul_self_nonneg (a i))

/-- Each entry of `a` is bounded in norm by `‖rowSquare a‖`. -/
theorem norm_apply_le_norm_rowSquare (a : ι → A) (i : ι) : ‖a i‖ ≤ ‖rowSquare a‖ := by
  simpa only [rowSquare_eq_columnSquare_star, norm_star] using
    norm_apply_le_norm_columnSquare (fun k => star (a k)) i

/-- `columnSquare a = 0` if and only if `a = 0`. -/
@[simp] theorem columnSquare_eq_zero_iff {a : ι → A} : columnSquare a = 0 ↔ a = 0 :=
  ⟨fun h => funext fun i => norm_le_zero_iff.mp <|
    (norm_apply_le_norm_columnSquare a i).trans_eq (by rw [h, norm_zero]),
   fun h => h ▸ columnSquare_zero⟩

/-- `rowSquare a = 0` if and only if `a = 0`. -/
@[simp] theorem rowSquare_eq_zero_iff {a : ι → A} : rowSquare a = 0 ↔ a = 0 :=
  ⟨fun h => funext fun i => norm_le_zero_iff.mp <|
    (norm_apply_le_norm_rowSquare a i).trans_eq (by rw [h, norm_zero]),
   fun h => h ▸ rowSquare_zero⟩

/-- **Operator Cauchy–Schwarz inequality** in a non-unital C⋆-algebra:
`‖∑ k, a k * b k‖ ≤ ‖rowSquare a‖ * ‖columnSquare b‖`. -/
theorem norm_sum_mul_le_norm_rowSquare_mul_norm_columnSquare (a b : ι → A) :
    ‖∑ k, a k * b k‖ ≤ ‖rowSquare a‖ * ‖columnSquare b‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    mul_pow, norm_rowSquare_sq, norm_columnSquare_sq]
  exact Finset.norm_sum_mul_sq_le Finset.univ a b

end TauCeti
