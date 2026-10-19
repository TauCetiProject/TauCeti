/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.LinearAlgebra.ExteriorPower.Plucker

/-!
# The greatest common divisor of the maximal minors

For a matrix `A` with `m` rows and columns indexed by a finite linearly ordered type `ι`, over a
ring with a normalized gcd, `Matrix.minorGcd A` is the greatest common divisor of the `m × m`
minors of `A`, that is, of the Plücker coordinates of its rows. It is the last determinantal
divisor of `A`.

For an integer matrix `A` whose rows are linearly independent over `ℚ`, the quantity
`√det (A * Aᵀ) / minorGcd A` is the right-hand side of the Bombieri–Vaaler form of Siegel's lemma
for the integral kernel `{x : ι → ℤ | A *ᵥ x = 0}`. This file proves the arithmetic facts about it
that do not involve the kernel: the rank hypothesis is the nonvanishing of the Gram determinant,
the Gram determinant is then positive, `minorGcd A ≥ 1`, `minorGcd A ^ 2` divides the Gram
determinant, and the quotient is unchanged under `A ↦ U * A` for `U ∈ GL_m(ℤ)`. The classical
Siegel bound in the entries of `A` is not invariant under this substitution.

## Main definitions

* `Matrix.minorGcd`: the greatest common divisor of the maximal minors of a matrix.

## Main results

* `Matrix.minorGcd_mul`: multiplying on the left by a square matrix `U` multiplies the minor gcd
  by `normalize (det U)`; `Matrix.minorGcd_unit_mul` is the unimodular case.
* `Matrix.sq_minorGcd_dvd_det_mul_transpose`: the square of the minor gcd divides the Gram
  determinant of the rows.
* `Matrix.linearIndependent_rows_rat_iff`: the rows of an integer matrix are linearly independent
  over `ℚ` exactly when `det (A * Aᵀ) ≠ 0`.
* `Matrix.one_le_minorGcd`: under that hypothesis the minor gcd is at least `1`.
* `Matrix.sqrt_det_div_minorGcd_unit_mul`: the Bombieri–Vaaler quantity
  `√det (A * Aᵀ) / minorGcd A` is invariant under `A ↦ U * A` for `U ∈ GL_m(ℤ)`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorems 1 and 2 and equation (2.5).

The statements and proofs of the integer part follow Ralf Stephan's
`ArithmeticHeights/BombieriVaaler.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/09835cb23557ae5ae0cf55a9c4ab9055f5d60338/ArithmeticHeights/BombieriVaaler.lean)
(Apache 2.0).
-/

public section

open Set Set.powersetCard TauCeti

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [LinearOrder ι] {m : ℕ}

section NormalizedGCDMonoid

variable [NormalizedGCDMonoid R]

/-- The **greatest common divisor of the maximal minors** of a matrix with `m` rows: the gcd of
the Plücker coordinates of its rows, indexed by the `m`-element sets of columns. -/
def minorGcd (A : Matrix (Fin m) ι R) : R :=
  Finset.univ.gcd (plucker A.row)

theorem minorGcd_def (A : Matrix (Fin m) ι R) :
    A.minorGcd = Finset.univ.gcd (plucker A.row) := (rfl)

/-- An element divides the minor gcd exactly when it divides every maximal minor. -/
theorem dvd_minorGcd_iff {A : Matrix (Fin m) ι R} {d : R} :
    d ∣ A.minorGcd ↔ ∀ s, d ∣ plucker A.row s := by
  simp [minorGcd_def, Finset.dvd_gcd_iff]

/-- The minor gcd divides every maximal minor. -/
theorem minorGcd_dvd_plucker (A : Matrix (Fin m) ι R) (s : powersetCard ι m) :
    A.minorGcd ∣ plucker A.row s :=
  Finset.gcd_dvd (Finset.mem_univ s)

@[simp]
theorem normalize_minorGcd (A : Matrix (Fin m) ι R) : normalize A.minorGcd = A.minorGcd :=
  Finset.normalize_gcd

/-- The minor gcd vanishes exactly when every maximal minor vanishes. -/
theorem minorGcd_eq_zero_iff {A : Matrix (Fin m) ι R} : A.minorGcd = 0 ↔ plucker A.row = 0 := by
  simp [minorGcd_def, Finset.gcd_eq_zero_iff, funext_iff]

/-- A matrix with no rows has the empty minor `1` as its only maximal minor. -/
@[simp]
theorem minorGcd_fin_zero (A : Matrix (Fin 0) ι R) : A.minorGcd = 1 := by
  have huniv : (Finset.univ : Finset (powersetCard ι 0)) =
      {ofCard (Finset.card_empty (α := ι))} :=
    Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, fun s _ ↦
      Subtype.ext (Finset.card_eq_zero.1 (mem_iff.1 s.2))⟩
  simp [minorGcd_def, huniv]

/-- The maximal minors of a single row are its entries, so its minor gcd is the gcd of its
entries. -/
theorem minorGcd_fin_one (A : Matrix (Fin 1) ι R) : A.minorGcd = Finset.univ.gcd (A 0) := by
  classical
  have huniv : (Finset.univ : Finset (powersetCard ι 1)) = Finset.univ.image ofSingleton :=
    (Finset.image_univ_of_surjective ofSingleton.surjective).symm
  rw [minorGcd_def, huniv, Finset.gcd_image]
  congr 1
  ext i
  rw [Function.comp_apply, plucker_ofSingleton, row_apply]

/-- The square of the minor gcd divides the Gram determinant of the rows, which is the sum of the
squares of the maximal minors. -/
theorem sq_minorGcd_dvd_det_mul_transpose (A : Matrix (Fin m) ι R) :
    A.minorGcd ^ 2 ∣ (A * Aᵀ).det := by
  rw [det_mul_transpose_self_eq_sum_sq]
  exact Finset.dvd_sum fun s _ ↦ pow_dvd_pow_of_dvd (minorGcd_dvd_plucker A s) 2

end NormalizedGCDMonoid

section StrongNormalizedGCDMonoid

variable [StrongNormalizedGCDMonoid R]

/-- Multiplying a matrix on the left by a square matrix `U` multiplies its minor gcd by the
normalization of `det U`. -/
theorem minorGcd_mul (U : Matrix (Fin m) (Fin m) R) (A : Matrix (Fin m) ι R) :
    (U * A).minorGcd = normalize U.det * A.minorGcd := by
  rw [minorGcd_def, minorGcd_def, funext (plucker_row_mul U A)]
  exact Finset.gcd_mul_left

/-- A row operation with unit determinant does not change the minor gcd. -/
theorem minorGcd_unit_mul {U : Matrix (Fin m) (Fin m) R} (hU : IsUnit U.det)
    (A : Matrix (Fin m) ι R) : (U * A).minorGcd = A.minorGcd := by
  rw [minorGcd_mul, normalize_eq_one.2 hU, one_mul]

end StrongNormalizedGCDMonoid

/-! ### Integer matrices -/

section Int

/-- The minor gcd of an integer matrix is nonnegative. -/
theorem minorGcd_nonneg (A : Matrix (Fin m) ι ℤ) : 0 ≤ A.minorGcd := by
  rw [← normalize_minorGcd, ← Int.abs_eq_normalize]
  exact abs_nonneg _

/-- **The rank hypothesis is a condition on the integer matrix alone**: the rows of an integer
matrix are linearly independent over `ℚ` exactly when their Gram determinant is nonzero. -/
theorem linearIndependent_rows_rat_iff (A : Matrix (Fin m) ι ℤ) :
    LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row ↔ (A * Aᵀ).det ≠ 0 := by
  have h : (A.map ((↑) : ℤ → ℚ) * (A.map ((↑) : ℤ → ℚ))ᵀ).det = ((A * Aᵀ).det : ℚ) := by
    rw [Int.cast_det, ← transpose_map, ← Int.coe_castRingHom, Matrix.map_mul]
    simp only [Int.coe_castRingHom]
  rw [← det_mul_transpose_self_ne_zero_iff, h, Int.cast_ne_zero]

/-- The Gram determinant of the rows of an integer matrix of rank equal to its number of rows is
positive. -/
theorem det_mul_transpose_self_pos {A : Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 0 < (A * Aᵀ).det :=
  (det_mul_transpose_self_nonneg A).lt_of_ne' ((linearIndependent_rows_rat_iff A).1 hA)

/-- The minor gcd of an integer matrix whose rows are linearly independent over `ℚ` is at least
`1`. -/
theorem one_le_minorGcd {A : Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 1 ≤ A.minorGcd := by
  have h0 : A.minorGcd ≠ 0 := by
    rw [ne_eq, minorGcd_eq_zero_iff, ← det_mul_transpose_self_eq_zero_iff]
    exact (linearIndependent_rows_rat_iff A).1 hA
  have := A.minorGcd_nonneg
  omega

/-- The square of the minor gcd of an integer matrix is at most the Gram determinant of its rows.
-/
theorem sq_minorGcd_le_det_mul_transpose (A : Matrix (Fin m) ι ℤ) :
    A.minorGcd ^ 2 ≤ (A * Aᵀ).det := by
  rcases (det_mul_transpose_self_nonneg A).lt_or_eq with h | h
  · exact Int.le_of_dvd h A.sq_minorGcd_dvd_det_mul_transpose
  · rw [← h, minorGcd_eq_zero_iff.2 ((det_mul_transpose_self_eq_zero_iff A).1 h.symm)]
    simp

omit [LinearOrder ι] in
/-- A row operation with determinant `±1` does not change the Gram determinant of the rows. -/
theorem det_mul_transpose_self_unit_mul {U : Matrix (Fin m) (Fin m) ℤ} (hU : IsUnit U.det)
    (A : Matrix (Fin m) ι ℤ) : ((U * A) * (U * A)ᵀ).det = (A * Aᵀ).det := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A, ← Matrix.mul_assoc, det_mul,
    det_mul, det_transpose, mul_right_comm, ← sq, Int.isUnit_sq hU, one_mul]

/-- **The invariance of the Bombieri–Vaaler bound** (Bombieri–Vaaler (2.5)): the quantity
`√det (A * Aᵀ) / minorGcd A` is unchanged by `A ↦ U * A` for `U ∈ GL_m(ℤ)`. -/
theorem sqrt_det_div_minorGcd_unit_mul {U : Matrix (Fin m) (Fin m) ℤ} (hU : IsUnit U.det)
    (A : Matrix (Fin m) ι ℤ) :
    Real.sqrt (((U * A) * (U * A)ᵀ).det : ℝ) / ((U * A).minorGcd : ℝ) =
      Real.sqrt ((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) := by
  rw [det_mul_transpose_self_unit_mul hU, minorGcd_unit_mul hU]

end Int

end Matrix
