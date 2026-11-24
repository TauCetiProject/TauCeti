/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Basic
-- `Matrix.map_mul_intCast`: the entrywise integer cast is multiplicative on matrices.
public import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Integral matrices as rational invertible matrices

An integral `n × n` matrix of nonzero determinant is invertible over `ℚ`. This file packages that
observation as a total map `HeckeRing.GLn.ofIntMatrix n : Matrix (Fin n) (Fin n) ℤ → GL (Fin n) ℚ`,
sending a matrix of nonzero determinant to its entrywise cast and a singular matrix to `1`. The
value at singular matrices is a convention: every statement about the cast carries a
nonzero-determinant hypothesis, and consumers restrict the map to a submonoid of nonsingular
integral matrices, where it is a monoid homomorphism.

This is the form in which monoids of integral matrices, such as the monoid `Σ₀(N)` of Hecke
operators on modular symbols, act on the cusps `ℙ¹(ℚ)` and on the divisors supported on them.
On nonsingular matrices the map is inverse to `HeckeRing.GLn.intMatrix n`, which reads the
integral matrix off an element of `HeckeRing.GLn.intEntries n`. The map
`FixedDetMatrices.toGL` does the same for matrices of one fixed nonzero determinant; a monoid
such as `Σ₀(N)` mixes determinants, which is why a single map defined on all integral matrices is
needed here.

## Main definitions

* `HeckeRing.GLn.ofIntMatrix n A`: the entrywise cast of `A` when `det A ≠ 0`, and `1` otherwise.

## Main results

* `HeckeRing.GLn.coe_ofIntMatrix`, `HeckeRing.GLn.ofIntMatrix_of_det_eq_zero`: the two cases of
  the definition.
* `HeckeRing.GLn.ofIntMatrix_mul`: the map is multiplicative on nonsingular matrices.
* `HeckeRing.GLn.ofIntMatrix_coe_SL`: on `SL_n(ℤ)` it is `mapGL ℚ`.
* `HeckeRing.GLn.intMatrix_ofIntMatrix`, `HeckeRing.GLn.ofIntMatrix_intMatrix`: it is inverse to
  `HeckeRing.GLn.intMatrix n` on nonsingular matrices.
-/

public section

open Matrix Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable (n : ℕ)

/-- **An integral matrix as an invertible rational matrix.** For `det A ≠ 0` this is the entrywise
cast of `A` to `ℚ`, which is invertible there; a singular `A` is sent to `1`. Only the
nonsingular case carries meaning; `HeckeRing.GLn.ofIntMatrix_mul` shows that the map is
multiplicative there. -/
noncomputable def ofIntMatrix (A : Matrix (Fin n) (Fin n) ℤ) : GL (Fin n) ℚ :=
  if h : A.det = 0 then 1
  else .mkOfDetNeZero (A.map (Int.cast : ℤ → ℚ)) (by rwa [← Int.cast_det, Int.cast_ne_zero])

variable {n}

/-- For `det A ≠ 0`, the matrix of `ofIntMatrix n A` is the entrywise cast of `A`. -/
@[simp]
theorem coe_ofIntMatrix {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) :
    (ofIntMatrix n A : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ) := by
  simp [ofIntMatrix, hA, GeneralLinearGroup.mkOfDetNeZero]

/-- A singular integral matrix is sent to `1`. -/
@[simp]
theorem ofIntMatrix_of_det_eq_zero {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det = 0) :
    ofIntMatrix n A = 1 := by
  simp [ofIntMatrix, hA]

/-- For `det A ≠ 0`, the determinant of `ofIntMatrix n A` is the determinant of `A`. -/
theorem det_ofIntMatrix {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) :
    (ofIntMatrix n A : Matrix (Fin n) (Fin n) ℚ).det = A.det := by
  rw [coe_ofIntMatrix hA, Int.cast_det]

/-- The identity matrix is sent to `1`. -/
@[simp]
theorem ofIntMatrix_one : ofIntMatrix n 1 = 1 := by
  ext : 1
  rw [coe_ofIntMatrix (by simp), Matrix.map_one _ Int.cast_zero Int.cast_one, Units.val_one]

/-- **Multiplicativity on nonsingular matrices.** -/
theorem ofIntMatrix_mul {A B : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    ofIntMatrix n (A * B) = ofIntMatrix n A * ofIntMatrix n B := by
  ext : 1
  rw [coe_ofIntMatrix (by simpa [det_mul] using mul_ne_zero hA hB), Units.val_mul,
    coe_ofIntMatrix hA, coe_ofIntMatrix hB, Matrix.map_mul_intCast]

/-- `ofIntMatrix n` is injective on nonsingular matrices. -/
theorem ofIntMatrix_injOn :
    Set.InjOn (ofIntMatrix n) {A : Matrix (Fin n) (Fin n) ℤ | A.det ≠ 0} := fun A hA B hB h ↦
  Matrix.map_injective Int.cast_injective <| by
    simpa only [coe_ofIntMatrix hA, coe_ofIntMatrix hB] using congrArg Units.val h

/-- On `SL_n(ℤ)` the map is the inclusion `mapGL ℚ`. -/
@[simp]
theorem ofIntMatrix_coe_SL (σ : SpecialLinearGroup (Fin n) ℤ) :
    ofIntMatrix n (σ : Matrix (Fin n) (Fin n) ℤ) = mapGL ℚ σ := by
  ext : 1
  rw [coe_ofIntMatrix (by simp)]
  simp [mapGL_coe_matrix, algebraMap_int_eq]

/-- Every value of `ofIntMatrix n` has integer entries, including the value `1` at singular
matrices. -/
theorem ofIntMatrix_mem_intEntries (A : Matrix (Fin n) (Fin n) ℤ) :
    ofIntMatrix n A ∈ intEntries n := by
  by_cases hA : A.det = 0
  · rw [ofIntMatrix_of_det_eq_zero hA]
    exact (intEntries n).one_mem
  · exact (mem_intEntries n).mpr ((hasIntEntries_iff n).mpr ⟨A, coe_ofIntMatrix hA⟩)

/-- **`intMatrix` undoes `ofIntMatrix` on nonsingular matrices.** -/
theorem intMatrix_ofIntMatrix {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det ≠ 0) :
    intMatrix n ⟨ofIntMatrix n A, ofIntMatrix_mem_intEntries A⟩ = A :=
  (intMatrix_eq_iff n).mpr (coe_ofIntMatrix hA)

/-- **`ofIntMatrix` undoes `intMatrix`.** -/
@[simp]
theorem ofIntMatrix_intMatrix (g : intEntries n) : ofIntMatrix n (intMatrix n g) = g := by
  -- the determinant of `intMatrix n g` casts to that of the invertible matrix `g`
  have hdet := (GeneralLinearGroup.det (g : GL (Fin n) ℚ)).ne_zero
  rw [GeneralLinearGroup.val_det_apply, ← map_intMatrix, ← Int.cast_det, Int.cast_ne_zero] at hdet
  ext : 1
  rw [coe_ofIntMatrix hdet, map_intMatrix]

end HeckeRing.GLn
