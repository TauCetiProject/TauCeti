/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The spectrum of a block triangular matrix

Over a commutative ring, a block upper triangular matrix `fromBlocks A B 0 D` is invertible
exactly when both diagonal blocks are, because its determinant is `det A * det D`. Applied to
`algebraMap R _ x - fromBlocks A B 0 D`, this computes the spectrum.

## Main results

* `Matrix.spectrum_fromBlocks_zero₂₁`: the spectrum of `fromBlocks A B 0 D` is the union of the
  spectra of `A` and `D`. In particular the spectrum of a block diagonal matrix
  `fromBlocks A 0 0 D` is the union of the spectra of its blocks.
-/

public section

namespace Matrix

variable {R S m n : Type*} [CommSemiring R] [CommRing S] [Algebra R S] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The spectrum of a block upper triangular matrix `fromBlocks A B 0 D` over a commutative ring
is the union of the spectra of its diagonal blocks `A` and `D`. -/
theorem spectrum_fromBlocks_zero₂₁ (A : Matrix m m S) (B : Matrix m n S) (D : Matrix n n S) :
    spectrum R (fromBlocks A B 0 D) = spectrum R A ∪ spectrum R D := by
  ext x
  have h : algebraMap R (Matrix (m ⊕ n) (m ⊕ n) S) x - fromBlocks A B 0 D =
      fromBlocks (algebraMap R _ x - A) (-B) 0 (algebraMap R _ x - D) := by
    simp only [Algebra.algebraMap_eq_smul_one, ← fromBlocks_one, fromBlocks_smul, smul_zero]
    ext (i | i) (j | j) <;> simp
  simp only [spectrum.mem_iff, Set.mem_union, h, isUnit_iff_isUnit_det (fromBlocks _ _ _ _),
    det_fromBlocks_zero₂₁, IsUnit.mul_iff, not_and_or, ← isUnit_iff_isUnit_det]

end Matrix
