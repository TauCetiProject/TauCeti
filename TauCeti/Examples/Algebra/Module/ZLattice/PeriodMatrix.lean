/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.PeriodMatrix

/-!
# Covolumes of period lattices: examples

The covolume of the lattice `ℤ^g + τ ℤ^g` in `ℂ^g` is `|det (Im τ)|`
(`ZLattice.covolume_span_normalizedPeriodBasis`). Two normalizations are checked here.

* For `τ = i · 1`, the lattice is the Gaussian lattice `ℤ[i]^g`, of covolume `1` in every
  dimension `g`, including `g = 0`.
* For `g = 1` and `τ = 2i`, the lattice `ℤ + 2i ℤ` has covolume `2`, the area of the rectangle
  with sides `1` and `2`.
-/

public section

open Matrix Submodule

namespace TauCeti.PeriodMatrixExample

/-- The imaginary part of `i · 1` is the identity matrix. -/
theorem map_im_I_smul_one {ι : Type*} [DecidableEq ι] :
    (Complex.I • (1 : Matrix ι ι ℂ)).map Complex.im = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- The imaginary part of `i · 1` is invertible. -/
theorem det_map_im_I_smul_one_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ((Complex.I • (1 : Matrix ι ι ℂ)).map Complex.im).det ≠ 0 := by
  rw [map_im_I_smul_one, det_one]
  exact one_ne_zero

/-- The Gaussian lattice `ℤ[i]^g = ℤ^g + i ℤ^g` has covolume `1`. -/
theorem covolume_gaussian {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ZLattice.covolume (span ℤ (Set.range ((Complex.I • (1 : Matrix ι ι ℂ)).normalizedPeriodBasis
      det_map_im_I_smul_one_ne_zero))) = 1 := by
  rw [ZLattice.covolume_span_normalizedPeriodBasis, map_im_I_smul_one, det_one, abs_one]

/-- The imaginary part of `τ = 2i` is invertible. -/
theorem det_map_im_two_I_ne_zero : ((of fun _ _ ↦ 2 * Complex.I : Matrix Unit Unit ℂ).map
    Complex.im).det ≠ 0 := by
  simp

/-- The lattice `ℤ + 2i ℤ` in `ℂ` has covolume `2`. -/
theorem covolume_two_I :
    ZLattice.covolume (span ℤ (Set.range
      ((of fun _ _ ↦ 2 * Complex.I : Matrix Unit Unit ℂ).normalizedPeriodBasis
        det_map_im_two_I_ne_zero))) = 2 := by
  rw [ZLattice.covolume_span_normalizedPeriodBasis]
  simp

end TauCeti.PeriodMatrixExample
