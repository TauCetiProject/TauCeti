/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Basic
public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic
import TauCeti.NumberTheory.Height.FamilyOverPairs.ProductFormula

/-!
# The product formula for covolume bounds

A `PrimePadicIso.HeightLe` bound on a nonzero Gram determinant gives a lower bound on any
uniform logarithmic squared-covolume budget. For a completed family, the price of the appended
columns is the sum of their individual logarithmic squared-length bounds. This lets a height
bound on the completed determinant control the covolume of the original block.

This is the product-formula step of `New.TwistedLattice.covolume_add_index_nonneg` in
[`New/Reduction/Lattices/TwistedLattice.lean`][short-proof] of lsernau/grh-lean.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Lattices/TwistedLattice.lean
-/

public section

open scoped ComplexOrder

namespace Matrix.CovolumeLE

open TauCeti.PrimePadicIso

/-- The sum of a logarithmic squared-covolume budget and a height budget for the same nonzero
Gram determinant is nonnegative. The metric need only be positive semidefinite. -/
theorem add_height_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {G : Matrix m m ℚ} {A : Matrix m n ℂ} {c h : ℝ} (hA : A.CovolumeLE G c)
    (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef)
    (hdet : (Aᴴ * G.map (algebraMap ℚ ℂ) * A).det ≠ 0)
    (hheight : HeightLe (fun _ ↦ (Aᴴ * G.map (algebraMap ℚ ℂ) * A).det) h) :
    0 ≤ c + h :=
  neg_le_iff_add_nonneg.mp
    (hheight.neg_le_of_norm_map_le hdet (hA.norm_map_det_conjTranspose_mul_mul_le hG))

/-- Bound the logarithmic squared-covolume budget of the first block from below using a height
bound on the nonzero Gram determinant of the completed family. The extra cost is the sum of the
individual logarithmic squared-length budgets for the appended columns. -/
theorem add_sum_add_height_nonneg {m n p : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] {G : Matrix m m ℚ} {A : Matrix m n ℂ} {B : Matrix m p ℂ}
    {c h : ℝ} {b : p → ℝ} (hA : A.CovolumeLE G c)
    (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef)
    (hB : ∀ (σ : ℂ ≃+* ℂ) j,
      ‖((B.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * B.map σ) j j‖ ≤ Real.exp (b j))
    (hdet : ((Matrix.fromCols A B)ᴴ * G.map (algebraMap ℚ ℂ) * Matrix.fromCols A B).det ≠ 0)
    (hheight : HeightLe
      (fun _ ↦ ((Matrix.fromCols A B)ᴴ * G.map (algebraMap ℚ ℂ) * Matrix.fromCols A B).det) h) :
    0 ≤ c + (∑ j, b j) + h :=
  (hA.fromCols (covolumeLE_sum_of_forall_norm_diag_le hG hB) hG).add_height_nonneg hG hdet hheight

end Matrix.CovolumeLE
