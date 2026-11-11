/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Phase

/-!
# The Maslov phase of rotated copies of `ℝⁿ`

For a nonzero complex scalar `z`, the rotated subspace `z ℝⁿ` of `ℂⁿ` is maximal totally real,
and its Maslov phase relative to `ℝⁿ` is `(z / conj z) ^ n`
(`Matrix.maslovPhase_realImage_smul_one`). This is
`TauCeti.IsMaximalTotallyReal.maslovPhase_map_lsmul` for `L = ℝⁿ`. For `z = e^{iθ}` it is
`e^{2inθ}` (`Matrix.maslovPhase_realImage_exp_smul_one`).
-/

public section

open scoped ComplexConjugate

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

open TauCeti

/-- The Maslov phase of the rotated subspace `z ℝⁿ` relative to `ℝⁿ` is `(z / conj z) ^ n`. -/
theorem maslovPhase_realImage_smul_one {z : ℂ} (hz : z ≠ 0) :
    isMaximalTotallyReal_realSubspace.maslovPhase
      (isMaximalTotallyReal_realImage_smul_one (n := n) hz) =
      (z / conj z) ^ Fintype.card n := by
  have h : (z • (1 : Matrix n n ℂ)).realImage = (realSubspace n).map
      (((LinearEquiv.smulOfNeZero ℂ (EuclideanSpace ℂ n) z hz : _ ≃ₗ[ℂ] _) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) := by
    rw [realImage_eq_map_toEuclideanCLE (by simp [hz])]
    congr 1
    ext v
    simp
  rw [isMaximalTotallyReal_realSubspace.maslovPhase_congr _
      (isMaximalTotallyReal_realSubspace.map_linearEquiv _) h,
    isMaximalTotallyReal_realSubspace.maslovPhase_map_lsmul hz, finrank_euclideanSpace]

/-- The Maslov phase of the rotated subspace `e^{iθ} ℝⁿ` relative to `ℝⁿ` is `e^{2inθ}`. -/
theorem maslovPhase_realImage_exp_smul_one (θ : ℝ) :
    isMaximalTotallyReal_realSubspace.maslovPhase
      (isMaximalTotallyReal_realImage_smul_one (n := n) (Complex.exp_ne_zero (θ * Complex.I))) =
      Complex.exp ((2 * Fintype.card n * θ : ℝ) * Complex.I) := by
  rw [maslovPhase_realImage_smul_one (Complex.exp_ne_zero _), ← Complex.exp_conj, ← Complex.exp_sub,
    ← Complex.exp_nat_mul]
  congr 1
  simp [Complex.conj_ofReal]
  ring

end Matrix
