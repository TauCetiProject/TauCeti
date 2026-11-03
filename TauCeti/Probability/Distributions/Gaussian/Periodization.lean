/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum

/-!
# Periodizing the real Gaussian density

Summing the Gaussian density with mean `m` and variance `v ≠ 0` over the translates `x + k • T`
of a point by a nonzero period `T` gives a rescaled Gaussian lattice sum:

`∑ k : ℤ, gaussianPDFReal m v (x + k • T) = (√(2 * π * v))⁻¹ * Z((m - x) / T, √v / T)`,

where `Z` is `Real.gaussianLatticeSum`. At variance zero every term vanishes, so the periodized
density is summable at every variance.
-/

public section

open ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

/-- Periodizing a Gaussian density with nonzero variance gives a rescaled Gaussian lattice sum. -/
theorem hasSum_gaussianPDFReal_add_zsmul (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {T : ℝ} (hT : T ≠ 0)
    (x : ℝ) :
    HasSum (fun k : ℤ ↦ gaussianPDFReal m v (x + k • T))
      ((√(2 * π * v))⁻¹ * gaussianLatticeSum ((m - x) / T) (√(v : ℝ) / T)) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : √(v : ℝ) / T ≠ 0 := div_ne_zero (sqrt_ne_zero'.mpr hv') hT
  refine ((hasSum_gaussianLatticeSum _ hs).mul_left (√(2 * π * v))⁻¹).congr_fun fun k ↦ ?_
  rw [gaussianPDFReal]
  congr 2
  rw [div_pow, sq_sqrt hv'.le, zsmul_eq_mul]
  field_simp
  ring

/-- The translates of a point by the multiples of a nonzero period give a summable family of
Gaussian densities, at every variance. -/
theorem summable_gaussianPDFReal_add_zsmul (m : ℝ) (v : ℝ≥0) {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    Summable fun k : ℤ ↦ gaussianPDFReal m v (x + k • T) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  exact (hasSum_gaussianPDFReal_add_zsmul m hv hT x).summable

end TauCeti.Probability
