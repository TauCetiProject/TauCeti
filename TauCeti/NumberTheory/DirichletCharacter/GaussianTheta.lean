/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.LSeries.GaussianTheta.Basic
import TauCeti.NumberTheory.DirichletCharacter.PartialSum

/-!
# Small-scale bounds for Dirichlet theta series

For a nonprincipal character, cancellation over each period bounds the unnormalized Gaussian
sum by the modulus, uniformly in the scale. In the square-root normalization this
controls the series at zero, where the absolute termwise estimate would grow as `1 / √u`.
The result applies to imprimitive characters and either Gaussian parity.

## References

* The small-scale bound used in `New.norm_gaussianTheta_char_le` in
  `grh/src/Lib/Analytic/DirichletTheta.lean` of <https://github.com/lsernau/grh-lean>, revision
  `72fead102f663d5c7a407964a13dc0cf9d977207`. Here the bound follows from Abel summation rather
  than Poisson summation.
-/

public section

open Real

namespace DirichletCharacter

open TauCeti

/-- The unnormalized Gaussian theta sum of a nonprincipal character is bounded by its modulus
at every real scale, without a primitivity or parity-matching hypothesis. -/
theorem norm_gaussianTheta_le_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (j : Fin 2) (u : ℝ) :
    ‖gaussianTheta j (fun n ↦ χ n) u‖ ≤ N :=
  norm_gaussianTheta_le_of_norm_sum_le (χ.norm_sum_Icc_le_level hχ) j u

/-- A nonprincipal character's square-root-normalized Gaussian theta series is bounded by
`N √u`. At nonpositive scales the square-root normalization makes the series vanish. -/
theorem norm_gaussianThetaSeries_le_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (j : Fin 2) (u : ℝ) :
    ‖gaussianThetaSeries j (fun n ↦ χ n) u‖ ≤ (N : ℝ) * √u := by
  rw [gaussianThetaSeries_def, norm_mul, Complex.norm_real,
    norm_of_nonneg (sqrt_nonneg u), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (χ.norm_gaussianTheta_le_of_ne_one hχ j u) (sqrt_nonneg u)

end DirichletCharacter
