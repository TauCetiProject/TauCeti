/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.Analysis.ODE.DiracCoefficient

/-!
# Checks for Carathéodory systems: the Dirac coefficient in the maximum-row-sum norm

The Dirac coefficient `-Ω(z - Q_q(t)) = [[f, -z - g], [z - g, -f]]` (`TauCeti.diracCoeff`, with
`f = Re q(t)` and `g = Im q(t)`) has Euclidean operator norm at most `|z| + |q(t)|`
(`TauCeti.norm_toEuclideanCLM_diracCoeff_le`). In the maximum-row-sum norm of `Fin 2 → ℂ` this
bound fails: at `z = 0` the coefficient has norm `|f| + |g|`
(`TauCeti.Examples.DiracCoefficient.linfty_opNorm_diracCoeff_zero`), which exceeds `|q(t)|`
whenever `f g ≠ 0` (`TauCeti.Examples.DiracCoefficient.norm_lt_linfty_opNorm_diracCoeff_zero`).
For `q = 1 + i` the norm is `2`
(`TauCeti.Examples.DiracCoefficient.linfty_opNorm_diracCoeff_zero_one_add_I`), against
`|q| = √2`. This is why the Dirac coefficient acts on `EuclideanSpace ℂ (Fin 2)` rather than on
`Fin 2 → ℂ`.
-/

public section

open Matrix
open scoped Matrix.Norms.Operator

namespace TauCeti.Examples.DiracCoefficient

/-- At `z = 0` the Dirac coefficient has maximum-row-sum norm `|Re q(t)| + |Im q(t)|`. -/
theorem linfty_opNorm_diracCoeff_zero (q : ℝ → ℂ) (t : ℝ) :
    ‖diracCoeff q 0 t‖ = |(q t).re| + |(q t).im| := by
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [linfty_opNorm_def, huniv]
  simp [diracCoeff_def, add_comm]

/-- **The maximum-row-sum norm is too large.** If `Re q(t)` and `Im q(t)` are both nonzero, the
Dirac coefficient at `z = 0` has maximum-row-sum norm larger than `|q(t)|`. -/
theorem norm_lt_linfty_opNorm_diracCoeff_zero {q : ℝ → ℂ} {t : ℝ} (hre : (q t).re ≠ 0)
    (him : (q t).im ≠ 0) : ‖q t‖ < ‖diracCoeff q 0 t‖ := by
  rw [linfty_opNorm_diracCoeff_zero]
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  rw [Complex.sq_norm, Complex.normSq_apply, add_sq, sq_abs, sq_abs]
  have : 0 < |(q t).re| * |(q t).im| := by positivity
  nlinarith

/-- For `q = 1 + i` the Dirac coefficient at `z = 0` has maximum-row-sum norm `2`, which exceeds
`|q| = √2` by `norm_lt_linfty_opNorm_diracCoeff_zero`. -/
theorem linfty_opNorm_diracCoeff_zero_one_add_I (t : ℝ) :
    ‖diracCoeff (fun _ ↦ 1 + Complex.I) 0 t‖ = 2 := by
  rw [linfty_opNorm_diracCoeff_zero]
  norm_num

end TauCeti.Examples.DiracCoefficient
