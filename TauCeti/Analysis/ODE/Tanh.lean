/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Analysis.ODE.Caratheodory

/-!
# The linear equations `v' = ± tanh(s) v`

On a real normed space `F`, the solutions of `v' = tanh(s) v` on the whole line are the paths
`cosh(s) • x`, and the solutions of `v' = -tanh(s) v` are the paths `(cosh s)⁻¹ • x`, for
`x ∈ F`. Both classifications follow from uniqueness for linear equations with continuous
coefficients, `Continuous.eq_of_hasDerivAt_clm_apply`.

## Main declarations

* `TauCeti.eq_cosh_smul_of_hasDerivAt`: every solution of `v' = tanh(s) v` is `cosh(s) • v(0)`.
* `TauCeti.hasDerivAt_inv_cosh_smul`: the path `(cosh s)⁻¹ • x` solves `v' = -tanh(s) v`.
* `TauCeti.eq_inv_cosh_smul_of_hasDerivAt`: every solution of `v' = -tanh(s) v` is
  `(cosh s)⁻¹ • v(0)`.
-/

public section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every solution of `v' = tanh(s) v` on the line is `cosh(s) • v(0)`, by uniqueness for linear
equations. -/
theorem eq_cosh_smul_of_hasDerivAt {v : ℝ → F}
    (hv : ∀ s, HasDerivAt v (Real.tanh s • v s) s) : v = fun s ↦ Real.cosh s • v 0 := by
  have hB : Continuous fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ F :=
    Real.continuous_tanh.smul continuous_const
  refine hB.eq_of_hasDerivAt_clm_apply (fun s ↦ by simpa using hv s) (fun s ↦ ?_) (t₀ := 0)
    (by simp)
  rw [smul_apply, ContinuousLinearMap.id_apply, smul_smul,
    Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ (Real.cosh_pos s).ne']
  exact (Real.hasDerivAt_cosh s).smul_const (v 0)

/-- The path `(cosh s)⁻¹ • x` solves `v' = -tanh(s) v`. -/
theorem hasDerivAt_inv_cosh_smul (x : F) (s : ℝ) :
    HasDerivAt (fun s ↦ (Real.cosh s)⁻¹ • x) (-Real.tanh s • ((Real.cosh s)⁻¹ • x)) s := by
  simpa [smul_smul] using (Real.hasDerivAt_inv_cosh s).smul_const x

/-- Every solution of `v' = -tanh(s) v` on the line is `(cosh s)⁻¹ • v(0)`, by uniqueness for
linear equations. -/
theorem eq_inv_cosh_smul_of_hasDerivAt {v : ℝ → F}
    (hv : ∀ s, HasDerivAt v (-Real.tanh s • v s) s) : v = fun s ↦ (Real.cosh s)⁻¹ • v 0 := by
  have hB : Continuous fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ F :=
    Real.continuous_tanh.neg.smul continuous_const
  exact hB.eq_of_hasDerivAt_clm_apply (fun s ↦ by simpa using hv s)
    (fun s ↦ by simpa [smul_comm (Real.tanh s)] using hasDerivAt_inv_cosh_smul (v 0) s) (t₀ := 0)
    (by simp)

end TauCeti
