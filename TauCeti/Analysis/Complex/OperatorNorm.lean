/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Bounds for real-linear maps out of the complex line

The values on `1` and `I` determine a continuous real-linear map on every complex vector
(`ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I`).
A real-linear map is the sum of its values at `1` and `I` weighted by the real and imaginary
parts (`ContinuousLinearMap.eq_reCLM_smulRight_add_imCLM_smulRight`, and for families
`ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM`).

The norm bounds in terms of the values on `1` and `I` hold over any `RCLike` field and live in
`TauCeti.Analysis.RCLike.OperatorNorm`.
-/

public section

namespace ContinuousLinearMap

/-- A continuous real-linear map out of the complex plane is evaluated in the real basis
`(1,I)`. -/
theorem apply_eq_re_smul_one_add_im_smul_I {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] (L : ℂ →L[ℝ] F) (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I :=
  L.toLinearMap.apply_eq_re_smul_one_add_im_smul_I z

/-- A real-linear map out of `ℂ` is determined by its values at `1` and `I`:
`L = re ⬝ L 1 + im ⬝ L I`. -/
theorem eq_reCLM_smulRight_add_imCLM_smulRight {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℂ →L[ℝ] V) :
    L = Complex.reCLM.smulRight (L 1) + Complex.imCLM.smulRight (L Complex.I) := by
  ext z
  simp [L.apply_eq_re_smul_one_add_im_smul_I z]

/-- A family of real-linear maps out of `ℂ` splits through its values at `1` and `I`, written
with the continuous linear maps `smulRightL` so that it can be postcomposed in families. -/
theorem fun_eq_smulRightL_reCLM_add_smulRightL_imCLM {X V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (D : X → ℂ →L[ℝ] V) :
    D = (fun x => smulRightL ℝ ℂ V Complex.reCLM (D x 1)) +
      fun x => smulRightL ℝ ℂ V Complex.imCLM (D x Complex.I) := by
  funext x
  conv_lhs => rw [(D x).eq_reCLM_smulRight_add_imCLM_smulRight]
  ext z
  simp

end ContinuousLinearMap

end
