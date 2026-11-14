/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Calculus.FDeriv.Smul

/-!
# Scalar multiplication at a zero of the scalar factor

`HasDerivWithinAt.smul_of_eq_zero` and `HasDerivAt.smul_of_eq_zero` differentiate a scalar
multiple at a zero of the scalar factor assuming only continuity of the vector factor. The
scalar factor may take values in a normed algebra over the parameter field.
-/

public section

variable {𝕜 𝕜' F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [Module 𝕜' F] [IsBoundedSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- At a zero of a differentiable scalar factor, the vector factor need only be continuous
within the parameter set to differentiate their scalar multiple. -/
theorem HasDerivWithinAt.smul_of_eq_zero {c : 𝕜 → 𝕜'} {c' : 𝕜'} {f : 𝕜 → F}
    {s : Set 𝕜} {x : 𝕜} (hc : HasDerivWithinAt c c' s x)
    (hf : ContinuousWithinAt f s x) (hc0 : c x = 0) :
    HasDerivWithinAt (fun y ↦ c y • f y) (c' • f x) s x := by
  simpa using (hc.hasFDerivWithinAt.smul_of_eq_zero hf hc0).hasDerivWithinAt

/-- At a zero of a differentiable scalar factor, the vector factor need only be continuous
to differentiate their scalar multiple. -/
theorem HasDerivAt.smul_of_eq_zero {c : 𝕜 → 𝕜'} {c' : 𝕜'} {f : 𝕜 → F}
    {x : 𝕜} (hc : HasDerivAt c c' x) (hf : ContinuousAt f x) (hc0 : c x = 0) :
    HasDerivAt (fun y ↦ c y • f y) (c' • f x) x := by
  simpa using (hc.hasFDerivAt.smul_of_eq_zero hf hc0).hasDerivAt
