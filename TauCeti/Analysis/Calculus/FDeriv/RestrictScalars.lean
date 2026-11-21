/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The derivative under restriction of scalars

For a map differentiable over a larger field `𝕜'`, the derivative over `𝕜` is the restriction of
scalars of the derivative over `𝕜'`, so it is `𝕜'`-linear, the two derivatives have the same
range, and one is injective exactly when the other is. For a holomorphic map, the real derivative
commutes with multiplication by `I`, the real tangent space is the complex tangent space, and the
map is a real immersion at a point exactly when it is a complex one. For a holomorphic function
of one variable, the real derivative is multiplication by the complex derivative, so the two have
the same norm.

## Main results

* `DifferentiableAt.fderiv_restrictScalars_smul`: the derivative over `𝕜` is `𝕜'`-linear.
* `DifferentiableAt.fderiv_restrictScalars_eq_smul_deriv`: on the line `𝕜'`, it is
  multiplication by the derivative.
* `DifferentiableAt.norm_fderiv_restrictScalars_eq_norm_deriv`: on the line `𝕜'`, its norm is
  the norm of the derivative.
* `DifferentiableAt.range_fderiv_restrictScalars`: the range of the derivative does not depend
  on the field of scalars.
* `DifferentiableAt.injective_fderiv_restrictScalars_iff`: neither does its injectivity.
-/

public section

namespace TauCeti

variable (𝕜 : Type*) {𝕜' V E : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace 𝕜' V]
  [IsScalarTower 𝕜 𝕜' V] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {i : V → E} {x : V}

/-- The derivative over `𝕜` of a map differentiable over a larger field `𝕜'` is `𝕜'`-linear. For
a holomorphic map, the real derivative commutes with multiplication by `I`. -/
theorem _root_.DifferentiableAt.fderiv_restrictScalars_smul (hi : DifferentiableAt 𝕜' i x)
    (c : 𝕜') (u : V) : fderiv 𝕜 i x (c • u) = c • fderiv 𝕜 i x u := by
  simp [hi.fderiv_restrictScalars 𝕜]

/-- The derivative over `𝕜` of a map `f` on `𝕜'` which is differentiable over `𝕜'` sends `v` to
`v • deriv f x`. For a holomorphic `f : ℂ → E`, the real derivative at `z` sends `1` to
`deriv f z` and `I` to `I • deriv f z`. -/
theorem _root_.DifferentiableAt.fderiv_restrictScalars_eq_smul_deriv {f : 𝕜' → E} {x : 𝕜'}
    (hf : DifferentiableAt 𝕜' f x) (v : 𝕜') : fderiv 𝕜 f x v = v • deriv f x := by
  rw [hf.fderiv_restrictScalars 𝕜, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_smul_deriv]

/-- The derivative over `𝕜` of a map on `𝕜'` which is differentiable over `𝕜'` has the norm of
its derivative. For a holomorphic `f : ℂ → E`, `‖fderiv ℝ f z‖ = ‖deriv f z‖`. -/
theorem _root_.DifferentiableAt.norm_fderiv_restrictScalars_eq_norm_deriv {f : 𝕜' → E}
    {x : 𝕜'} (hf : DifferentiableAt 𝕜' f x) : ‖fderiv 𝕜 f x‖ = ‖deriv f x‖ := by
  rw [hf.fderiv_restrictScalars 𝕜, ContinuousLinearMap.norm_restrictScalars,
    norm_deriv_eq_norm_fderiv]

/-- The tangent space of a map differentiable over a larger field `𝕜'` is the same over `𝕜`. For
a holomorphic map, the real tangent space is the complex tangent space; in particular it is stable
under multiplication by `I`. -/
theorem _root_.DifferentiableAt.range_fderiv_restrictScalars (hi : DifferentiableAt 𝕜' i x) :
    (fderiv 𝕜 i x).range = (fderiv 𝕜' i x).range.restrictScalars 𝕜 := by
  rw [hi.fderiv_restrictScalars 𝕜]
  exact LinearMap.range_restrictScalars _

/-- The derivative over `𝕜` of a map differentiable over a larger field `𝕜'` is injective exactly
when its derivative over `𝕜'` is. For a holomorphic map, it is a real immersion at `x` exactly
when it is a complex immersion there. -/
theorem _root_.DifferentiableAt.injective_fderiv_restrictScalars_iff
    (hi : DifferentiableAt 𝕜' i x) :
    Function.Injective (fderiv 𝕜 i x) ↔ Function.Injective (fderiv 𝕜' i x) := by
  rw [hi.fderiv_restrictScalars 𝕜, ContinuousLinearMap.coe_restrictScalars']

end TauCeti
