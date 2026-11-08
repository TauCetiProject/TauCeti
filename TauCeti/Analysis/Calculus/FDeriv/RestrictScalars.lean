/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# The derivative under restriction of scalars

For a map differentiable over a larger field `𝕜'`, the derivative over `𝕜` is the restriction of
scalars of the derivative over `𝕜'`, so it is `𝕜'`-linear, the two derivatives have the same
range, and one is injective exactly when the other is. For a holomorphic map, the real derivative
commutes with multiplication by `I`, the real tangent space is the complex tangent space, and the
map is a real immersion at a point exactly when it is a complex one. For a holomorphic function
of one variable, the real derivative is multiplication by the complex derivative. Precomposition
with the multiplication by a scalar `c` of the larger field is differentiated by the chain rule,
without any differentiability assumption; for instance, the real derivative of `w ↦ f (c * w)` on
`ℂ` is `v ↦ fderiv ℝ f (c * w) (c * v)`.

## Main results

* `DifferentiableAt.fderiv_restrictScalars_smul`: the derivative over `𝕜` is `𝕜'`-linear.
* `DifferentiableAt.fderiv_restrictScalars_eq_smul_deriv`: on the line `𝕜'`, it is
  multiplication by the derivative.
* `DifferentiableAt.range_fderiv_restrictScalars`: the range of the derivative does not depend
  on the field of scalars.
* `DifferentiableAt.injective_fderiv_restrictScalars_iff`: neither does its injectivity.
* `TauCeti.fderiv_comp_smul_apply`: the derivative over `𝕜` of `w ↦ f (c • w)` for `c : 𝕜'`.
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

/-- The derivative over `𝕜` of a map on `𝕜'` which is differentiable over `𝕜'` sends `v` to
`v • f'`. For a holomorphic `f : ℂ → E`, the real derivative sends `1` to `f'` and `I` to
`I • f'`. -/
theorem _root_.DifferentiableAt.fderiv_restrictScalars_eq_smul_deriv {f : 𝕜' → E} {x : 𝕜'}
    (hf : DifferentiableAt 𝕜' f x) (v : 𝕜') : fderiv 𝕜 f x v = v • deriv f x := by
  rw [hf.fderiv_restrictScalars 𝕜, ContinuousLinearMap.coe_restrictScalars', fderiv_eq_smul_deriv]

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

/-- The chain rule for precomposition with the multiplication by a scalar `c` of a larger field
`𝕜'`, which is `𝕜`-linear. No differentiability of `f` is needed. Over `𝕜 = 𝕜'` this is
`fderiv_comp_smul`; for `𝕜 = ℝ` and `𝕜' = ℂ` it differentiates `w ↦ f (c * w)` on `ℂ`. -/
theorem fderiv_comp_smul_apply {𝕜 𝕜' V F : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedSpace 𝕜' V] [IsScalarTower 𝕜 𝕜' V] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : V → F) (c : 𝕜') (x v : V) :
    fderiv 𝕜 (fun w ↦ f (c • w)) x v = fderiv 𝕜 f (c • x) (c • v) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have h := ((ContinuousLinearEquiv.smulLeft (R₁ := 𝕜') (Units.mk0 c hc)).restrictScalars 𝕜
      |>.comp_right_fderiv (f := f) (x := x))
    simpa [Function.comp_def] using congrArg (fun L ↦ L v) h

end TauCeti
