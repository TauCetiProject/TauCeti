/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import TauCeti.Geometry.Lie.AutomaticSmoothness
import TauCeti.Geometry.Lie.Subgroup.Kernel
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The real smooth embedding of the special linear group

For an `RCLike` field `𝕜`, the special linear group `SL(n, 𝕜)` carries the real structure of its
native analytic atlas, whose charts come from the `L∞` operator norm. This file compares it with
the real `ℓ²` structure of the general linear group `GL(n, 𝕜)` and of the matrices. The inclusion
`SL(n, 𝕜) → GL(n, 𝕜)` is real smooth by automatic smoothness of continuous homomorphisms of real
Lie groups. It is injective, hence an immersion (`ContinuousMonoidHom.isImmersion_of_injective`),
so the matrix inclusion of `SL(n, 𝕜)` is a real smooth embedding for the `ℓ²` operator norm on the
matrices. This avoids comparing the two atlases directly.

To state or use these results, `open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main declarations

* `Matrix.SpecialLinearGroup.toGLContinuousMonoidHom`: the inclusion into the general linear
  group, as a continuous homomorphism.
* `Matrix.SpecialLinearGroup.contMDiff_toGL_real`: the inclusion into the general linear group is
  real smooth for its `ℓ²` structure.
* `Matrix.SpecialLinearGroup.isSmoothEmbedding_subtypeVal_real`: the matrix inclusion is a real
  smooth embedding for the `ℓ²` structure.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
-/

public section

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace Matrix.SpecialLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The inclusion of `SL(n, 𝕜)` into the general linear group, as a continuous homomorphism. -/
def toGLContinuousMonoidHom : SpecialLinearGroup n 𝕜 →ₜ* GL n 𝕜 :=
  ⟨toGL, continuous_toGL⟩

/-- The continuous inclusion into the general linear group is `SpecialLinearGroup.toGL`. -/
@[simp]
theorem coe_toGLContinuousMonoidHom :
    ⇑(toGLContinuousMonoidHom : SpecialLinearGroup n 𝕜 →ₜ* GL n 𝕜) = toGL :=
  (rfl)

/-- The inclusion of `SL(n, 𝕜)` into the general linear group is real smooth for the real
structure of the native atlas of `SL(n, 𝕜)` and the `ℓ²` structure of `GL(n, 𝕜)`, by automatic
smoothness of continuous homomorphisms of real Lie groups. -/
theorem contMDiff_toGL_real :
    ContMDiff 𝓘(ℝ, Model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
      (toGL : SpecialLinearGroup n 𝕜 → GL n 𝕜) :=
  TauCeti.Lie.contMDiff_of_continuous_monoidHom toGLContinuousMonoidHom continuous_toGL

/-- The matrix inclusion of `SL(n, 𝕜)` is a real smooth embedding for the real atlas of
`SL(n, 𝕜)` and the `ℓ²` operator norm on the matrices. The inclusion into the general linear
group is an injective continuous homomorphism of real Lie groups, hence an immersion. -/
theorem isSmoothEmbedding_subtypeVal_real :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) := by
  have h := Units.isImmersion_val_comp (ContinuousMonoidHom.isImmersion_of_injective
    (I := 𝓘(ℝ, Model n 𝕜)) (I' := 𝓘(ℝ, Matrix n n 𝕜)) toGLContinuousMonoidHom toGL_injective)
  exact ⟨h, .subtypeVal⟩

end Matrix.SpecialLinearGroup
