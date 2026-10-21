/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Vanishing of the derivative of a vector-valued function

For a function `g` from a manifold to a normed space `F`, Mathlib has two derivatives at `x`:
`mfderiv I 𝓘(𝕜, F) g x`, with values in the tangent space `TangentSpace 𝓘(𝕜, F) (g x)`, and
`mvfderiv I g x`, with values in `F` itself. They differ by the identification of the tangent space
with `F`, so one vanishes exactly when the other does.

## Main results

* `TauCeti.mvfderiv_comp_apply_of_differentiableAt`: the chain rule when the outer map is
  between normed spaces.
* `mvfderiv_apply_eq_mfderiv_apply`: evaluating `mvfderiv` agrees with evaluating `mfderiv`.
* `TauCeti.mvfderiv_eq_zero_iff`: `mvfderiv I g x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0`.
* `TauCeti.mdifferentiableAt_of_mvfderiv_apply_ne_zero`: a function whose `mvfderiv` is nonzero on
  some tangent vector is differentiable there.
* `TauCeti.mfderiv_neg_eq_zero_iff`: `mfderiv I 𝓘(𝕜, F) (-g) x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0`.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The canonical model-space tangent identification preserves the underlying vector.
Use this equation explicitly: automatic simplification can change an equality's codomain
from the tangent fibre to the model, whose normed-space instances are distinct. -/
theorem _root_.NormedSpace.fromTangentSpace_apply (x : E) (v : TangentSpace 𝓘(𝕜, E) x) :
    NormedSpace.fromTangentSpace (𝕜 := 𝕜) x v = v := rfl

/-- The inverse model-space tangent identification preserves the underlying vector.
As with `fromTangentSpace_apply`, this equation is for explicit tangent/model conversions. -/
theorem _root_.NormedSpace.fromTangentSpace_symm_apply (x : E) (v : E) :
    (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm v = v := rfl

/-- For a normed vector-space target, evaluating `mvfderiv` agrees with evaluating
`mfderiv` under the canonical tangent-space identification. -/
@[simp] theorem _root_.mvfderiv_apply_eq_mfderiv_apply
    (f : M → F) (x : M) (v : TangentSpace I x) :
    mvfderiv I f x v = mfderiv I 𝓘(𝕜, F) f x v := by
  rw [mvfderiv, ContinuousLinearMap.comp_apply]
  exact NormedSpace.fromTangentSpace_apply _ _

/-- The chain rule for a vector-valued function on a manifold followed by a map between normed
spaces that is differentiable at the relevant point, evaluated on a tangent vector. -/
theorem mvfderiv_comp_apply_of_differentiableAt {g : M → F} {φ : F → F'} {x : M}
    (hφ : DifferentiableAt 𝕜 φ (g x)) (hg : MDiffAt g x) (v : TangentSpace I x) :
    mvfderiv I (φ ∘ g) x v = fderiv 𝕜 φ (g x) (mvfderiv I g x v) := by
  rw [mvfderiv_comp_apply x hφ.mdifferentiableAt hg, mvfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    NormedSpace.fromTangentSpace_apply, mvfderiv_apply_eq_mfderiv_apply]

/-- The derivative of a vector-valued function, read in the target space, vanishes exactly when
its manifold derivative does. -/
theorem mvfderiv_eq_zero_iff {g : M → F} {x : M} :
    mvfderiv I g x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [mvfderiv, h]⟩
  ext u
  simpa [mvfderiv] using congrArg (fun L ↦ L u) h

/-- A vector-valued function whose derivative does not vanish on some tangent vector is
differentiable there. -/
theorem mdifferentiableAt_of_mvfderiv_apply_ne_zero {g : M → F} {x : M} {v : TangentSpace I x}
    (h : mvfderiv I g x v ≠ 0) : MDifferentiableAt I 𝓘(𝕜, F) g x := by
  by_contra hnd
  simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hnd] at h

/-- The derivative of `-g` vanishes at `x` if and only if the derivative of `g` does. -/
@[simp]
theorem mfderiv_neg_eq_zero_iff {g : M → F} {x : M} :
    mfderiv I 𝓘(𝕜, F) (-g) x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0 := by
  rw [← mvfderiv_eq_zero_iff, mvfderiv_neg, neg_eq_zero, mvfderiv_eq_zero_iff]

end TauCeti
