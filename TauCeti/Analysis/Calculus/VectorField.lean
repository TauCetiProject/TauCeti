/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Pulling vector fields back along open partial homeomorphisms

Mathlib's pullback `VectorField.pullback 𝕜 f X x = (Df_x)⁻¹ (X (f x))` inverts the derivative of
`f`. For an open partial homeomorphism `e` that is differentiable at a point `p` of its source,
with inverse differentiable at `e p`, this inverse is the derivative of `e.symm` at `e p`
(`OpenPartialHomeomorph.inverse_fderiv`). Hence pulling back along `e` applies `De⁻¹`, and pulling
back along `e.symm` pushes forward by `De`.

## Main results

* `OpenPartialHomeomorph.vectorFieldPullback_apply`: the pullback of `X` along `e` is
  `De⁻¹_{e p} (X (e p))` at `p`.
* `OpenPartialHomeomorph.vectorFieldPullback_symm_apply`: the pullback of `X` along `e.symm` is
  the pushforward `De_p (X p)` at `e p`.
* `VectorField.pullback_zero`, `VectorField.pullback_fun_zero`: the pullback of the zero vector
  field along any map is zero.
-/

public section

namespace VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The pullback of the zero vector field along any map is zero. -/
@[simp]
theorem pullback_zero (f : E → F) : pullback 𝕜 f 0 = 0 := by
  ext x
  simp [pullback]

/-- The pullback of the zero vector field, written as a constant function, along any map is
zero. -/
@[simp]
theorem pullback_fun_zero (f : E → F) : pullback 𝕜 f (fun _ => 0) = 0 :=
  pullback_zero f

end VectorField

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : OpenPartialHomeomorph E F)
  {p : E}

/-- Mathlib's pullback `VectorField.pullback` of a vector field `X` on `F` along `e` is, at a
point `p` of the source, `De⁻¹_{e p} (X (e p))`, with `De⁻¹` the derivative of `e.symm`. -/
theorem vectorFieldPullback_apply (X : F → F) (hp : p ∈ e.source)
    (he : DifferentiableAt 𝕜 e p) (hs : DifferentiableAt 𝕜 e.symm (e p)) :
    VectorField.pullback 𝕜 e X p = fderiv 𝕜 e.symm (e p) (X (e p)) := by
  rw [VectorField.pullback, e.inverse_fderiv hp he hs]

/-- **Pulling a vector field back along the inverse pushes it forward.** Mathlib's pullback
`VectorField.pullback` of a vector field `X` on `E` along `e.symm` is, at `e p`, the
pushforward `De_p (X p)`. -/
theorem vectorFieldPullback_symm_apply (X : E → E) (hp : p ∈ e.source)
    (he : DifferentiableAt 𝕜 e p) (hs : DifferentiableAt 𝕜 e.symm (e p)) :
    VectorField.pullback 𝕜 e.symm X (e p) = fderiv 𝕜 e p (X p) := by
  rw [e.symm.vectorFieldPullback_apply X (e.map_source hp) hs
    (by rwa [e.symm_symm, e.left_inv hp]), e.symm_symm, e.left_inv hp]

end OpenPartialHomeomorph
