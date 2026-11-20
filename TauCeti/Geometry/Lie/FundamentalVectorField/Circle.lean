/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Linear
public import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The fundamental vector fields of the circle acting on complex vector spaces

Mathlib's unit circle `Circle ⊆ ℂ` is a Lie group, and it acts smoothly on every complex normed
space `V` by scalar multiplication, `z • v = (z : ℂ) • v` (`Circle.smul_def`,
`Circle.instContMDiffSMul`). This file computes the fundamental vector fields of this action: an
element `ξ` of the Lie algebra of the circle acts on `V` by multiplication by the complex number
`ι_* ξ`, its image under the derivative at `1` of the inclusion `ι : Circle → ℂ`
(`TauCeti.fundamentalLinearMap_circle_apply`). Since the generator of the rotations
`t ↦ exp (t i)` has image `i` (`TauCeti.mvfderiv_coe_mfderiv_circleExp`), this generator acts by
`v ↦ i • v`.

These are the inputs for the moment maps of circle actions on complex vector spaces, such as the
rotations of the phase space of a planar mechanical system.

## Main results

* `TauCeti.fundamentalLinearMap_circle_apply`: the fundamental vector field of `ξ` is
  `v ↦ (ι_* ξ) • v`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V]

attribute [local instance] finrank_real_complex_fact'

namespace TauCeti

/-- **The fundamental vector fields of the circle action.** An element `ξ` of the Lie algebra of
the circle acts on a complex normed space by multiplication by its image `ι_* ξ ∈ ℂ` under the
derivative at `1` of the inclusion `ι : Circle → ℂ`. -/
theorem fundamentalLinearMap_circle_apply (ξ : GroupLieAlgebra (𝓡 1) Circle) (v : V) :
    fundamentalLinearMap (𝓡 1) Circle V ξ v =
      mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1 ξ • v := by
  -- The orbit map of `v` is the inclusion followed by the real-linear map `c ↦ c • v`.
  let L : ℂ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℂ).smulRight v
  have horbit : (fun g : Circle ↦ g • v) = L ∘ (fun z : Circle ↦ (z : ℂ)) := by
    ext g
    simp [L, Circle.smul_def]
  have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) 1 :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  rw [fundamentalLinearMap_apply, horbit,
    mvfderiv_comp_apply_of_differentiableAt L.differentiableAt hcoe, L.fderiv,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]

end TauCeti
