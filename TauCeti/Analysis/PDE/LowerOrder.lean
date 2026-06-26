/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Lower-order pointwise forms for divergence-form PDEs

For a divergence-form operator `L u = -∂ⱼ(aⁱʲ ∂ᵢ u) + bⁱ ∂ᵢ u + c u`, the principal matrix
coefficient lives in `TauCeti.Analysis.PDE.UniformEllipticity`. This file records the two
lower-order pointwise forms:

* `u ↦ b(x) · ∇u`, the first-order drift form `driftForm (b x)`;
* `u ↦ c(x) u`, the zeroth-order mass form `massForm (c x)`.

Boundedness of the coefficients is not given its own predicate: following Mathlib, a result
that needs a bound states it inline, as `∀ x ∈ Ω, ‖b x‖ ≤ β`, and the energy-form estimates in
`TauCeti.Analysis.PDE.EnergyForm` and `TauCeti.Analysis.PDE.CoerciveEnergy` take their bounds
in that shape.

## Main declarations

* `TauCeti.PDE.driftForm`, `TauCeti.PDE.massForm`: the pointwise lower-order forms.
-/

public section

namespace TauCeti

namespace PDE

open scoped InnerProductSpace

variable {n : Type*} [Fintype n]

/-- The pointwise first-order drift form `(u, ξ) ↦ ⟪b, ξ⟫ u`. -/
noncomputable def driftForm (b : EuclideanSpace ℝ n) :
    ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ n) ℝ (innerSL ℝ b)

/-- The pointwise zeroth-order mass form `(u, v) ↦ c u v`. -/
noncomputable def massForm (c : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  c • ContinuousLinearMap.mul ℝ ℝ

/-- Applying the drift form is the scalar product with the drift coefficient times `u`. -/
@[simp]
lemma driftForm_apply (b : EuclideanSpace ℝ n) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    driftForm b u ξ = ⟪b, ξ⟫_ℝ * u := by
  rw [driftForm, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]

/-- Applying the mass form is multiplication by the mass coefficient. -/
@[simp]
lemma massForm_apply (c u v : ℝ) :
    massForm c u v = c * u * v := by
  rw [massForm, smul_apply, smul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

end PDE

end TauCeti
