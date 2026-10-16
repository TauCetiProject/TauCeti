/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic

/-!
# The operator norm as a unitarily invariant seminorm

On linear maps `A : E →ₗ[𝕜] F` out of a finite-dimensional inner product space, every linear map
is continuous, and the operator norm `‖A‖` of the continuous linear map
`LinearMap.toContinuousLinearMap A` is a seminorm on `E →ₗ[𝕜] F`. Composing with unitaries of the
source or the target does not change it, so it is a unitarily invariant seminorm. Only the source
needs to be finite-dimensional.

## Main declarations

* `TauCeti.UnitarilyInvariantSeminorm.opNorm`: the operator norm as a unitarily invariant
  seminorm on `E →ₗ[𝕜] F`.
* `TauCeti.UnitarilyInvariantSeminorm.opNorm_apply`: its value is the operator norm of the
  associated continuous linear map.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
-/

public section

namespace TauCeti.UnitarilyInvariantSeminorm

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The **operator norm** `A ↦ ‖A‖` on linear maps out of a finite-dimensional inner product
space, as a unitarily invariant seminorm. -/
noncomputable def opNorm : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := (normSeminorm 𝕜 (E →L[𝕜] F)).comp LinearMap.toContinuousLinearMap.toLinearMap
  map_linearIsometryEquiv_comp_comp' U V A := by
    have h : LinearMap.toContinuousLinearMap ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) =
        (U : F →L[𝕜] F).comp ((LinearMap.toContinuousLinearMap A).comp (V : E →L[𝕜] E)) := by
      ext; simp
    simp only [Seminorm.comp_apply, coe_normSeminorm, LinearEquiv.coe_coe, h]
    rcases subsingleton_or_nontrivial E with hE | hE
    · simp [Subsingleton.elim (LinearMap.toContinuousLinearMap A) 0]
    · simp

variable {𝕜 E F}

/-- The operator-norm seminorm evaluates to the operator norm of the associated continuous linear
map. -/
@[simp]
theorem opNorm_apply (A : E →ₗ[𝕜] F) : opNorm 𝕜 E F A = ‖LinearMap.toContinuousLinearMap A‖ :=
  (rfl)

end TauCeti.UnitarilyInvariantSeminorm
