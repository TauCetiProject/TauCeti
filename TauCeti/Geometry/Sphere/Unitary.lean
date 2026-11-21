/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The unitary group acting on the unit sphere

On a Hilbert space `E` over `ℝ` or `ℂ`, the unitary elements of the C⋆-algebra `E →L[𝕜] E` are
exactly the linear isometry equivalences of `E` (Mathlib's `Unitary.linearIsometryEquiv`). This
file transports the action of the linear isometry group on the unit sphere of `E`
(`LinearIsometryEquiv.instMulActionUnitSphere`) to `unitary (E →L[𝕜] E)`.

The point of this model of the orthogonal or unitary group is its topology: `unitary (E →L[𝕜] E)`
is a topological group, compact when `E` is finite-dimensional, so it carries normalized Haar
measure. The action on the sphere is transitive and jointly continuous, which is what averaging
over Haar-random rotations of the sphere needs.

## Main definitions

* `Unitary.instMulActionUnitSphere`: the unitary group of `E →L[𝕜] E` acts on the unit sphere of
  `E` by evaluation.

## Main results

* `Unitary.coe_smul_unitSphere`: the action is evaluation of the operator.
* `Unitary.isPretransitive_unitSphere`: the action is transitive.
* `Unitary.continuousSMul_unitSphere`: the action is jointly continuous.
-/

public section

open Metric

namespace Unitary

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The unitary group of `E →L[𝕜] E` acts on the unit sphere of `E` by evaluation, through the
identification `Unitary.linearIsometryEquiv` of unitary operators with linear isometry
equivalences. -/
noncomputable instance instMulActionUnitSphere :
    MulAction (unitary (E →L[𝕜] E)) (sphere (0 : E) 1) :=
  .compHom _ (linearIsometryEquiv : unitary (E →L[𝕜] E) ≃* (E ≃ₗᵢ[𝕜] E)).toMonoidHom

/-- A unitary operator acts on the unit sphere by evaluation. -/
@[simp]
theorem coe_smul_unitSphere (U : unitary (E →L[𝕜] E)) (x : sphere (0 : E) 1) :
    ((U • x : sphere (0 : E) 1) : E) = (U : E →L[𝕜] E) x := by
  rw [MulAction.compHom_smul_def, MulEquiv.coe_toMonoidHom,
    LinearIsometryEquiv.coe_smul_unitSphere]
  exact congr($(coe_linearIsometryEquiv_apply U) (x : E))

/-- The unitary group of `E →L[𝕜] E` acts transitively on the unit sphere of `E`. -/
instance isPretransitive_unitSphere :
    MulAction.IsPretransitive (unitary (E →L[𝕜] E)) (sphere (0 : E) 1) :=
  MulAction.isPretransitive_compHom (E := unitary (E →L[𝕜] E))
    (linearIsometryEquiv : unitary (E →L[𝕜] E) ≃* (E ≃ₗᵢ[𝕜] E)).surjective

/-- The action of the unitary group of `E →L[𝕜] E` on the unit sphere of `E` is jointly
continuous. -/
instance continuousSMul_unitSphere :
    ContinuousSMul (unitary (E →L[𝕜] E)) (sphere (0 : E) 1) where
  continuous_smul := continuous_induced_rng.2 <| by
    simpa only [Function.comp_def, coe_smul_unitSphere] using
      (continuous_subtypeVal.comp continuous_fst).clm_apply
        (continuous_subtypeVal.comp continuous_snd)

end Unitary
