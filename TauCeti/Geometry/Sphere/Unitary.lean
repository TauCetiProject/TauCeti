/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Normed.Group.BallSphere
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The unitary group acts transitively on the unit sphere

On a Hilbert space `E` over `ℝ` or `ℂ`, unitary operators act by isometries
(`Unitary.instIsIsometricSMul`), so `unitary (E →L[𝕜] E)` acts on the unit sphere of `E` by
evaluation (`TauCeti.Sphere.instMulActionOfIsIsometricSMul`), jointly continuously
(`TauCeti.Sphere.instContinuousSMulOfIsIsometricSMul`). This file shows that this action is
transitive, by transporting the transitivity of the linear isometry group
(`LinearIsometryEquiv.isPretransitive_unitSphere`) along Mathlib's identification
`Unitary.linearIsometryEquiv` of unitary operators with linear isometry equivalences.

The point of this model of the orthogonal or unitary group is its topology: `unitary (E →L[𝕜] E)`
is a topological group, compact when `E` is finite-dimensional, so it carries normalized Haar
measure. A transitive, jointly continuous action on the sphere is what averaging over Haar-random
rotations of the sphere needs.

## Main results

* `Unitary.linearIsometryEquiv_smul_unitSphere`: on the sphere, a unitary operator and the
  corresponding linear isometry equivalence act in the same way.
* `Unitary.isPretransitive_unitSphere`: the action is transitive.
-/

public section

open Metric

namespace Unitary

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On the unit sphere, a unitary operator acts as the linear isometry equivalence
`Unitary.linearIsometryEquiv U` it corresponds to. -/
theorem linearIsometryEquiv_smul_unitSphere (U : unitary (E →L[𝕜] E)) (x : sphere (0 : E) 1) :
    linearIsometryEquiv U • x = U • x :=
  Subtype.ext <| by
    rw [TauCeti.Sphere.coe_smul_of_isIsometricSMul, LinearIsometryEquiv.coe_smul_unitSphere]
    exact congr($(coe_linearIsometryEquiv_apply U) (x : E))

/-- The unitary group of `E →L[𝕜] E` acts transitively on the unit sphere of `E`. -/
instance isPretransitive_unitSphere :
    MulAction.IsPretransitive (unitary (E →L[𝕜] E)) (sphere (0 : E) 1) where
  exists_smul_eq x y := by
    obtain ⟨e, rfl⟩ := MulAction.exists_smul_eq (E ≃ₗᵢ[𝕜] E) x y
    refine ⟨linearIsometryEquiv.symm e, ?_⟩
    rw [← linearIsometryEquiv_smul_unitSphere, MulEquiv.apply_symm_apply]

end Unitary
