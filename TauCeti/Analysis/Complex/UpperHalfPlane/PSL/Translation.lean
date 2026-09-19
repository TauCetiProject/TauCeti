/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo

/-!
# Projective translations of the upper half-plane

The projective upper unipotent matrix acts by real translation. This identifies conjugated
parabolic stabilizers with the translations used in cusp coordinates.
-/

public section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- The projective upper unipotent matrix acts by real translation. -/
@[simp]
theorem upperRightHom_smul (x : ℝ) (z : ℍ) : upperRightHom x • z = x +ᵥ z := by
  rw [upperRightHom_apply, pslMk_smul]
  apply UpperHalfPlane.coe_injective
  rw [coe_specialLinearGroup_apply]
  simp [Matrix.SpecialLinearGroup.transvection_coe, coe_vadd, add_comm]

end TauCeti.UpperHalfPlane
