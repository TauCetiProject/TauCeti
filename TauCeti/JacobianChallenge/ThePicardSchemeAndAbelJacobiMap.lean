/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Roadmap: JacobianChallenge
Target: The Picard scheme and Abel-Jacobi map
<!--tauceti-target:v1
  {"focus":"JacobianChallenge","id":"JacobianChallenge.The_Picard_scheme_and_Abel_Jacobi_map"}-->
-/

public section

namespace JacobianChallenge

/-- Data for the Abel-Jacobi map from a curve to its Jacobian variety. -/
structure AbelJacobiData (Curve : Type*) where
  Jacobian : Type
  [jac_group : AddCommGroup Jacobian]
  basepoint : Curve
  abel_jacobi : Curve → Jacobian
  basepoint_maps_zero : abel_jacobi basepoint = 0

attribute [instance] AbelJacobiData.jac_group

/-- The Abel-Jacobi map sends the chosen basepoint of the curve to the origin of the Jacobian
variety. -/
theorem abel_jacobi_basepoint {Curve : Type*} (data : AbelJacobiData Curve) :
    data.abel_jacobi data.basepoint = 0 := by
  exact data.basepoint_maps_zero

end JacobianChallenge
