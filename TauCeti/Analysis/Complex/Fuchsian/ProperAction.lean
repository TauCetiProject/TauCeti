/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# Properly discontinuous actions of Fuchsian groups

Every discrete subgroup of `PSL(2, ℝ)` acts properly discontinuously on the upper half-plane,
as a consequence of the proper projective action constructed in
`TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction`.

This supplies the proper-discontinuity input needed to construct Hausdorff orbit quotients and
to control stabilizers of Fuchsian groups.
-/

public section

noncomputable section

open scoped MatrixGroups

open UpperHalfPlane

namespace TauCeti

/-- Every discrete subgroup of `PSL(2, ℝ)` acts properly discontinuously on the upper
half-plane. -/
instance (G : Subgroup PSL(2, ℝ)) [DiscreteTopology G] : ProperlyDiscontinuousSMul G ℍ := by
  have : IsClosed (G : Set PSL(2, ℝ)) := Subgroup.isClosed_of_discrete
  rw [properlyDiscontinuousSMul_iff_properSMul]
  infer_instance

end TauCeti
