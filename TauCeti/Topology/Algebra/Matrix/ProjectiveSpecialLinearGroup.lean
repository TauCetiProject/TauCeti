/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Topology on `PSL(2, ℝ)`

The quotient topology on the projective special linear group `PSL(2, ℝ)` is Hausdorff
because the center of `SL(2, ℝ)` is finite, hence closed.
-/

public section

open scoped MatrixGroups

open Matrix.SpecialLinearGroup

namespace TauCeti

/-- The projective special linear group `PSL(2, ℝ)` is Hausdorff. -/
instance : T2Space PSL(2, ℝ) := by
  let _ : Finite (Subgroup.center SL(2, ℝ)) :=
    Matrix.SpecialLinearGroup.finite_center (R := ℝ)
  let _ : IsClosed ((Subgroup.center SL(2, ℝ) : Subgroup SL(2, ℝ)) : Set SL(2, ℝ)) :=
    Set.toFinite _ |>.isClosed
  infer_instance

end TauCeti
