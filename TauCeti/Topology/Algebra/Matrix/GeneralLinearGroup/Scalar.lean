/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of scalar matrices in the general linear group

The scalar matrix `Matrix.GeneralLinearGroup.scalar n u`, with the unit `u` on the diagonal,
depends continuously on `u`.

## Main results

* `Matrix.GeneralLinearGroup.continuous_scalar`: the map `scalar n : Rˣ → GL n R` is continuous.
-/

public section

namespace Matrix.GeneralLinearGroup

/-- The scalar matrix `u ↦ (u)` in `GL n R` depends continuously on the unit `u`. -/
@[continuity, fun_prop]
theorem continuous_scalar {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    [TopologicalSpace R] : Continuous (scalar n : Rˣ → GL n R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, coe_scalar, Matrix.scalar_apply]
    fun_prop
  · simp only [← map_inv, coe_scalar, Matrix.scalar_apply]
    fun_prop

end Matrix.GeneralLinearGroup
