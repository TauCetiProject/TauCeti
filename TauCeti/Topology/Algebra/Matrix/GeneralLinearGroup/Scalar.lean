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

/-- The scalar matrix `scalar n u` in `GL n R`, with the unit `u` on the diagonal, depends
continuously on `u`. -/
@[continuity, fun_prop]
theorem continuous_scalar {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    [TopologicalSpace R] : Continuous (scalar n : Rˣ → GL n R) := by
  unfold scalar
  refine Continuous.units_map _ ?_
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  exact (show Continuous fun a : R ↦ diagonal fun _ : n ↦ a by fun_prop).congr
    fun a ↦ (Matrix.scalar_apply a).symm

end Matrix.GeneralLinearGroup
