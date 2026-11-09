/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The derivative of the units inclusion

The inclusion of the units of a complete normed algebra has identity derivative in their native
open-submanifold charts, at every unit.

## Main results

* `Units.mvfderiv_val`: the vector-valued derivative of the units inclusion is the identity.

## References

* `Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra`, for the open-submanifold charts.
* `Mathlib.Geometry.Manifold.MFDeriv.Atlas`, for `mfderiv_extChartAt_self`.
-/

public section

open scoped Manifold

namespace Units

variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

/-- The derivative of the units inclusion is the identity in the ambient algebra coordinates. -/
@[simp]
theorem mvfderiv_val (u : Rˣ) :
    mvfderiv 𝓘(𝕜, R) (val : Rˣ → R) u = ContinuousLinearMap.id 𝕜 R := by
  have hc : (extChartAt 𝓘(𝕜, R) u) = (val : Rˣ → R) := by
    funext g
    simp only [extChartAt_coe, Function.comp_apply, Units.chartAt_apply,
      modelWithCornersSelf_coe, id_eq]
  ext v
  rw [mvfderiv_apply_eq_mfderiv_apply, ← hc, mfderiv_extChartAt_self]
  exact ContinuousLinearMap.id_apply v

end Units
