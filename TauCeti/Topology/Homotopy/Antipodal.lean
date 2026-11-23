/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
public import TauCeti.Analysis.Normed.Module.Normalize

/-!
# Maps into a sphere that are homotopic to their antipodes

Let `f : Y → S` be a continuous map into the unit sphere `S` of a real inner product space `E`,
and let `v : Y → E` be a continuous field along `f` which is orthogonal to it and vanishes nowhere:
`⟪v y, f y⟫ = 0` and `v y ≠ 0`. Then `f` is homotopic to its antipode `-f`, through the half
great circles `t ↦ cos (π t) • f y + sin (π t) • v y / ‖v y‖`
(`ContinuousMap.homotopic_neg_of_ne_zero_of_inner_eq_zero`). This normalizes `v` to a unit
normal field and applies `ContinuousMap.homotopic_neg_of_inner_eq_zero`.

For `f` the identity of `S`, the field `v` is a tangent vector field, and this is the homotopy
from the identity to the antipodal map in the proof of the hairy ball theorem. For a general
`f` the field is a section of the pullback of the tangent bundle of `S` along `f`; for instance
the second vector of a family of orthonormal two-frames is such a field along the first vector.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5, the proof of Theorem 1.
-/

public section

open Metric
open scoped InnerProductSpace

namespace ContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Y : Type*}
  [TopologicalSpace Y]

/-- **A map into a sphere with a nowhere-vanishing normal field is homotopic to its antipode.** If
`v : Y → E` is continuous, vanishes nowhere and is orthogonal to `f : Y → S` at every point, then
`f` is homotopic to `-f`, through the half great circles from `f y` to `-f y` leaving `f y` in the
direction of `v y`. -/
theorem homotopic_neg_of_ne_zero_of_inner_eq_zero {f : C(Y, sphere (0 : E) 1)} {v : Y → E}
    (hv : Continuous v) (h0 : ∀ y, v y ≠ 0) (ht : ∀ y, ⟪v y, (f y : E)⟫_ℝ = 0) :
    f.Homotopic (-f) :=
  -- The unit field `v / ‖v‖` is orthogonal to `f`.
  f.homotopic_neg_of_inner_eq_zero (TauCeti.normalizeToSphere v hv h0) fun y ↦ by
    rw [TauCeti.coe_normalizeToSphere_apply, NormedSpace.normalize, real_inner_smul_right,
      real_inner_comm, ht, mul_zero]

end ContinuousMap
