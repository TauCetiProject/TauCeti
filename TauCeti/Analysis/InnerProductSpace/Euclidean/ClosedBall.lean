/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Euclidean coordinates on a closed ball in a finite-dimensional subspace

A finite-dimensional subspace `V` of a real inner product space carries an orthonormal basis,
`stdOrthonormalBasis`, whose coordinate map is a linear isometry onto `EuclideanSpace ℝ (Fin n)`
for `n` the dimension of `V`. Being an isometry it carries the closed ball of `V` about the origin
onto the Euclidean closed ball of the same radius, so the two balls are homeomorphic.

The subspace is allowed to arrive as a set `s` known to equal `V`, which is how a range of a
projection presents itself, and the ball is the subtype of `s` cut out by the norm bound rather
than `Metric.closedBall` in the subtype, which is how a set truncated by a norm bound presents
itself.

## Main definitions

* `TauCeti.euclideanClosedBallHomeomorph`: the closed ball of radius `rho` in such a subspace is
  homeomorphic to the closed ball of radius `rho` in `EuclideanSpace ℝ (Fin n)`.
-/

public section

open Metric Set

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed ball of radius `rho` in a subspace `V` of `E`, presented through a set `s` equal to
that subspace, is homeomorphic to the closed ball of the same radius in the Euclidean space of the
dimension of `V`. -/
def euclideanClosedBallHomeomorph {s : Set E} {V : Submodule ℝ E} [FiniteDimensional ℝ V]
    (hs : s = (V : Set E)) {n : ℕ} (hn : Module.finrank ℝ V = n) (rho : ℝ) :
    {v : s | ‖(v : E)‖ ≤ rho} ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin n)) rho :=
  (Homeomorph.subtype (Homeomorph.setCongr hs)
      (fun _ ↦ by simp only [mem_ofPred_eq, Homeomorph.setCongr_apply])).trans
    (Homeomorph.subtype
      (p := fun v : (V : Set E) ↦ ‖(v : E)‖ ≤ rho)
      (q := fun w ↦ w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) rho)
      ((stdOrthonormalBasis ℝ V).reindex (finCongr hn)).repr.toHomeomorph
      (fun v ↦ by
        simp only [LinearIsometryEquiv.coe_toHomeomorph, mem_closedBall_zero_iff,
          LinearIsometryEquiv.norm_map, Submodule.norm_coe]))

end TauCeti

end
