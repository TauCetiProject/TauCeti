/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The one-point compactification of `ℝ^k` as a sphere with a prescribed basepoint

The unit sphere `S^k ⊆ ℝ^(k+1)` is homeomorphic to the one-point compactification of `ℝ^k`
(Mathlib's `onePointEquivSphereOfFinrankEq`), with `∞` going to a point of the sphere that is
determined by that construction. Composing with a linear isometry of `ℝ^(k+1)` moving this point,
which exists because the linear isometry group acts transitively on the unit sphere, sends `∞` to
any prescribed basepoint.

## Main declarations

* `TauCeti.onePointHomeomorphSphere`: `OnePoint (Fin k → ℝ) ≃ₜ S^k` sending `∞` to a basepoint.
* `TauCeti.onePointHomeomorphSphere_infty`: it sends `∞` to the prescribed basepoint.
-/

public section

noncomputable section

open Metric OnePoint

namespace TauCeti

variable (k : ℕ)

/-- Mathlib's homeomorphism of the one-point compactification of `ℝ^k` with the unit sphere
`S^k ⊆ ℝ^(k+1)`. -/
private def onePointHomeomorphSphereAux :
    OnePoint (Fin k → ℝ) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
  onePointEquivSphereOfFinrankEq (V := Fin k → ℝ) (ι := Fin (k + 1)) (by simp)

/-- The unit sphere `S^k ⊆ ℝ^(k+1)` is the one-point compactification of `ℝ^k` with `∞` at any
prescribed basepoint `s₀`: Mathlib's homeomorphism `onePointEquivSphereOfFinrankEq`, followed by a
linear isometry of `ℝ^(k+1)` moving the image of `∞` to `s₀`. -/
def onePointHomeomorphSphere (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    OnePoint (Fin k → ℝ) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
  (onePointHomeomorphSphereAux k).trans
    (LinearIsometryEquiv.unitSphereIsometryEquiv
      (MulAction.exists_smul_eq (EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (k + 1))) (onePointHomeomorphSphereAux k ∞) s₀).choose).toHomeomorph

/-- The homeomorphism sends `∞` to the prescribed basepoint. -/
@[simp]
theorem onePointHomeomorphSphere_infty (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    onePointHomeomorphSphere k s₀ ∞ = s₀ := by
  rw [onePointHomeomorphSphere, Homeomorph.trans_apply]
  exact (LinearIsometryEquiv.unitSphereIsometryEquiv_apply_eq_smul _ _).trans
    (MulAction.exists_smul_eq (EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (k + 1))) (onePointHomeomorphSphereAux k ∞) s₀).choose_spec

end TauCeti
