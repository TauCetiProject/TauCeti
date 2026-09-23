/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Orbit
public import TauCeti.Topology.Algebra.CliffordAlgebra.RealForm
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The compact real Spin unit level as a Euclidean sphere

The positive-definite quadratic form defining the compact real Spin group is the squared
Euclidean norm in Euclidean coordinates. This file packages the resulting homeomorphism between
the Spin action's unit level and the standard Euclidean unit sphere, together with the first
topological consumer needed by the compact sphere-bundle construction.

## Main declarations

* `CliffordAlgebra.realCliffordUnitLevelHomeomorphSphere` identifies the unit level with the
  Euclidean unit sphere through `EuclideanSpace.equiv`.
* `CliffordAlgebra.pathConnectedSpace_realCliffordUnitLevel_add_two` transfers the standard
  path-connectedness theorem for spheres to the unit level in dimensions at least two.

-/

public section

namespace CliffordAlgebra

open Metric TauCeti

noncomputable section

/-- The compact real Spin unit level is homeomorphic to the Euclidean unit sphere. -/
def realCliffordUnitLevelHomeomorphSphere (n : ℕ) :
    realCliffordUnitLevel n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.subtype fun v => by
    rw [mem_realCliffordUnitLevel, mem_sphere, dist_zero_right]
    constructor
    · exact norm_euclideanSpaceEquiv_symm_eq_one_of_realCliffordForm_zero_eq_one
    · intro hv
      change ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ = 1 at hv
      calc
        realCliffordForm n 0 v =
            ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ ^ 2 := by
          simpa only [ContinuousLinearEquiv.apply_symm_apply] using
            realCliffordForm_zero_euclideanSpaceEquiv_eq_norm_sq
              ((EuclideanSpace.equiv (Fin n) ℝ).symm v)
        _ = 1 := by rw [hv]; norm_num

/-- The forward map of `realCliffordUnitLevelHomeomorphSphere` is Euclidean coordinate
conversion. -/
@[simp]
theorem coe_realCliffordUnitLevelHomeomorphSphere_apply (n : ℕ)
    (x : realCliffordUnitLevel n) :
    (realCliffordUnitLevelHomeomorphSphere n x : EuclideanSpace ℝ (Fin n)) =
      (EuclideanSpace.equiv (Fin n) ℝ).symm x.1 :=
  (rfl)

/-- The inverse map of `realCliffordUnitLevelHomeomorphSphere` returns function coordinates. -/
@[simp]
theorem coe_realCliffordUnitLevelHomeomorphSphere_symm_apply (n : ℕ)
    (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ((realCliffordUnitLevelHomeomorphSphere n).symm u : Fin n → ℝ) =
      EuclideanSpace.equiv (Fin n) ℝ u :=
  (rfl)

/-- The compact real Spin unit level is path-connected in dimensions at least two. -/
theorem pathConnectedSpace_realCliffordUnitLevel_add_two (n : ℕ) :
    PathConnectedSpace (realCliffordUnitLevel (n + 2)) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  let _ : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin (n + 2))) zero_le_one)
  exact (realCliffordUnitLevelHomeomorphSphere (n + 2)).symm.pathConnectedSpace

end

end CliffordAlgebra
