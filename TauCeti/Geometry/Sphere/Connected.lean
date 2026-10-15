/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectedness of Euclidean spheres

The unit sphere in `EuclideanSpace ℝ (Fin m)` is connected for `m ≥ 2`.
`TauCeti.connectedSpace_euclideanSphere` supplies the connected-space instance used by
covering-space and separation arguments on spheres, independently of their manifold structure.
-/

public section

namespace TauCeti

open Metric
open scoped EuclideanSpace

/-- The unit sphere of `ℝᵐ` is connected for `m ≥ 2`. -/
theorem connectedSpace_euclideanSphere {m : ℕ} (hm : 1 < m) :
    ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  isConnected_iff_connectedSpace.1 <| isConnected_sphere (by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hm) 0 zero_le_one

end TauCeti
