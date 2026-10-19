/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectedness of spheres

Spheres in real normed spaces of dimension at least two are connected. In particular, the unit
sphere in `EuclideanSpace ℝ (Fin m)` is connected for `m ≥ 2`.
`TauCeti.connectedSpace_euclideanSphere` supplies the connected-space instance used by
covering-space and separation arguments on spheres, independently of their manifold structure.
-/

public section

namespace TauCeti

open Metric Module
open scoped EuclideanSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- For `n ≥ 1`, the unit sphere in an `(n + 1)`-dimensional real normed space is connected. -/
theorem isConnected_sphere_of_one_le (hn : 1 ≤ n) : IsConnected (sphere (0 : E) 1) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  refine isConnected_sphere ?_ 0 zero_le_one
  rw [← finrank_eq_rank, Fact.out (p := finrank ℝ E = n + 1)]
  exact_mod_cast (by omega : 1 < n + 1)

/-- The unit sphere of `ℝᵐ` is connected for `m ≥ 2`. -/
theorem connectedSpace_euclideanSphere {m : ℕ} (hm : 1 < m) :
    ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  isConnected_iff_connectedSpace.1 <| isConnected_sphere (by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hm) 0 zero_le_one

end TauCeti
