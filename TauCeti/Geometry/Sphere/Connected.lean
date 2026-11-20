/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Nonemptiness and connectedness of spheres

Unit spheres in nontrivial real normed spaces, and more generally in real seminormed spaces
with a nontrivial topology, are nonempty (`TauCeti.instNonemptySphere`), and spheres in real
normed spaces of dimension at least two are connected. In particular, the unit sphere in
`EuclideanSpace ℝ ι` is connected when `ι` has at least two elements.
`TauCeti.connectedSpace_sphere` and `TauCeti.connectedSpace_euclideanSphere` supply the
connected-space instances used by covering-space, separation and orientation arguments on spheres,
independently of their manifold structure.
-/

public section

namespace TauCeti

open Metric Module
open scoped EuclideanSpace

/-- In a real seminormed space with a nontrivial topology (for instance a nontrivial real normed
space), the unit sphere about any point is nonempty. -/
instance instNonemptySphere {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [NontrivialTopology E] (x : E) : Nonempty (sphere x 1) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- For `n ≥ 1`, the unit sphere in an `(n + 1)`-dimensional real normed space is connected. -/
theorem isConnected_sphere_of_one_le (hn : 1 ≤ n) : IsConnected (sphere (0 : E) 1) := by
  refine isConnected_sphere ?_ 0 zero_le_one
  simpa using lt_rank_of_lt_finrank (R := ℝ) (M := E) (n := 1)
    (by rw [Fact.out (p := finrank ℝ E = n + 1)]; omega)

variable (n) in
/-- For `n ≥ 1`, the unit sphere in an `(n + 1)`-dimensional real normed space is a connected
space. -/
theorem connectedSpace_sphere [NeZero n] : ConnectedSpace (sphere (0 : E) 1) :=
  Subtype.connectedSpace (isConnected_sphere_of_one_le (NeZero.one_le (n := n)))

/-- The unit sphere of `EuclideanSpace ℝ ι` is connected when `ι` has at least two elements. -/
theorem connectedSpace_euclideanSphere {ι : Type*} [Fintype ι] (hι : 1 < Fintype.card ι) :
    ConnectedSpace (sphere (0 : EuclideanSpace ℝ ι) 1) :=
  isConnected_iff_connectedSpace.1 <| isConnected_sphere (by
    rw [← finrank_eq_rank, finrank_euclideanSpace]
    exact_mod_cast hι) 0 zero_le_one

end TauCeti
