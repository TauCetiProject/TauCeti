/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Analysis.Normed.Module.Connected

import Mathlib.Topology.Separation.Connected

/-!
# Nonemptiness and connectedness of spheres

The unit sphere in `EuclideanSpace ℝ ι` is nonempty whenever `ι` is finite and nonempty
(`TauCeti.instNonemptyEuclideanSphere`), and spheres in real normed spaces of dimension at least two
are connected. In particular, the unit sphere in `EuclideanSpace ℝ (Fin m)` is connected for
`m ≥ 2`. `TauCeti.connectedSpace_sphere` and `TauCeti.connectedSpace_euclideanSphere` supply the
connected-space instances used by covering-space, separation and orientation arguments on spheres,
independently of their manifold structure. Every sphere of nonzero radius in a real normed space of
rank greater than one also contains a point distinct from any given antipodal pair
(`TauCeti.exists_sphere_ne_and_ne_neg_of_one_lt_rank`, `TauCeti.exists_sphere_ne_and_ne_neg`).
-/

public section

namespace TauCeti

open Metric Module
open scoped EuclideanSpace

/-- For a nonempty finite index type `ι`, the unit sphere of `EuclideanSpace ℝ ι` is nonempty. -/
instance instNonemptyEuclideanSphere {ι : Type*} [Fintype ι] [Nonempty ι] :
    Nonempty (sphere (0 : EuclideanSpace ℝ ι) 1) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

/-- Every sphere of nonzero radius in a real normed space of rank greater than one contains a point
distinct from both `p` and `-p`. -/
theorem exists_sphere_ne_and_ne_neg_of_one_lt_rank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ} (h : 1 < Module.rank ℝ E) (hr : r ≠ 0) (p : sphere (0 : E) r) :
    ∃ q : sphere (0 : E) r, q ≠ p ∧ q ≠ -p := by
  classical
  have : PreconnectedSpace (sphere (0 : E) r) :=
    Subtype.preconnectedSpace (isPreconnected_sphere h 0 r)
  have : Nontrivial (sphere (0 : E) r) := ⟨p, -p, ne_neg_of_mem_sphere ℝ hr p⟩
  have : Infinite (sphere (0 : E) r) := PreconnectedSpace.infinite
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset ({p, -p} : Finset (sphere (0 : E) r))
  exact ⟨q, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hq⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- For `n ≥ 1`, the unit sphere in an `(n + 1)`-dimensional real normed space is connected. -/
theorem isConnected_sphere_of_one_le (hn : 1 ≤ n) : IsConnected (sphere (0 : E) 1) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  refine isConnected_sphere ?_ 0 zero_le_one
  rw [← finrank_eq_rank, Fact.out (p := finrank ℝ E = n + 1)]
  exact_mod_cast (by omega : 1 < n + 1)

variable (n) in
/-- For `n ≥ 1`, the unit sphere in an `(n + 1)`-dimensional real normed space is a connected
space. -/
theorem connectedSpace_sphere [NeZero n] : ConnectedSpace (sphere (0 : E) 1) :=
  Subtype.connectedSpace (isConnected_sphere_of_one_le (NeZero.one_le (n := n)))

variable (n) in
/-- For `n ≥ 1`, every unit sphere in an `(n + 1)`-dimensional real normed space contains a point
distinct from both `p` and `-p`. -/
theorem exists_sphere_ne_and_ne_neg [NeZero n] (p : sphere (0 : E) 1) :
    ∃ q : sphere (0 : E) 1, q ≠ p ∧ q ≠ -p := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hrank : 1 < Module.rank ℝ E := by
    rw [← finrank_eq_rank, Fact.out (p := finrank ℝ E = n + 1)]
    have := NeZero.one_le (n := n)
    exact_mod_cast (by omega : 1 < n + 1)
  exact exists_sphere_ne_and_ne_neg_of_one_lt_rank hrank one_ne_zero p

/-- The unit sphere of `ℝᵐ` is connected for `m ≥ 2`. -/
theorem connectedSpace_euclideanSphere {m : ℕ} (hm : 1 < m) :
    ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  isConnected_iff_connectedSpace.1 <| isConnected_sphere (by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hm) 0 zero_le_one

end TauCeti
