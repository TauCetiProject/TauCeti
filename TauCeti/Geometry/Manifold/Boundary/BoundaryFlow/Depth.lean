/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import Mathlib.Geometry.Manifold.ContMDiffMap
import TauCeti.Geometry.Manifold.ContMDiffMap.Radius

/-!
# A smooth depth inside a neighbourhood of the boundary zero section

A neighbourhood `U` of every `(x, 0)` in `∂M × ℝ` contains `[0, δ x]` in each fibre for a
positive smooth depth `δ`, chosen below `1`. In the collar construction, `U` simultaneously
encodes the flow domain and local invertibility of the flow-out. Taking `U` as input preserves
the caller's chosen flow and allows any additional open condition along the zero section.

The construction restricts `TauCeti.exists_contMDiffMap_closedBall_subset` to nonnegative times;
the boundary is sigma-compact as a closed subset of the ambient manifold.

## Main results

* `TauCeti.exists_contMDiffMap_depth_boundary`: a positive smooth depth whose closed forward
  intervals lie in a prescribed neighbourhood of the boundary zero section.
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- A neighbourhood of the boundary zero section contains the fibrewise closed intervals of a
positive smooth depth, bounded above by `1`. -/
theorem exists_contMDiffMap_depth_boundary
    {U : Set (ModelWithCorners.boundary (I := 𝓡∂ (n + 1)) M × ℝ)}
    (hU : ∀ x, U ∈ 𝓝 (x, (0 : ℝ))) :
    ∃ δ : (let := isManifold_boundary (n := n) (k := ∞) M;
        C^∞⟮𝓡 n, (𝓡∂ (n + 1)).boundary M; 𝓘(ℝ), ℝ⟯),
      (∀ x, 0 < δ x) ∧ (∀ x, δ x < 1) ∧ ∀ x, ∀ t ∈ Icc 0 (δ x), (x, t) ∈ U := by
  let := isManifold_boundary (n := n) (k := ∞) M
  let : SigmaCompactSpace ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary (by simp : (∞ : ℕ∞ω) ≠ 0)).sigmaCompactSpace
  obtain ⟨δ, hδ, hδ₁, hδU⟩ := exists_contMDiffMap_closedBall_subset (I := 𝓡 n) hU
    (ε := fun _ ↦ 1) lowerSemicontinuous_const (fun _ ↦ one_pos)
  refine ⟨δ, hδ, hδ₁, fun x t ht ↦ hδU x t ?_⟩
  simpa [Real.dist_eq, abs_of_nonneg ht.1] using ht.2

end TauCeti
