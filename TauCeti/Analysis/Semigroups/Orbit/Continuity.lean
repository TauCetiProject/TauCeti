/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Basic
public import Mathlib.Analysis.Convex.Hull

/-! # Closed invariant sets and determination by dense orbits

This file develops the continuity consequences of the semigroup action: agreement on dense
initial vectors determines a semigroup, common fixed sets are closed, and invariant sets
have invariant closed convex hulls. The hull result needs invariance only at the time applied.
-/

public section

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Two semigroups agreeing on a dense set of initial vectors are equal. -/
theorem eq_of_orbits_eq_on_dense (S T :
    StronglyContinuousSemigroup X) {D : Set X} (hD : Dense D) (h : ∀ t : ℝ≥0, ∀ x ∈ D, S t x = T
    t x) :
    S = T := by
  ext t x
  exact congrFun (Continuous.ext_on hD (S t).continuous (T t).continuous (h t)) x

/-- The set of vectors fixed at every time is closed. -/
theorem isClosed_common_fixed_set (S :
    StronglyContinuousSemigroup X) :
    IsClosed {x : X | ∀ t : ℝ≥0, S t x = x} := by
  have h : {x : X | ∀ t : ℝ≥0, S t x = x} = ⋂ t : ℝ≥0, {x : X | S t x = x} := by
    ext x; simp
  rw [h]
  exact isClosed_iInter fun t => isClosed_eq (S t).cont continuous_id

/-- The time operator preserves the closed convex hull of any set it preserves. -/
theorem preserves_closed_convexHull (S : StronglyContinuousSemigroup X) {K : Set X}
    (t : ℝ≥0) (hK : ∀ x ∈ K, S t x ∈ K) {x : X}
    (hx : x ∈ closure (convexHull ℝ K)) :
    S t x ∈ closure (convexHull ℝ K) := by
  have hconv : MapsTo (S t) (convexHull ℝ K) (convexHull ℝ K) :=
    convexHull_min (fun y hy ↦ subset_convexHull ℝ K (hK y hy))
      ((convex_convexHull ℝ K).linear_preimage (S t).toLinearMap)
  exact hconv.closure (S t).continuous hx

end TauCeti.Semigroups.StronglyContinuousSemigroup
