/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Basic

/-!
# Propagation of semigroup orbit increments

Time-shifted orbit and operator increments factor through the earlier time operator.
These identities and the operator norm estimate control how an initial increment propagates
along a strongly continuous semigroup.
-/

public section
noncomputable section
open scoped NNReal Topology

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- An orbit increment at a sum of times is the earlier operator applied to the initial
increment. -/
theorem map_add_sub_apply (S :
    StronglyContinuousSemigroup X) (s t : ℝ≥0) (x : X) :
    S (s + t) x - S s x = S s (S t x - x) := by
  rw [S.map_add_apply s t x]
  exact ((S s).map_sub _ _).symm

/-- The norm of an operator increment is bounded by the earlier operator norm times the initial
increment norm. -/
theorem norm_increment_operator_le (S :
    StronglyContinuousSemigroup X) (s t : ℝ≥0) :
    ‖S (s + t) - S s‖ ≤ ‖S s‖ * ‖S t - 1‖ := by
  have h_le : s ≤ s + t := by simp
  have h : S (s + t) - S s = (S s).comp (S t - 1) := by
    rw [S.sub_eq_comp_sub_one_of_le h_le, add_tsub_cancel_left]
  rw [h]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end TauCeti.Semigroups.StronglyContinuousSemigroup
