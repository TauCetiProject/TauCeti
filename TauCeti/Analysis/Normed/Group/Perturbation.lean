/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.LocalExtr
public import TauCeti.Algebra.Order.Field.Basic

/-!
# Bounds from quadratic perturbations

On a bounded subset of a seminormed group, upper bounds obtained at maximizers of
`f + ε‖·‖²` for every `ε > 0` give an upper bound for `f` itself. This separates the limiting
estimate from the analytic arguments that produce the maximizers.
-/

public section

/-- On a bounded set, if `f z ≤ m` at some maximizer `z` of `f + ε‖·‖²` for every positive `ε`,
then `f ≤ m` on the whole set. This limiting estimate is shared by weak maximum principles. -/
theorem Bornology.IsBounded.le_of_forall_pos_exists_isMaxOn_perturbation {E : Type*}
    [SeminormedAddGroup E] {K : Set E} (hK : Bornology.IsBounded K)
    {f : E → ℝ} {m : ℝ} {x : E} (hxK : x ∈ K)
    (H : ∀ ε : ℝ, 0 < ε → ∃ z ∈ K, IsMaxOn (fun y : E => f y + ε • ‖y‖ ^ 2) K z ∧ f z ≤ m) :
    f x ≤ m := by
  obtain ⟨M, hM⟩ := hK.exists_norm_le
  refine TauCeti.le_of_forall_pos_mul_le (C := M ^ 2) fun ε hε => ?_
  obtain ⟨z, hzK, hzmax, hfz⟩ := H ε hε
  have hxz : f x + ε * ‖x‖ ^ 2 ≤ f z + ε * ‖z‖ ^ 2 := by simpa [smul_eq_mul] using hzmax hxK
  have hzC : ‖z‖ ^ 2 ≤ M ^ 2 := by nlinarith [hM z hzK, norm_nonneg z]
  have hεzC : ε * ‖z‖ ^ 2 ≤ ε * M ^ 2 := mul_le_mul_of_nonneg_left hzC hε.le
  have hεx : 0 ≤ ε * ‖x‖ ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  linarith
