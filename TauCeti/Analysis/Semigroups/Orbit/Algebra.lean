/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Orbit.Estimates

/-! # Orbit estimates and fixed vectors of semigroups

This file develops orbit increments, fixed-vector algebra, and norm estimates at nonnegative
times. The contraction subclass also preserves norms before an orbit returns to its start.
-/

public section

noncomputable section

open scoped NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace StronglyContinuousSemigroup

/-- Operators at two times commute on every vector. -/
theorem apply_comm (S :
    StronglyContinuousSemigroup X) (s t : ℝ≥0) (x : X) :
    S s (S t x) = S t (S s x) := by
  rw [← S.map_add_apply s t x, ← S.map_add_apply t s x, add_comm]

/-- Powers of two operators in the same semigroup commute. -/
theorem commute_powers (S :
    StronglyContinuousSemigroup X) (s t : ℝ≥0) (m n : ℕ) :
    Commute ((S s) ^ m) ((S t) ^ n) := by
  refine Commute.pow_pow ?_ m n
  have h : S (s + t) = S (t + s) := congrArg S (add_comm s t)
  rw [S.map_add, S.map_add] at h
  exact h

/-- A time operator is surjective when another time operator is its right inverse. -/
theorem surjective_of_right_inverse_time (S :
    StronglyContinuousSemigroup X) (s t : ℝ≥0) (h : S (s + t) = 1) :
    Function.Surjective (S t) := by
  have hcomp : (S t).comp (S s) = 1 := by
    rw [← S.map_add t s, add_comm t s, h]
  intro y
  exact ⟨S s y, by
    rw [← ContinuousLinearMap.comp_apply, hcomp]
    exact one_apply_eq_self y⟩

/-- The norm bound controls the separation of two orbits at a fixed time. -/
theorem norm_orbit_sub_le (S :
    StronglyContinuousSemigroup X) (t : ℝ≥0) (x y : X) :
    ‖S t x - S t y‖ ≤ ‖S t‖ * ‖x - y‖ := by
  simpa [map_sub] using (S t).le_opNorm (x - y)

/-- An orbit increment after a starting time is bounded by its operator norm. -/
theorem norm_increment_le (S :
    StronglyContinuousSemigroup X) (s t : ℝ≥0) (x : X) :
    ‖S (s + t) x - S s x‖ ≤ ‖S s‖ * ‖S t x - x‖ := by
  rw [S.map_add_sub_apply]
  exact (S s).le_opNorm _

/-- An orbit increment between ordered times is bounded through the earlier operator. -/
theorem norm_increment_le_of_le (S :
    StronglyContinuousSemigroup X) {s t : ℝ≥0} (h : s ≤ t) (x : X) :
    ‖S t x - S s x‖ ≤ ‖S s‖ * ‖S (t - s) x - x‖ := by
  have h_eq := S.sub_eq_comp_sub_one_of_le h
  have h_pt : S t x - S s x = S s (S (t - s) x - x) := by
    have := congrArg (fun f => f x) h_eq
    simpa [sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self] using this
  rw [h_pt]
  exact ContinuousLinearMap.le_opNorm _ _

/-- A linear combination of vectors fixed at one time is fixed at that time. -/
theorem fixed_linear_combination (S :
    StronglyContinuousSemigroup X) {t : ℝ≥0} {x y : X} (hx : S t x = x) (hy : S t y = y) (a b :
    ℝ) :
    S t (a • x + b • y) = a • x + b • y := by
  rw [(S t).map_add, (S t).map_smul, (S t).map_smul, hx, hy]

/-- A vector fixed at two times is fixed at their sum. -/
theorem fixed_add (S :
    StronglyContinuousSemigroup X) {s t : ℝ≥0} {x : X} (hs : S s x = x) (ht : S t x = x) :
    S (s + t) x = x := by
  rw [S.map_add_apply]
  rw [ht, hs]

/-- A vector fixed at two ordered times is fixed at their difference. -/
theorem fixed_sub_of_le (S :
    StronglyContinuousSemigroup X) {s t : ℝ≥0} {x : X} (h : s ≤ t) (hs : S s x = x) (ht : S t x
    = x) :
    S (t - s) x = x := by
  have h2 : (t - s) + s = t := tsub_add_cancel_of_le h
  rw [← h2, S.map_add_apply, hs] at ht
  exact ht

/-- The orbit of a vector fixed at a given time remains fixed at that time. -/
theorem fixed_orbit (S :
    StronglyContinuousSemigroup X) {s : ℝ≥0} {x : X} (hx : S s x = x) (t : ℝ≥0) :
    S s (S t x) = S t x := by
  rw [← S.map_add_apply, add_comm, S.map_add_apply, hx]

/-- A vector fixed at a given time has an orbit with that period. -/
theorem orbit_periodic (S :
    StronglyContinuousSemigroup X) {s : ℝ≥0} {x : X} (hx : S s x = x) :
    ∀ t : ℝ≥0, S (t + s) x = S t x := by
  intro t
  rw [S.map_add_apply t s x, hx]

/-- A fixed difference of vectors gives equal orbit increments. -/
theorem orbit_increment_eq_of_fixed_sub (S :
    StronglyContinuousSemigroup X) (t : ℝ≥0) {x y : X} (h : S t (x - y) = x - y) :
    S t x - x = S t y - y := by
  have h1 : S t x - S t y = x - y := by
    rw [← h, (S t).map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp h1

/-- A vector fixed by an operator of norm less than one is zero. -/
theorem eq_zero_of_fixed_of_norm_lt_one (S :
    StronglyContinuousSemigroup X) {t : ℝ≥0} {x : X} (hx : S t x = x) (h : ‖S t‖ < 1) :
    x = 0 := by
  have h1 : ‖x‖ ≤ ‖S t‖ * ‖x‖ := by
    have h := ContinuousLinearMap.le_opNorm (S t) x
    rw [hx] at h
    exact h
  have h2 : ‖x‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have := mul_lt_mul_of_pos_right h hpos
    linarith
  exact norm_eq_zero.mp h2

end StronglyContinuousSemigroup

namespace ContractionSemigroup

/-- A contraction semigroup does not increase the norm of a vector. -/
theorem norm_apply_le (S : ContractionSemigroup X) (t : ℝ≥0) (x : X) :
    ‖S t x‖ ≤ ‖x‖ := calc
  ‖S t x‖ ≤ ‖S t‖ * ‖x‖ := (S t).le_opNorm x
  _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (S.contracting t) (norm_nonneg x)
  _ = ‖x‖ := one_mul _

/-- The norm bound controls the separation of two orbits at a fixed time. -/
theorem norm_orbit_sub_le (S : ContractionSemigroup X) (t : ℝ≥0) (x y : X) :
    ‖S t x - S t y‖ ≤ ‖x - y‖ := by
  simpa only [map_sub] using S.norm_apply_le t (x - y)

/-- For a contraction semigroup, an orbit increment decreases after a time shift. -/
theorem norm_increment_bound (S : ContractionSemigroup
    X) (s t : ℝ≥0) (x : X) :
    ‖S (s + t) x - S s x‖ ≤ ‖S t x - x‖ := by
  have h := S.toStronglyContinuousSemigroup.map_add_sub_apply s t x
  simp only [toStronglyContinuousSemigroup_apply] at h
  rw [h]
  exact S.norm_apply_le s (S t x - x)

/-- A contraction semigroup preserves every closed ball centered at zero. -/
theorem orbit_closedBall (S : ContractionSemigroup X) (t
    : ℝ≥0) {x : X} {r : ℝ} (hx : x ∈ Metric.closedBall 0 r) :
    S t x ∈ Metric.closedBall 0 r := by
  simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx ⊢
  exact (S.norm_apply_le t x).trans hx

/-- A contraction semigroup preserves every open ball centered at zero. -/
theorem orbit_ball (S : ContractionSemigroup X) (t :
    ℝ≥0) {x : X} {r : ℝ} (hx : x ∈ Metric.ball 0 r) :
    S t x ∈ Metric.ball 0 r := by
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hx ⊢
  exact (S.norm_apply_le t x).trans_lt hx

/-- A contraction orbit returning to its initial vector preserves its norm at earlier times. -/
theorem norm_eq_of_return (S : ContractionSemigroup X)
    {s t : ℝ≥0} (h : s ≤ t) {x : X} (hx : S t x = x) :
    ‖S s x‖ = ‖x‖ := by
  have hts : (t - s) + s = t := by
    rw [add_comm, add_tsub_cancel_of_le h]
  have hsg : S ((t - s) + s) x = S (t - s) (S s x) :=
    (S.toStronglyContinuousSemigroup).map_add_apply (t - s) s x
  have hge : ‖x‖ ≤ ‖S s x‖ := by
    calc ‖x‖ = ‖S (t - s) (S s x)‖ := by rw [← hsg, hts, hx]
      _ ≤ ‖S s x‖ := S.norm_apply_le (t - s) (S s x)
  exact le_antisymm (S.norm_apply_le s x) hge

end ContractionSemigroup

end TauCeti.Semigroups
