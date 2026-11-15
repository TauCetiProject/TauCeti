/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Metric and cardinality properties of orthonormal families

Distinct members of an orthonormal family in an inner product space have squared difference norm `2`
and mutual distance `√2` (`Orthonormal.norm_sub_sq`, `Orthonormal.dist_eq_sqrt_two`). Consequently,
any orthonormal family in a separable inner product space is countable (`Orthonormal.countable`),
and any orthonormal family in a subsingleton space has an empty index type
(`Orthonormal.isEmpty_of_subsingleton`).

For every vector `x`, Bessel's inequality forces the set of indices where `⟪v i, x⟫ ≠ 0` to be
countable (`Orthonormal.countable_support_inner`). Together with completeness of Hilbert bases,
these properties underlie the invariance of Hilbert-basis cardinality and the classification of
Hilbert spaces by Hilbert dimension.
-/

public section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {v : ι → E}

/-- Distinct members of an orthonormal family have squared difference norm `2`. -/
theorem norm_sub_sq (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ ^ 2 = 2 := by
  rw [@_root_.norm_sub_sq 𝕜, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij]
  norm_num

/-- Distinct members of an orthonormal family have difference norm `√2`. -/
theorem norm_sub_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i - v j‖ = √2 := by
  rw [← Real.sqrt_sq (norm_nonneg _), hv.norm_sub_sq hij]

/-- Distinct members of an orthonormal family lie at distance `√2`. -/
theorem dist_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    dist (v i) (v j) = √2 := by
  rw [dist_eq_norm, hv.norm_sub_eq_sqrt_two hij]

/-- Distinct members of an orthonormal family have squared sum norm `2`. -/
theorem norm_add_sq (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i + v j‖ ^ 2 = 2 := by
  rw [@_root_.norm_add_sq 𝕜, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij]
  norm_num

/-- Distinct members of an orthonormal family have sum norm `√2`. -/
theorem norm_add_eq_sqrt_two (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    ‖v i + v j‖ = √2 := by
  rw [← Real.sqrt_sq (norm_nonneg _), hv.norm_add_sq hij]

/-- Against any vector `x`, at most countably many members of an orthonormal family have nonzero
inner product `⟪v i, x⟫`. -/
theorem countable_support_inner (hv : Orthonormal 𝕜 v) (x : E) :
    {i : ι | ⟪v i, x⟫_𝕜 ≠ 0}.Countable := by
  refine (hv.inner_products_summable x).countable_support.mono fun i (hi : ⟪v i, x⟫_𝕜 ≠ 0) ↦ ?_
  exact pow_ne_zero 2 (norm_ne_zero_iff.2 hi)

/-- Against any vector `x`, at most countably many members of an orthonormal family have nonzero
inner product `⟪x, v i⟫`. -/
theorem countable_support_inner_right (hv : Orthonormal 𝕜 v) (x : E) :
    {i : ι | ⟪x, v i⟫_𝕜 ≠ 0}.Countable := by
  refine (hv.countable_support_inner x).mono fun i (hi : ⟪x, v i⟫_𝕜 ≠ 0) ↦ ?_
  rwa [← inner_conj_symm, starRingEnd_apply, star_ne_zero] at hi

/-- Every orthonormal family in a separable inner product space has a countable index type. -/
theorem countable [TopologicalSpace.SeparableSpace E] (hv : Orthonormal 𝕜 v) :
    Countable ι := by
  -- Open balls of radius `√2 / 2` around the `v i` are pairwise disjoint because `dist = √2`.
  refine Pairwise.countable_of_isOpen_disjoint
    (s := fun i : ι ↦ Metric.ball (v i) (√2 / 2))
    (fun i j hij ↦ Metric.ball_disjoint_ball <| by rw [add_halves, hv.dist_eq_sqrt_two hij])
    (fun _ ↦ Metric.isOpen_ball)
    (fun _ ↦ Metric.nonempty_ball.2 (by positivity))

/-- An orthonormal family in a subsingleton inner product space has an empty index type. -/
theorem isEmpty_of_subsingleton [Subsingleton E] (hv : Orthonormal 𝕜 v) :
    IsEmpty ι :=
  ⟨fun i ↦ hv.ne_zero i (Subsingleton.elim (v i) 0)⟩

/-- An orthonormal subset of a subsingleton inner product space is empty. -/
theorem eq_empty_of_subsingleton [Subsingleton E] {s : Set E}
    (hs : Orthonormal 𝕜 ((↑) : s → E)) : s = ∅ := by
  have := hs.isEmpty_of_subsingleton
  exact Set.eq_empty_of_isEmpty s

end Orthonormal
