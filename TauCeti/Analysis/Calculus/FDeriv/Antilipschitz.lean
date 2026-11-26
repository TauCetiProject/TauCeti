/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Topology.MetricSpace.Antilipschitz

/-!
# Quantitative embeddings of compact convex sets

An injective map with continuous derivative on a compact convex set is bounded below on chords
if its derivatives are uniformly bounded below on the directions of those chords. The bound
can deteriorate between distant points, but remains positive. Only directions parallel to the
set matter, so the result applies to lower-dimensional simplices in barycentric coordinates.

This is the separation estimate used to preserve injectivity under small Lipschitz errors in
secant approximations; compare Munkres, *Elementary Differential Topology*, Chapter II, §9.
It rests on the uniform first-order approximation of such a map by its derivative at nearby
points, `IsCompact.exists_pos_forall_norm_image_sub_sub_le`.

With one point held fixed, differentiability at that point alone suffices. At a point `x` where
`f` has an antilipschitz derivative, such as an injective derivative on a finite-dimensional
space, `dist x y ≤ K * dist (f x) (f y)` for `y` near `x`
(`HasFDerivWithinAt.exists_eventually_dist_le_mul_dist`,
`HasFDerivAt.exists_eventually_dist_le_mul_dist`). If moreover `f` is continuous on a compact set
`s` on which `x` is the only point with image `f x`, and the derivative is taken within `s`, the
bound holds for every `y ∈ s`
(`IsCompact.exists_forall_dist_le_mul_dist_of_hasFDerivWithinAt`). This is the global self-point
floor at an injective regular point of a map, in the sense of `TauCeti.AntilipschitzWithFrom`.
-/

public section

open Asymptotics Filter Set Metric
open scoped NNReal Topology

namespace IsCompact

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set V}

/-- A map with a continuous derivative within a compact convex set is uniformly approximated to
first order by its derivative: for every `ε > 0`, the error at nearby points is at most `ε` times
their distance. The derivative need only exist within the set. -/
theorem exists_pos_forall_norm_image_sub_sub_le (hs : IsCompact s) (hconv : Convex ℝ s)
    {F : V → E} {F' : V → V →L[ℝ] E} (hF : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x)
    (hF' : ContinuousOn F' s) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, ‖y - x‖ < δ → ‖F y - F x - F' x (y - x)‖ ≤ ε * ‖y - x‖ := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hs.uniformContinuousOn_of_continuous hF') ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  let T := s ∩ closedBall x ‖y - x‖
  have hderiv : ∀ z ∈ T, HasFDerivWithinAt F (F' z) T z :=
    fun z hz => (hF z hz.1).mono inter_subset_left
  have hnear : ∀ z ∈ T, ‖F' z - F' x‖ ≤ ε := fun z hz => by
    rw [← dist_eq_norm]
    exact (hclose z hz.1 x hx ((mem_closedBall.mp hz.2).trans_lt hxy)).le
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hderiv hnear
    (hconv.inter (convex_closedBall x _)) ⟨hx, by simp⟩ ⟨hy, by simp [dist_eq_norm]⟩

/-- An injective map on a compact convex set whose continuous derivative is uniformly bounded
below on chord directions is antilipschitz on that set. The derivative
need only exist within the set, and need not be injective on the whole ambient space. -/
theorem exists_antilipschitzWith_of_hasFDerivWithinAt (hs : IsCompact s) (hconv : Convex ℝ s)
    {F : V → E} {F' : V → V →L[ℝ] E}
    (hF : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x) (hF' : ContinuousOn F' s)
    (hinj : InjOn F s) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, c * ‖y - z‖ ≤ ‖F' x (y - z)‖) :
    ∃ K > 0, AntilipschitzWith K (s.domRestrict F) := by
  obtain ⟨δ, hδ, hest⟩ := hs.exists_pos_forall_norm_image_sub_sub_le hconv hF hF' (half_pos hc)
  refine hs.exists_antilipschitzWith_of_locally (fun x hx => (hF x hx).continuousWithinAt) hinj
    (half_pos hc) hδ fun x hx y hy hxy => ?_
  rw [dist_comm, dist_eq_norm] at hxy
  have hest := hest x hx y hy hxy
  have hlower := hbound x hx y hy x hx
  have htriangle := norm_sub_norm_le (F' x (y - x)) (F y - F x)
  rw [norm_sub_rev (F' x (y - x))] at htriangle
  simp only [dist_eq_norm, norm_sub_rev x y, norm_sub_rev (F x) (F y)]
  nlinarith

end IsCompact

section Pointwise

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {f' : E →L[𝕜] F}
  {s : Set E} {x : E} {C : ℝ≥0}

/-- At a point where a map has an antilipschitz derivative within a set, the points of the set
near `x` are separated from `x` by their images: `dist x y ≤ K * dist (f x) (f y)` for some `K`. -/
theorem HasFDerivWithinAt.exists_eventually_dist_le_mul_dist (h : HasFDerivWithinAt f f' s x)
    (hf' : AntilipschitzWith C f') :
    ∃ K : ℝ≥0, ∀ᶠ y in 𝓝[s] x, dist x y ≤ K * dist (f x) (f y) := by
  -- As in Mathlib's `HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE`: `y - x` is `O(f' (y - x))`,
  -- which is asymptotically equivalent to `f y - f x`.
  have A : (fun y ↦ y - x) =O[𝓝[s] x] fun y ↦ f' (y - x) := isBigO_iff.2
    ⟨C, .of_forall fun y ↦ by
      simpa only [dist_zero_right, map_zero] using hf'.le_mul_dist (y - x) 0⟩
  have B : (fun y ↦ f y - f x) ~[𝓝[s] x] fun y ↦ f' (y - x) := h.isLittleO.trans_isBigO A
  obtain ⟨c, hc⟩ := (A.trans B.isBigO_symm).bound
  refine ⟨c.toNNReal, hc.mono fun y hy ↦ ?_⟩
  rw [dist_comm x, dist_comm (f x), dist_eq_norm, dist_eq_norm]
  exact hy.trans (by gcongr; exact Real.le_coe_toNNReal c)

/-- At a point where a map has an antilipschitz derivative, nearby points are separated from `x`
by their images: `dist x y ≤ K * dist (f x) (f y)` for `y` near `x`, for some `K`. -/
theorem HasFDerivAt.exists_eventually_dist_le_mul_dist (h : HasFDerivAt f f' x)
    (hf' : AntilipschitzWith C f') : ∃ K : ℝ≥0, ∀ᶠ y in 𝓝 x, dist x y ≤ K * dist (f x) (f y) := by
  simpa only [nhdsWithin_univ] using
    (h.hasFDerivWithinAt (s := univ)).exists_eventually_dist_le_mul_dist hf'

/-- Let `f` be continuous on a compact set `s`, with an antilipschitz derivative within `s` at
`x`, and let `x` be the only point of `s` with image `f x`. Then
`dist x y ≤ K * dist (f x) (f y)` for every `y ∈ s`, for some `K`. -/
theorem IsCompact.exists_forall_dist_le_mul_dist_of_hasFDerivWithinAt (hs : IsCompact s)
    (hf : ContinuousOn f s) (hinj : ∀ y ∈ s, f y = f x → y = x) (h : HasFDerivWithinAt f f' s x)
    (hf' : AntilipschitzWith C f') : ∃ K : ℝ≥0, ∀ y ∈ s, dist x y ≤ K * dist (f x) (f y) :=
  have ⟨_, hK⟩ := h.exists_eventually_dist_le_mul_dist hf'
  hs.exists_forall_dist_le_mul_dist_of_eventually hf hinj hK

end Pointwise
