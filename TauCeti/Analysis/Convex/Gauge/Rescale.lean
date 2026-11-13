/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Gauge rescale homeomorphisms through prescribed interior points

Mathlib's `exists_homeomorph_image_eq` gives, for two convex von Neumann bounded sets `s` and
`t` with nonempty interiors in a real topological vector space, a homeomorphism of the ambient
space sending the interior, the closure and the frontier of `s` to those of `t`. Its proof
translates an interior point `x` of `s` and an interior point `y` of `t` to the origin and
applies `gaugeRescaleHomeomorph`, which fixes the origin. Hence the homeomorphism can be chosen
to send any prescribed interior point `x` of `s` to any prescribed interior point `y` of `t`.

Taking `t = s`, the interior of a closed convex bounded set is homogeneous under the
homeomorphisms of the set preserving its interior. For instance, a closed ball can be recentred
at any point of the open ball.

## Main declarations

* `TauCeti.exists_homeomorph_image_eq_of_mem_interior`: the homeomorphism of
  `exists_homeomorph_image_eq` can be chosen to send `x` to `y`.
* `TauCeti.exists_homeomorph_apply_eq_of_mem_interior`: a self-homeomorphism of a closed convex
  bounded set preserving its interior and sending one interior point to another.
* `TauCeti.exists_homeomorph_closedBall_apply_eq`: the same for a closed ball of a real normed
  space and two points of the open ball.

## References

The proof of `TauCeti.exists_homeomorph_image_eq_of_mem_interior` is the proof of Mathlib's
`exists_homeomorph_image_eq` in `Mathlib/Analysis/Convex/GaugeRescale.lean`, due to Yury
Kudryashov, with the image of the chosen interior point recorded.
-/

public section

open Metric Set Bornology
open scoped Pointwise Topology

namespace TauCeti

/-- Evaluating the bundled gauge rescale homeomorphism gives the gauge rescale map. -/
@[simp] theorem gaugeRescaleHomeomorph_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T1Space E]
    (s t : Set E) (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) (x : E) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb x = gaugeRescale s t x := rfl

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T1Space E] {s t : Set E} {x y : E}

/-- Given two convex bounded sets `s` and `t` in a real topological vector space and interior
points `x` of `s` and `y` of `t`, there is a homeomorphism of the ambient space sending `x` to `y`
and the interior, the closure and the frontier of `s` to those of `t`. This is
`exists_homeomorph_image_eq` with a prescribed image of one interior point. -/
theorem exists_homeomorph_image_eq_of_mem_interior (hsc : Convex ℝ s) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (htb : IsVonNBounded ℝ t) (hx : x ∈ interior s) (hy : y ∈ interior t) :
    ∃ e : E ≃ₜ E, e x = y ∧ e '' interior s = interior t ∧ e '' closure s = closure t ∧
      e '' frontier s = frontier t := by
  let h : E ≃ₜ E := by
    apply gaugeRescaleHomeomorph (-x +ᵥ s) (-y +ᵥ t) <;>
      simp [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem, *]
  let e : E ≃ₜ E := .trans (.addLeft (-x)) <| h.trans <| .addLeft y
  have he : ⇑e = fun a ↦ y + h (-x + a) := by ext; simp [e]
  have he_img (u : Set E) : e '' u = y +ᵥ h '' (-x +ᵥ u) := by
    simp_rw [he, ← image_vadd, image_image, vadd_eq_add]
  have hint : e '' interior s = interior t := by
    rw [he_img, ← interior_vadd, image_gaugeRescaleHomeomorph_interior, interior_vadd,
      vadd_neg_vadd]
  have hcl : e '' closure s = closure t := by
    rw [he_img, ← closure_vadd, image_gaugeRescaleHomeomorph_closure, closure_vadd,
      vadd_neg_vadd]
  refine ⟨e, ?_, hint, hcl, ?_⟩
  · simp [e, h]
  · simp_rw [← closure_sdiff_interior, image_sdiff e.injective, hint, hcl]

/-- The interior of a closed convex bounded set `s` of a real topological vector space is
homogeneous: for interior points `x` and `y` of `s`, some self-homeomorphism of `s` sends `x` to
`y` and preserves the interior of `s`. -/
theorem exists_homeomorph_apply_eq_of_mem_interior (hsc : Convex ℝ s) (hsb : IsVonNBounded ℝ s)
    (hs : IsClosed s) (hx : x ∈ interior s) (hy : y ∈ interior s) :
    ∃ f : s ≃ₜ s, (f ⟨x, interior_subset hx⟩ : E) = y ∧
      ∀ z : s, (f z : E) ∈ interior s ↔ (z : E) ∈ interior s := by
  obtain ⟨e, hexy, hint, hcl, -⟩ :=
    exists_homeomorph_image_eq_of_mem_interior hsc hsb hsc hsb hx hy
  rw [hs.closure_eq] at hcl
  refine ⟨e.subtype fun z ↦ ?_, ?_, fun z ↦ ?_⟩
  · rw [← e.injective.mem_set_image, hcl]
  · simpa only [Homeomorph.subtype_apply_coe] using hexy
  · simpa only [Homeomorph.subtype_apply_coe, hint] using
      e.injective.mem_set_image (a := (z : E)) (s := interior s)

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c x y : E} {r : ℝ}

/-- A closed ball of a real normed space can be recentred: for points `x` and `y` of the open
ball, some self-homeomorphism of the closed ball sends `x` to `y` and preserves the open ball. -/
theorem exists_homeomorph_closedBall_apply_eq (hx : x ∈ ball c r) (hy : y ∈ ball c r) :
    ∃ f : closedBall c r ≃ₜ closedBall c r, (f ⟨x, ball_subset_closedBall hx⟩ : E) = y ∧
      ∀ z : closedBall c r, (f z : E) ∈ ball c r ↔ (z : E) ∈ ball c r := by
  have hr : r ≠ 0 := (pos_of_mem_ball hx).ne'
  rw [← interior_closedBall c hr] at hx hy ⊢
  exact exists_homeomorph_apply_eq_of_mem_interior (convex_closedBall c r)
    (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall) isClosed_closedBall hx hy

end TauCeti
