/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The mean value inequality across a puncture

Let `s` be a convex open subset of a real normed space `E` of dimension greater than one, and let
`p` be a point. If `f` is differentiable on `s ∖ {p}` with `‖Df‖ ≤ C` there, then
`‖f y - f x‖ ≤ C ‖y - x‖` for all `x, y ∈ s ∖ {p}`, with the same constant as on a convex set,
although `s ∖ {p}` is not convex.

When the segment `[x, y]` avoids `p`, this is the mean value inequality. Otherwise `y - x` is
parallel to `p - x`; moving `y` to `y + t v`, with `v` not parallel to `p - x`, gives segments
`[x, y + t v]` that avoid `p` for `t ≠ 0`, and the inequality for `y` follows by letting `t → 0`.

In dimension one the statement fails: the sign function on `ℝ ∖ {0}` has
zero derivative but is not continuous across `0`.

## Main results

* `Convex.norm_image_sub_le_of_norm_fderiv_le_sdiff_singleton`: the mean value inequality on
  `s ∖ {p}`.
* `Convex.lipschitzOnWith_sdiff_singleton_of_nnNorm_fderiv_le`: the Lipschitz form.

## References

* O. Chodosh, *Introduction to minimal surfaces*, proof of Theorem 32.5.
-/

public section

open Filter Set
open scoped NNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {s : Set E} {p x y : E} {f : E → F} {C : ℝ}

/-- **The mean value inequality across a puncture.** In a real normed space of dimension greater
than one, if `f` is differentiable on `s ∖ {p}`, with `s` convex and open, and `‖Df‖ ≤ C` there,
then `‖f y - f x‖ ≤ C ‖y - x‖` for all `x, y ∈ s ∖ {p}`. -/
theorem Convex.norm_image_sub_le_of_norm_fderiv_le_sdiff_singleton (hs : Convex ℝ s)
    (hso : IsOpen s) (hE : 1 < Module.rank ℝ E) (hf : ∀ z ∈ s \ {p}, DifferentiableAt ℝ f z)
    (bound : ∀ z ∈ s \ {p}, ‖fderiv ℝ f z‖ ≤ C) (hx : x ∈ s \ {p}) (hy : y ∈ s \ {p}) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  have key : ∀ y' ∈ s, p ∉ segment ℝ x y' → ‖f y' - f x‖ ≤ C * ‖y' - x‖ := by
    intro y' hy' hp
    have hsub : segment ℝ x y' ⊆ s \ {p} :=
      fun z hz ↦ ⟨hs.segment_subset hx.1 hy' hz, fun h ↦ hp (h ▸ hz)⟩
    exact (convex_segment x y').norm_image_sub_le_of_norm_fderiv_le (fun z hz ↦ hf z (hsub hz))
      (fun z hz ↦ bound z (hsub hz)) (left_mem_segment ℝ x y') (right_mem_segment ℝ x y')
  have hspan : ∀ y' : E, p ∈ segment ℝ x y' → y' - x ∈ Submodule.span ℝ {p - x} := by
    intro y' hp
    rw [segment_eq_image'] at hp
    obtain ⟨θ, -, hθ⟩ := hp
    have hθ0 : θ ≠ 0 := by
      rintro rfl
      exact hx.2 (by simpa using hθ)
    refine Submodule.mem_span_singleton.2 ⟨θ⁻¹, ?_⟩
    simp [← hθ, hθ0]
  by_cases hseg : p ∈ segment ℝ x y
  · obtain ⟨v, hv⟩ := Submodule.exists_smul_notMem_of_rank_lt
      (N := Submodule.span ℝ {p - x}) ((rank_span_le _).trans_lt (by simpa using hE))
    have hyx := hspan y hseg
    have hc : Tendsto (fun t : ℝ ↦ y + t • v) (𝓝[≠] 0) (𝓝 y) := by
      have h : Tendsto (fun t : ℝ ↦ y + t • v) (𝓝 0) (𝓝 (y + (0 : ℝ) • v)) :=
        tendsto_const_nhds.add (tendsto_id.smul_const v)
      rw [zero_smul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖f (y + t • v) - f x‖ ≤ C * ‖y + t • v - x‖ := by
      filter_upwards [hc.eventually (hso.mem_nhds hy.1), self_mem_nhdsWithin] with t hts ht0
      refine key _ hts fun hp ↦ hv t ht0 ?_
      have h := sub_mem (hspan _ hp) hyx
      convert h using 1; abel
    exact le_of_tendsto_of_tendsto
      (((hf y hy).continuousAt.tendsto.comp hc).sub_const (f x)).norm
      ((hc.sub_const x).norm.const_mul C) hev
  · exact key y hy.1 hseg

/-- **Lipschitz bound across a puncture.** In a real normed space of dimension greater than one,
a function differentiable on `s ∖ {p}`, with `s` convex and open, and with `‖Df‖₊ ≤ C` there, is
`C`-Lipschitz on `s ∖ {p}`. -/
theorem Convex.lipschitzOnWith_sdiff_singleton_of_nnNorm_fderiv_le (hs : Convex ℝ s)
    (hso : IsOpen s) (hE : 1 < Module.rank ℝ E) {C : ℝ≥0}
    (hf : ∀ z ∈ s \ {p}, DifferentiableAt ℝ f z) (bound : ∀ z ∈ s \ {p}, ‖fderiv ℝ f z‖₊ ≤ C) :
    LipschitzOnWith C f (s \ {p}) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  exact hs.norm_image_sub_le_of_norm_fderiv_le_sdiff_singleton hso hE hf
    (fun z hz ↦ NNReal.coe_le_coe.2 (bound z hz)) hy hx
