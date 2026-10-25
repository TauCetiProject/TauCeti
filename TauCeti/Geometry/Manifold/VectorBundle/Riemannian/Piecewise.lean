/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Gluing Riemannian metrics along an open cover

Let `U` and `V` be open subsets covering the base of a vector bundle, and let `g₁` and `g₂` be
`C^n` Riemannian metrics on the bundle which agree over `U ∩ V`. Then there is a `C^n` Riemannian
metric equal to `g₁` over `U` and to `g₂` over `V`. Positivity and boundedness of the
unit ball are fibrewise conditions, and smoothness is local: near a point of `U` the glued metric
is `g₁`, and near a point of `V` it is `g₂`.

This is how metrics built separately on overlapping regions, for instance on the two ends of a
cylinder that agree with a common product metric on the overlap, are assembled into one metric.

## Main definitions and results

* `Bundle.ContMDiffRiemannianMetric.piecewise`: the metric equal to `g₁` over `U` and to `g₂`
  over `V`.
* `Bundle.ContMDiffRiemannianMetric.piecewise_inner_of_mem_left` and
  `Bundle.ContMDiffRiemannianMetric.piecewise_inner_of_mem_right`: its inner products over `U`
  and over `V`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {U V : Set B}

open Classical in
/-- Glue two `C^n` Riemannian metrics `g₁` and `g₂` which agree over the overlap of two open sets
`U` and `V` covering the base: the result is `g₁` over `U` and `g₂` over `V`. -/
def piecewise (g₁ g₂ : ContMDiffRiemannianMetric IB n F E) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) (h : ∀ b ∈ U ∩ V, g₁.inner b = g₂.inner b) :
    ContMDiffRiemannianMetric IB n F E where
  inner b := if b ∈ U then g₁.inner b else g₂.inner b
  symm b v w := by
    split_ifs
    exacts [g₁.symm b v w, g₂.symm b v w]
  pos b v hv := by
    split_ifs
    exacts [g₁.pos b v hv, g₂.pos b v hv]
  isVonNBounded b := by
    split_ifs
    exacts [g₁.isVonNBounded b, g₂.isVonNBounded b]
  contMDiff b := by
    by_cases hb : b ∈ U
    · -- Near a point of `U`, the glued metric is `g₁`.
      refine (g₁.contMDiff b).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds hb] with c hc
      simp [hc]
    · -- Near a point outside `U`, which lies in `V`, the glued metric is `g₂`.
      have hbV : b ∈ V := (hUV ▸ mem_univ b : b ∈ U ∪ V).resolve_left hb
      refine (g₂.contMDiff b).congr_of_eventuallyEq ?_
      filter_upwards [hV.mem_nhds hbV] with c hc
      split_ifs with hcU
      · rw [h c ⟨hcU, hc⟩]
      · rfl

variable {g₁ g₂ : ContMDiffRiemannianMetric IB n F E} {hU : IsOpen U} {hV : IsOpen V}
  {hUV : U ∪ V = univ} {h : ∀ b ∈ U ∩ V, g₁.inner b = g₂.inner b}

/-- Over `U`, the glued metric is `g₁`. -/
theorem piecewise_inner_of_mem_left {b : B} (hb : b ∈ U) :
    (g₁.piecewise g₂ hU hV hUV h).inner b = g₁.inner b := by
  simp [piecewise, hb]

/-- Over `V`, the glued metric is `g₂`. -/
theorem piecewise_inner_of_mem_right {b : B} (hb : b ∈ V) :
    (g₁.piecewise g₂ hU hV hUV h).inner b = g₂.inner b := by
  by_cases hbU : b ∈ U
  · rw [piecewise_inner_of_mem_left hbU, h b ⟨hbU, hb⟩]
  · simp [piecewise, hbU]

end Bundle.ContMDiffRiemannianMetric
