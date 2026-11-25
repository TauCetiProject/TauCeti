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
  -- Over each point use whichever of `g₁` and `g₂` is chosen there, so that the fibrewise
  -- axioms are those of the chosen metric.
  inner b := (if b ∈ U then g₁ else g₂).inner b
  symm b := (if b ∈ U then g₁ else g₂).symm b
  pos b := (if b ∈ U then g₁ else g₂).pos b
  isVonNBounded b := (if b ∈ U then g₁ else g₂).isVonNBounded b
  contMDiff := contMDiff_of_contMDiffOn_union_of_isOpen
    -- Over `U`, the glued metric is `g₁`.
    (g₁.contMDiff.contMDiffOn.congr fun b hb ↦ by simp [hb])
    -- Over `V` it is `g₂`, as `g₁` and `g₂` agree over `U ∩ V`.
    (g₂.contMDiff.contMDiffOn.congr fun b hb ↦ by
      split_ifs with hbU
      · rw [h b ⟨hbU, hb⟩]
      · rfl)
    hUV hU hV

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
