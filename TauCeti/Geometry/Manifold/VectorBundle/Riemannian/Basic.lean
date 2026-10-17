/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Extensionality of smooth Riemannian metrics

A bundled smooth Riemannian metric is determined by its fibrewise inner products.
This permits comparison of metrics without installing them as competing bundle
instances.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- Two smooth Riemannian metrics agree if all their inner products agree. -/
@[ext]
theorem contMDiffRiemannianMetric_ext {g h : ContMDiffRiemannianMetric IB n F E}
    (hinner : ∀ b v w, g.inner b v w = h.inner b v w) : g = h := by
  have : g.inner = h.inner := by
    funext b
    ext v w
    exact hinner b v w
  cases g
  cases h
  congr

end TauCeti
