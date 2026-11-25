/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Strong
public import TauCeti.Analysis.Convex.Along

import TauCeti.Analysis.Convex.Function.Uniform

/-!
# Strong convexity along affine segments

The real-to-extended-real embedding preserves strong convexity along affine segments.
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {f : E → ℝ} {μ : ℝ} {x y : E}

/-- The real-to-extended-real embedding of a strongly convex function is convex along
the affine segment between any two points in its domain, with the same modulus. -/
theorem StrongConvexOn.convexAlong_lineMap (hf : StrongConvexOn s μ f) (hx : x ∈ s) (hy : y ∈ s) :
    TauCeti.ConvexAlong μ (fun z ↦ (f z : EReal)) (AffineMap.lineMap x y) := by
  rw [TauCeti.convexAlong_def]
  intro t ht
  simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
  have hbound : f (AffineMap.lineMap x y t) ≤
      (1 - t) * f x + t * f y - μ / 2 * t * (1 - t) * dist x y ^ 2 := by
    rw [dist_eq_norm]
    convert UniformConvexOn.map_lineMap_le hf hx hy ht using 1
    ring
  exact_mod_cast hbound
