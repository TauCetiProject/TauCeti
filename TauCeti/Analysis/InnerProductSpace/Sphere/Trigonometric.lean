/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Trigonometric combinations of orthogonal unit vectors

For orthogonal unit vectors `p, q` in a real inner product space, the combination
`cos(t) p + sin(t) q` has norm one. This supplies the unit-sphere membership needed
to parametrize great circles without any manifold or finite-dimensional assumptions.
-/

public section

open Metric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A cosine-sine combination of orthogonal unit vectors has norm one. -/
theorem norm_cos_smul_add_sin_smul (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) (t : ℝ) :
    ‖Real.cos t • (p : E) + Real.sin t • (q : E)‖ = 1 := by
  have hp : inner ℝ (p : E) p = 1 := by
    simp [norm_eq_of_mem_sphere]
  have hq : inner ℝ (q : E) q = 1 := by
    simp [norm_eq_of_mem_sphere]
  have hqp : inner ℝ (q : E) (p : E) = 0 := by rwa [real_inner_comm]
  have hsq : ‖Real.cos t • (p : E) + Real.sin t • (q : E)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hp, hq, hpq, hqp]
    nlinarith [Real.cos_sq_add_sin_sq t]
  nlinarith [norm_nonneg (Real.cos t • (p : E) + Real.sin t • (q : E))]

end TauCeti
