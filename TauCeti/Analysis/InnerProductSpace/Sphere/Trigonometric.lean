/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Homotopy.Basic

/-!
# Trigonometric combinations of orthogonal unit vectors

For orthogonal unit vectors `p, q` in a real inner product space, the combination
`cos(t) p + sin(t) q` has norm one. This supplies the unit-sphere membership needed
to parametrize great circles without any manifold or finite-dimensional assumptions.

Following the half great circles `t ↦ cos (π t) • f x + sin (π t) • v x` from `f x` to `-f x`, a
map `f` into the unit sphere is homotopic to its antipode `-f` as soon as it has a unit normal
field `v`, a map into the unit sphere with `v x` orthogonal to `f x` for every `x`
(`ContinuousMap.homotopic_neg_of_inner_eq_zero`). For `f` the identity of the sphere, `v` is a
unit tangent vector field; this is the homotopy behind the hairy ball theorem.
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

namespace ContinuousMap

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Type*}
  [TopologicalSpace X]

/-- **A map into the sphere with a unit normal field is homotopic to its antipode.** If
`f, v : X → S` are maps into the unit sphere `S` of a real inner product space with `v x`
orthogonal to `f x` for every `x`, then `f` is homotopic to `-f`, through the half great circles
`t ↦ cos (π t) • f x + sin (π t) • v x`. -/
theorem homotopic_neg_of_inner_eq_zero (f v : C(X, sphere (0 : E) 1))
    (h : ∀ x, inner ℝ (f x : E) (v x : E) = 0) : f.Homotopic (-f) :=
  ⟨{ toFun p := ⟨Real.cos (Real.pi * p.1) • (f p.2 : E) + Real.sin (Real.pi * p.1) • (v p.2 : E),
        mem_sphere_zero_iff_norm.2 (norm_cos_smul_add_sin_smul _ _ (h p.2) _)⟩
     continuous_toFun := by fun_prop
     map_zero_left x := Subtype.ext (by simp)
     map_one_left x := Subtype.ext (by simp) }⟩

end ContinuousMap
