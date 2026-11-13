/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# The exponential map of a commutative complex Lie group is holomorphic

A complex Lie group `G` modelled on a finite-dimensional complex space `E` is also a real Lie group,
with the same charts. Its real exponential `exp : E → G` is the tangent-space exponential
`mulInvariantExp` of that real Lie group: the time-one value of the flow of an invariant vector
field. This file shows that for commutative `G` this map is holomorphic.

Read in the chart at the identity, the real derivative of `exp` at `0` is the identity of `E`,
which is complex linear; so `exp` is complex differentiable at `0`, for every complex Lie group.
When `G` is commutative, `exp` is a homomorphism (`TauCeti.mulInvariantExp_add`), so near any `v`
it is `w ↦ exp v * exp (w - v)`, a left translate of its germ at `0`, and left translations of `G`
are holomorphic.

## Main results

* `TauCeti.hasFDerivAt_extChartAt_mulInvariantExp_zero_complex`: in the chart at the identity of a
  complex Lie group, the real exponential has complex derivative the identity at `0`.
* `TauCeti.mdifferentiable_mulInvariantExp_complex` and
  `TauCeti.contMDiff_mulInvariantExp_complex`: the real exponential of a commutative complex Lie
  group is holomorphic.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, for complex Lie groups as real Lie groups.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup 𝓘(ℝ, E) ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The derivative of the exponential of a complex Lie group at `0` is the identity**: read in
the chart at the identity, the real exponential has complex derivative the identity at `0`. Only
the real Lie group structure on the complex charts is used. -/
theorem hasFDerivAt_extChartAt_mulInvariantExp_zero_complex :
    HasFDerivAt (fun v : E ↦ extChartAt 𝓘(ℂ, E) (1 : G)
      (mulInvariantExp (I := 𝓘(ℝ, E)) (v : GroupLieAlgebra 𝓘(ℝ, E) G)))
      (ContinuousLinearMap.id ℂ E) 0 :=
  -- The real derivative is the identity, which is complex linear. The charts of the two models
  -- agree, as both self-models have the identity as underlying map.
  hasFDerivAt_of_restrictScalars ℝ (hasFDerivAt_extChartAt_mulInvariantExp_zero (I := 𝓘(ℝ, E)))
    (by ext; rfl)

variable [LieGroup 𝓘(ℂ, E) ∞ G] [IsMulCommutative G]

/-- **The exponential of a commutative complex Lie group is holomorphic.** -/
theorem mdifferentiable_mulInvariantExp_complex :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E) (fun v : E ↦
      mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) (v : GroupLieAlgebra 𝓘(ℝ, E) G)) := by
  intro v
  have h₀ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E)
      (fun w : E ↦ mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) (w : GroupLieAlgebra 𝓘(ℝ, E) G)) 0 := by
    rw [mdifferentiableAt_iff_target, mdifferentiableAt_iff_differentiableAt]
    refine ⟨((contMDiff_mulInvariantExp (I := 𝓘(ℝ, E)) (G := G)).continuous).continuousAt, ?_⟩
    have h1 : mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) ((0 : E) : GroupLieAlgebra 𝓘(ℝ, E) G) = 1 :=
      mulInvariantExp_zero
    rw [h1]
    exact hasFDerivAt_extChartAt_mulInvariantExp_zero_complex.differentiableAt
  -- Near `v` the exponential is the left translate by `exp v` of its germ at `0`.
  have h : (fun w : E ↦ mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) (w : GroupLieAlgebra 𝓘(ℝ, E) G)) =
      fun w ↦ mulInvariantExp (v : GroupLieAlgebra 𝓘(ℝ, E) G) *
        mulInvariantExp ((w - v : E) : GroupLieAlgebra 𝓘(ℝ, E) G) :=
    funext fun w ↦ (congrArg (mulInvariantExp (I := 𝓘(ℝ, E)) (G := G))
      (add_sub_cancel v w).symm).trans (mulInvariantExp_add _ _)
  have h₁ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E)
      (fun w : E ↦
        mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) ((w - v : E) : GroupLieAlgebra 𝓘(ℝ, E) G)) v := by
    refine MDifferentiableAt.comp v ?_ (differentiableAt_id.sub_const v).mdifferentiableAt
    simp only [sub_self]
    exact h₀
  rw [h]
  exact ((contMDiff_mul_left (I := 𝓘(ℂ, E)) (n := 1)).mdifferentiableAt one_ne_zero).comp v h₁

/-- **The exponential of a commutative complex Lie group is an entire map**: it is `C^n` over `ℂ`
for every `n`, including `n = ω`. -/
theorem contMDiff_mulInvariantExp_complex (n : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) n (fun v : E ↦
      mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) (v : GroupLieAlgebra 𝓘(ℝ, E) G)) :=
  have : FiniteDimensional ℂ E := .of_restrictScalars_finite ℝ ℂ E
  mdifferentiable_mulInvariantExp_complex.contMDiff

end TauCeti
