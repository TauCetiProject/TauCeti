/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Metric

/-!
# Metric compatibility of the normal connection of an immersion

Let `f : M → N` be a map into a manifold with a Riemannian metric and a metric-compatible
covariant derivative `∇` on `TN`. The normal connection `∇^⊥_X ν = (∇_X ν)^⊥`
(`TauCeti.immersionNormalConnection`) preserves the induced metric on the normal spaces: for fields
`ν`, `ξ` along `f` which are normal at `x`,

`X ⟪ν, ξ⟫ = ⟪∇^⊥_X ν, ξ⟫ + ⟪ν, ∇^⊥_X ξ⟫`

(`TauCeti.mvfderiv_inner_eq_inner_immersionNormalConnection`). In particular the normal
connection of a unit normal field is orthogonal to it
(`TauCeti.inner_immersionNormalConnection_self_eq_zero`). The proof is the product rule along
`f` (`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_alongMap`): pairing `∇_X ν` with the
normal vector `ξ x` only sees its normal part.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8
  (the normal connection and its compatibility with the metric).
-/

public section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {cov : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)} {f : M → N} {x : M}

/-- **The normal connection is metric.** For a metric-compatible covariant derivative, a map `f`
differentiable at `x`, and fields `ν`, `ξ` along `f` with differentiable readings at `x` which are
normal at `x`, `X ⟪ν, ξ⟫ = ⟪∇^⊥_X ν, ξ⟫ + ⟪ν, ∇^⊥_X ξ⟫` at `x`. -/
theorem mvfderiv_inner_eq_inner_immersionNormalConnection
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (hf : MDifferentiableAt I J f x) {ν ξ : Π y : M, TangentSpace J (f y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hξ : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ξ (f x)) x)
    (hνx : ν x ∈ orthogonalNormalSpace I J f x) (hξx : ξ x ∈ orthogonalNormalSpace I J f x)
    (X : Π y : M, TangentSpace I y) :
    mvfderiv I (fun y ↦ inner ℝ (ν y) (ξ y)) x (X x) =
      inner ℝ (immersionNormalConnection cov f ν X x) (ξ x) +
        inner ℝ (ν x) (immersionNormalConnection cov f ξ X x) := by
  rw [hcov.mvfderiv_inner_alongMap hf hν hξ (X x),
    ← inner_immersionNormalConnection_of_mem ν X hξx, real_inner_comm _ (ν x),
    ← inner_immersionNormalConnection_of_mem ξ X hνx, real_inner_comm (ν x)]

/-- The normal connection of a normal field of constant length near `x`, such as a unit normal
field, is orthogonal to it at `x`: `⟪∇^⊥_X ν, ν⟫ = 0`. -/
theorem inner_immersionNormalConnection_self_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (hf : MDifferentiableAt I J f x) {ν : Π y : M, TangentSpace J (f y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hνx : ν x ∈ orthogonalNormalSpace I J f x) {c : ℝ}
    (hc : ∀ᶠ y in 𝓝 x, inner ℝ (ν y) (ν y) = c) (X : Π y : M, TangentSpace I y) :
    inner ℝ (immersionNormalConnection cov f ν X x) (ν x) = 0 := by
  have h := mvfderiv_inner_eq_inner_immersionNormalConnection hcov hf hν hν hνx hνx X
  rw [Filter.EventuallyEq.mvfderiv_eq (f := fun _ ↦ c) hc, mvfderiv_const, zero_apply,
    real_inner_comm (immersionNormalConnection cov f ν X x) (ν x)] at h
  linarith

end TauCeti
