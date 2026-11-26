/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Metric

/-!
# The Weingarten equation for an immersion into a Riemannian manifold

Let `f : M → N` be a map into a manifold with a Riemannian metric and a metric-compatible
covariant derivative `∇` on `TN`. For a field `ν` along `f` which is normal near `x`, the shape
operator `S_ν` (`TauCeti.immersionShapeOperator`) and the second fundamental form `B`
(`TauCeti.immersionSecondFundamentalForm`) are paired by the **Weingarten equation**

`⟪S_ν X, df Y⟫ = ⟪B(X, Y), ν⟫`.

The proof differentiates `⟪ν, df Y⟫ = 0` in the direction `X` with the metric product rule
along `f` (`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_alongMap`): the tangential part
of `∇_X ν` is `-S_ν X` and the normal part of `∇_X (df Y)` is `B(X, Y)`.

For a torsion-free connection the second fundamental form is symmetric
(`TauCeti.immersionSecondFundamentalForm_comm`), so the shape operator is self-adjoint:
`⟪S_ν X, df Y⟫ = ⟪df X, S_ν Y⟫`. Both apply to the Levi-Civita connection of `N`.

## Main results

* `TauCeti.inner_immersionShapeOperator_mfderiv`: the Weingarten equation.
* `TauCeti.inner_immersionShapeOperator_mfderiv_comm`: self-adjointness of the shape operator.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8.
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

/-- **The Weingarten equation.** For a metric-compatible covariant derivative, a map `f`
differentiable at `x`, a field `ν` along `f` which is normal near `x`, and a field `Y` such that
`df Y` has a differentiable reading at `x`, `⟪S_ν X, df Y⟫ = ⟪B(X, Y), ν⟫` at `x`. -/
theorem inner_immersionShapeOperator_mfderiv
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (hf : MDifferentiableAt I J f x) {ν : Π y : M, TangentSpace J (f y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hνn : ∀ᶠ y in 𝓝 x, ν y ∈ orthogonalNormalSpace I J f y)
    (X : Π y : M, TangentSpace I y) {Y : Π y : M, TangentSpace I y}
    (hY : MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (Y y)) (f x)) x) :
    inner ℝ (immersionShapeOperator cov f ν X x) (mfderiv I J f x (Y x)) =
      inner ℝ (immersionSecondFundamentalForm cov f X Y x) (ν x) := by
  have h0 : (fun y ↦ inner ℝ (ν y) (mfderiv I J f y (Y y))) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
    hνn.mono fun y hy ↦ inner_coe_orthogonalNormalSpace_mfderiv ⟨_, hy⟩ (Y y)
  have hd := hcov.mvfderiv_inner_alongMap hf hν hY (X x)
  rw [h0.mvfderiv_eq, mvfderiv_const, zero_apply] at hd
  have hνx : ν x ∈ orthogonalNormalSpace I J f x := hνn.self_of_nhds
  have hN : inner ℝ (immersionNormalConnection cov f ν X x) (mfderiv I J f x (Y x)) = 0 :=
    inner_coe_orthogonalNormalSpace_mfderiv ⟨_, immersionNormalConnection_mem ν X x⟩ (Y x)
  rw [← neg_immersionShapeOperator_add_immersionNormalConnection, inner_add_left, inner_neg_left,
    hN, real_inner_comm _ (ν x), ← inner_immersionSecondFundamentalForm_of_mem X Y hνx] at hd
  linarith

/-- **The shape operator is self-adjoint.** For a metric-compatible torsion-free covariant
derivative (the Levi-Civita connection), a map `f` which is `C²` at `x`, a field `ν` along `f`
normal near `x`, and vector fields `X`, `Y` differentiable at `x` such that `df X` and `df Y` have
differentiable readings at `x`, `⟪S_ν X, df Y⟫ = ⟪df X, S_ν Y⟫` at `x`. -/
theorem inner_immersionShapeOperator_mfderiv_comm [CompleteSpace E] [IsManifold I 2 M]
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (ht : cov.IsTorsionFree) (hf : ContMDiffAt I J 2 f x)
    {ν : Π y : M, TangentSpace J (f y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hνn : ∀ᶠ y in 𝓝 x, ν y ∈ orthogonalNormalSpace I J f y) {X Y : Π y : M, TangentSpace I y}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hdX : MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (X y)) (f x)) x)
    (hdY : MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (Y y)) (f x)) x) :
    inner ℝ (immersionShapeOperator cov f ν X x) (mfderiv I J f x (Y x)) =
      inner ℝ (mfderiv I J f x (X x)) (immersionShapeOperator cov f ν Y x) := by
  have hf1 : MDifferentiableAt I J f x := hf.mdifferentiableAt (by norm_num)
  rw [inner_immersionShapeOperator_mfderiv hcov hf1 hν hνn X hdY,
    real_inner_comm (immersionShapeOperator cov f ν Y x),
    inner_immersionShapeOperator_mfderiv hcov hf1 hν hνn Y hdX,
    immersionSecondFundamentalForm_comm ht hf hX hY]

end TauCeti
