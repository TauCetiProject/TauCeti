/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.SecondFundamentalForm.Norm
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

For a map which is `C²` at `x`, extending tangent vectors at `x` to local fields gives the
pointwise form `⟪∇_v ν, df w⟫ = -⟪B_x(v, w), ν⟫` with the pointwise second fundamental form
`B_x` (`TauCeti.immersionSecondFundamentalFormAt`).

## Main results

* `TauCeti.inner_immersionShapeOperator_mfderiv`: the Weingarten equation.
* `TauCeti.inner_immersionShapeOperator_mfderiv_comm`: self-adjointness of the shape operator.
* `TauCeti.inner_alongMap_mfderiv_of_eventually_mem`: the pointwise Weingarten equation.

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

/-- **The Weingarten equation, pointwise.** For a metric-compatible connection, a map `f` which is
`C²` at `x` and a field `ν` along `f` which is normal near `x` with differentiable reading at `x`,
`⟪∇_v ν, df w⟫ = -⟪B_x(v, w), ν⟫`. -/
theorem inner_alongMap_mfderiv_of_eventually_mem [FiniteDimensional ℝ E] [IsManifold I 2 M]
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (hf : ContMDiffAt I J 2 f x) {ν : Π y : M, TangentSpace J (f y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hνn : ∀ᶠ y in 𝓝 x, ν y ∈ orthogonalNormalSpace I J f y) (v w : TangentSpace I x) :
    inner ℝ (cov.alongMap I f ν x v) (mfderiv I J f x w) =
      -inner ℝ (immersionSecondFundamentalFormAt cov f x v w) (ν x) := by
  set V : Π y : M, TangentSpace I y := FiberBundle.extend E v
  set W : Π y : M, TangentSpace I y := FiberBundle.extend E w
  have hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E w
  have hdW : MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (W y)) (f x)) x := by
    have h := hf.contMDiffAt_tangentMap (X := (W x : TangentBundle I M)) (m := 1) (by norm_num)
    exact mdifferentiableAt_sectionCoord f _ ((h.mdifferentiableAt one_ne_zero).comp
      x hW) (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f x))
  have hB : immersionSecondFundamentalFormAt cov f x v w =
      immersionSecondFundamentalForm cov f V W x := by
    simpa only [V, W, FiberBundle.extend_apply_self] using
      immersionSecondFundamentalFormAt_apply hf (FiberBundle.mdifferentiableAt_extend I E v) hW
  have hN : inner ℝ (immersionNormalConnection cov f ν V x) (mfderiv I J f x (W x)) = 0 :=
    inner_coe_orthogonalNormalSpace_mfderiv ⟨_, immersionNormalConnection_mem ν V x⟩ (W x)
  have h := inner_immersionShapeOperator_mfderiv hcov (hf.mdifferentiableAt (by norm_num)) hν
    hνn V hdW
  have hv : V x = v := FiberBundle.extend_apply_self E v
  have hw : W x = w := FiberBundle.extend_apply_self E w
  rw [hB, ← h, ← hv, ← hw, ← neg_immersionShapeOperator_add_immersionNormalConnection ν V x]
  simp [inner_add_left, hN]

end TauCeti
