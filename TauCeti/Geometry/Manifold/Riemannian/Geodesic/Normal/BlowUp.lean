/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.BlowUp
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Metric

/-!
# Blowing up a metric in normal coordinates

Let `U` be a normal domain at a point `p` of a Riemannian manifold `M`. Pulling the metric `g`
back along the exponential map gives the metric `g` read in normal coordinates,
`TauCeti.Manifold.IsNormalDomain.normalCoordinateMetric`, a metric on the open set `U` of the
tangent space `T_p M`. Since `U` is star-shaped about the origin, this metric can be blown up
(`Bundle.ContMDiffRiemannianMetric.blowUp`): for `t ∈ (0, 1]` the blow-up at scale `t` is the
metric `t⁻² μ_t^* exp_p^* g` of the magnified ball `v ↦ exp_p (t • v)`, and its scalar curvature at
`v` is `t² Scal(g)(exp_p (t • v))`. Since the differential of `exp_p` at the origin is the
identity, the blow-up at scale `0` is the constant metric `g_p` of the Euclidean space `T_p M`.

The blow-up is continuous in `t ∈ [0, 1]` for every chart `Cᵏ` topology
(`Bundle.ContMDiffRiemannianMetric.continuous_blowUp_chartCk`). So a ball around `p` of radius
`t`, magnified to unit size, carries a metric that converges to the flat metric `g_p` as `t → 0`,
uniformly on compact sets with derivatives of every order. This is the comparison with the flat
model at a point used by the Gromov–Lawson construction for surgery on a point, that is, for
connected sums.

## Main results

* `TauCeti.Manifold.IsNormalDomain.blowUp_normalCoordinateMetric_zero_inner`: the blow-up at
  scale `0` is the inner product `g_p` of `T_p M`.
* `TauCeti.Manifold.IsNormalDomain.scalarCurvature_blowUp_normalCoordinateMetric`: for `t > 0` the
  blow-up at scale `t` has scalar curvature `t² Scal(g)(exp_p (t • v))` at `v`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
-/

public section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

namespace IsNormalDomain

variable {p : M} {U : Set (TangentSpace I p)}

/-- At scale `0`, the blow-up of the metric in normal coordinates is the constant metric given by
the inner product of `T_p M`. -/
theorem blowUp_normalCoordinateMetric_zero_inner [T2Space M] [I.Boundaryless]
    (hU : IsNormalDomain I M p U) (v : hU.opens) (u w : TangentSpace I p) :
    (hU.normalCoordinateMetric.blowUp hU.starConvex_opens 0).inner v u w = inner ℝ u w := by
  rw [ContMDiffRiemannianMetric.blowUp_zero_inner]
  refine (normalCoordinateMetric_inner hU _ u w).trans ?_
  refine (congrArg₂ (inner ℝ) (hU.mfderiv_riemannianExp_comp_val_zero_apply u)
    (hU.mfderiv_riemannianExp_comp_val_zero_apply w)).trans ?_
  rw [Function.comp_apply, riemannianExp_zero]

/-- For `t > 0`, the blow-up at scale `t` of the metric in normal coordinates has scalar
curvature `t² Scal(g)(exp_p (t • v))` at `v`. -/
theorem scalarCurvature_blowUp_normalCoordinateMetric [T2Space M] (hU : IsNormalDomain I M p U)
    (t : Icc (0 : ℝ) 1) (ht : 0 < (t : ℝ)) (v : hU.opens) :
    (hU.normalCoordinateMetric.blowUp hU.starConvex_opens t).scalarCurvature v =
      (t : ℝ) ^ 2 * (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
        (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)).scalarCurvature
          (riemannianExp I M p ((t : ℝ) • (v : TangentSpace I p))) := by
  have ht' := ContMDiffRiemannianMetric.scalarCurvature_blowUp hU.normalCoordinateMetric
    hU.starConvex_opens t ht v
  rw [ht', normalCoordinateMetric_eq_pullback,
    ContMDiffRiemannianMetric.scalarCurvature_pullback_of_isInvertible _ _
      hU.isInvertible_mfderiv_riemannianExp_comp_val, Function.comp_apply,
    StarConvex.coe_opensHomothety]

end IsNormalDomain

end TauCeti.Manifold
