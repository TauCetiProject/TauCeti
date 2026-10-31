/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Torpedo
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius

/-!
# Surgery handles of positive scalar curvature

In the Gromov–Lawson surgery construction, a sphere `S^k` with trivial normal bundle in an
`n`-manifold of positive scalar curvature, of codimension `q = n - k ≥ 3`, is removed together with
a tubular neighbourhood `S^k × D^q`, and the handle `D^(k + 1) × S^(q - 1)` is glued in along the
common boundary `S^k × S^(q - 1)`. After the metric near `S^k` has been deformed to a product
`(g_(S^k) + dt²) + δ² g_(S^(q - 1))` near the boundary, the handle carries the product of the
torpedo metric on `ℝ^(k + 1)` with the round metric of radius `δ` on `S^(q - 1)`. This file
constructs the handle side of the gluing.

The torpedo metric has nonnegative scalar curvature in every dimension, so its product with any
metric of positive scalar curvature, such as a round sphere of dimension at least `2`, has positive
scalar curvature (`TauCeti.hasPositiveScalarCurvature_torpedoMetric_prodTangentSpace`). This covers
the handles of low index `k + 1 ≤ 2`, where the torpedo metric itself is not of positive scalar
curvature.

To match the handle with the deformed metric, the torpedo metric is read in polar coordinates
`(u, t) ↦ e^t u` on `Sⁿ × ℝ`, the map underlying `TauCeti.sphereProdRealDiffeomorph`. Where
`t ≥ -1` it is exactly the cylinder metric `g_(Sⁿ) + dt²`
(`TauCeti.torpedoMetric_inner_mfderiv_exp_smul_coe_sphere_of_le`). Hence on its collar the handle
metric is the product `(g_(Sⁿ) + dt²) × g`.

## Main results

* `TauCeti.hasPositiveScalarCurvature_torpedoMetric_prodTangentSpace_sphereRoundMetricOfRadius`:
  the handle metric on `D^(k + 1) × S^(q - 1)` has positive scalar curvature when `q ≥ 3`.
* `TauCeti.torpedoMetric_prodTangentSpace_inner_mfderiv_prodMap_of_le`: the handle metric is a
  product on its collar.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434.
* M. Walsh, *Metrics of positive scalar curvature and generalised Morse functions, Part I*,
  Mem. Amer. Math. Soc. 209 (2011), no. 983, Section 1.
-/

public section

noncomputable section

open Real Set Metric Module Bundle
open scoped ContDiff Manifold InnerProductSpace
open TauCeti.Manifold (tangentSpaceProdEquiv)

namespace TauCeti

section Handle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  {g : ContMDiffRiemannianMetric J ∞ E (fun x : N ↦ TangentSpace J x)}

section ScalarCurvature

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ E] [T2Space N]

/-- **The Gromov–Lawson handle metric.** For `m ≥ 2` and every radius `δ > 0`, the product of the
torpedo metric on `F` with the round metric of radius `δ` on `Sᵐ` has positive scalar curvature.
With `F = ℝ^(k + 1)` and `m = q - 1`, this is the metric on the handle `D^(k + 1) × S^(q - 1)` glued
in by surgery along `S^k` in codimension `q ≥ 3`. -/
theorem hasPositiveScalarCurvature_torpedoMetric_prodTangentSpace_sphereRoundMetricOfRadius
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m : ℕ}
    [Fact (finrank ℝ V = m + 1)] (hm : 2 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    ((torpedoMetric F).prodTangentSpace
      (sphereRoundMetricOfRadius (E := V) (n := m) δ hδ)).HasPositiveScalarCurvature :=
  hasPositiveScalarCurvature_torpedoMetric_prodTangentSpace
    (hasPositiveScalarCurvature_sphereRoundMetricOfRadius hδ hm)

end ScalarCurvature

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

/-- **The collar of a handle.** On the cylindrical end `t ≥ -1` of the torpedo factor, the product
of the torpedo metric on `V` with a metric `g` on `N`, read in polar coordinates `y = e^t u` on the
first factor, is the product of the cylinder metric `g_(Sⁿ) + dt²` with `g`. For the handle
`D^(k + 1) × S^(q - 1)` this is the product collar `(S^k × ℝ) × S^(q - 1)` along which the handle
is glued. -/
theorem torpedoMetric_prodTangentSpace_inner_mfderiv_prodMap_of_le
    {q : (sphere (0 : V) 1 × ℝ) × N} (hq : -1 ≤ q.1.2)
    (v w : TangentSpace (((𝓡 n).prod 𝓘(ℝ)).prod J) q) :
    ((torpedoMetric V).prodTangentSpace g).inner
        (Prod.map (fun p : sphere (0 : V) 1 × ℝ ↦ exp p.2 • (p.1 : V)) id q)
        (mfderiv (((𝓡 n).prod 𝓘(ℝ)).prod J) (𝓘(ℝ, V).prod J)
          (Prod.map (fun p : sphere (0 : V) 1 × ℝ ↦ exp p.2 • (p.1 : V)) id) q v)
        (mfderiv (((𝓡 n).prod 𝓘(ℝ)).prod J) (𝓘(ℝ, V).prod J)
          (Prod.map (fun p : sphere (0 : V) 1 × ℝ ↦ exp p.2 • (p.1 : V)) id) q w) =
      (((sphereRoundMetric (E := V)).ofLE le_top).cylinder.prodTangentSpace g).inner q v w := by
  have hP : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V)
      (fun p : sphere (0 : V) 1 × ℝ ↦ exp p.2 • (p.1 : V)) q.1 :=
    ((Real.differentiable_exp.mdifferentiable _).comp q.1 mdifferentiableAt_snd).smul
      (((contMDiff_coe_sphere (E := V) (n := n) (m := 1) q.1.1).mdifferentiableAt
        one_ne_zero).comp q.1 mdifferentiableAt_fst)
  have hd (u : TangentSpace (((𝓡 n).prod 𝓘(ℝ)).prod J) q) :=
    TauCeti.Manifold.mfderiv_prodMap_apply hP mdifferentiableAt_id (tangentSpaceProdEquiv q u)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hd
  rw [ContMDiffRiemannianMetric.prodTangentSpace_inner,
    ContMDiffRiemannianMetric.prodTangentSpace_inner, hd, hd]
  -- The point `Prod.map P id q` is `(P q.1, id q.2)` by definition, and both identifications of
  -- the product tangent space are the identity.
  have hpt (a : TangentSpace 𝓘(ℝ, V) (exp q.1.2 • (q.1.1 : V)) × TangentSpace J q.2) :
      tangentSpaceProdEquiv (Prod.map (fun p : sphere (0 : V) 1 × ℝ ↦ exp p.2 • (p.1 : V)) id q)
        ((tangentSpaceProdEquiv (exp q.1.2 • (q.1.1 : V), id q.2)).symm a) = a :=
    (TauCeti.Manifold.tangentSpaceProdEquiv_apply _ _).trans
      (TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply (exp q.1.2 • (q.1.1 : V), id q.2) a)
  simp only [hpt, mfderiv_id, ContinuousLinearMap.id_apply]
  exact congrArg (· + _) (torpedoMetric_inner_mfderiv_exp_smul_coe_sphere_of_le hq _ _)

end Handle

end TauCeti
