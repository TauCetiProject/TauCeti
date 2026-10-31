/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Torpedo
public import TauCeti.Geometry.Manifold.Instances.Cylinder
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

The torpedo metric has nonnegative scalar curvature in every dimension
(`TauCeti.scalarCurvature_torpedoMetric_nonneg`), so its product with any metric of positive scalar
curvature, such as a round sphere of dimension at least `2`, has positive scalar curvature. This
covers the handles of low index `k + 1 ≤ 2`, where the torpedo metric itself is not of positive
scalar curvature.

To match the handle with the deformed metric, the torpedo metric is read in polar coordinates
`(u, t) ↦ e^t u` on `Sⁿ × ℝ`, the map underlying `TauCeti.sphereProdRealDiffeomorph`. These pull the
Euclidean metric back to `e^(2 t) (g_(Sⁿ) + dt²)`, so they pull the torpedo metric back to
`e^(2 w(t)) (g_(Sⁿ) + dt²)`, with `w` the torpedo profile. Where `t ≥ -1` the profile vanishes, and
the torpedo metric is exactly the cylinder metric `g_(Sⁿ) + dt²`. Hence on its collar the handle
metric is the product `(g_(Sⁿ) + dt²) × g`.

## Main results

* `TauCeti.inner_mvfderiv_exp_smul_coe_sphere`: the Euclidean metric in polar coordinates.
* `TauCeti.torpedoMetric_inner_mfderiv_exp_smul_coe_sphere`: the torpedo metric in polar
  coordinates, and `TauCeti.torpedoMetric_inner_mfderiv_exp_smul_coe_sphere_of_le`: its cylindrical
  end.
* `TauCeti.hasPositiveScalarCurvature_torpedoMetric_prodTangentSpace`: the product of the torpedo
  metric with a metric of positive scalar curvature has positive scalar curvature.
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

section Polar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

/-- **The Euclidean metric in polar coordinates.** Polar coordinates `(u, t) ↦ e^t u` pull the
inner product of `V` back to `e^(2 t)` times the cylinder metric `g_(Sⁿ) + dt²`. -/
theorem inner_mvfderiv_exp_smul_coe_sphere (p : sphere (0 : V) 1 × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    ⟪mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ exp q.2 • (q.1 : V)) p v,
      mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ exp q.2 • (q.1 : V)) p w⟫_ℝ =
      exp (2 * p.2) * ((sphereRoundMetric (E := V)).ofLE le_top).cylinder.inner p v w := by
  have hu : ⟪(p.1 : V), (p.1 : V)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p.1, one_pow]
  have h₁ : ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.1 (tangentSpaceProdEquiv p v).1,
      (p.1 : V)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact inner_coe_mvfderiv_subtypeVal_sphere p.1 _
  have h₂ := inner_coe_mvfderiv_subtypeVal_sphere p.1 (tangentSpaceProdEquiv p w).1
  rw [mvfderiv_exp_smul_coe_sphere_apply, mvfderiv_exp_smul_coe_sphere_apply,
    ContMDiffRiemannianMetric.cylinder_inner, ContMDiffRiemannianMetric.ofLE_inner,
    sphereRoundMetric_inner, two_mul, exp_add]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right, h₁, h₂,
    hu]
  ring

/-- **The torpedo metric in polar coordinates.** In the coordinates `y = e^t u`, with `t ∈ ℝ` and
`u` in the unit sphere, the torpedo metric is `e^(2 w(t)) (g_(Sⁿ) + dt²)`, where `w` is the torpedo
profile. -/
theorem torpedoMetric_inner_mfderiv_exp_smul_coe_sphere (p : sphere (0 : V) 1 × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    (torpedoMetric V).inner (exp p.2 • (p.1 : V))
        (mfderiv ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 × ℝ ↦ exp q.2 • (q.1 : V))
          p v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 × ℝ ↦ exp q.2 • (q.1 : V))
          p w) =
      exp (2 * torpedoProfile p.2) *
        ((sphereRoundMetric (E := V)).ofLE le_top).cylinder.inner p v w := by
  have hnorm : ‖exp p.2 • (p.1 : V)‖ = exp p.2 := by
    rw [norm_smul, norm_eq_of_mem_sphere p.1, mul_one, norm_of_nonneg (exp_pos _).le]
  rw [torpedoMetric_inner, NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_apply,
    ← mvfderiv_apply_eq_mfderiv_apply, ← mvfderiv_apply_eq_mfderiv_apply,
    inner_mvfderiv_exp_smul_coe_sphere, ← mul_assoc, ← exp_add, hnorm,
    torpedoExponent_of_ne_zero (exp_pos _).ne', log_exp]
  ring_nf

/-- On the cylindrical end `t ≥ -1`, the torpedo metric in polar coordinates `y = e^t u` is the
cylinder metric `g_(Sⁿ) + dt²`. -/
theorem torpedoMetric_inner_mfderiv_exp_smul_coe_sphere_of_le {p : sphere (0 : V) 1 × ℝ}
    (hp : -1 ≤ p.2) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    (torpedoMetric V).inner (exp p.2 • (p.1 : V))
        (mfderiv ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 × ℝ ↦ exp q.2 • (q.1 : V))
          p v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 × ℝ ↦ exp q.2 • (q.1 : V))
          p w) =
      ((sphereRoundMetric (E := V)).ofLE le_top).cylinder.inner p v w := by
  rw [torpedoMetric_inner_mfderiv_exp_smul_coe_sphere, torpedoProfile_of_ge hp, mul_zero, exp_zero,
    one_mul]

end Polar

section Handle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  {g : ContMDiffRiemannianMetric J ∞ E (fun x : N ↦ TangentSpace J x)}

section ScalarCurvature

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ E] [T2Space N]

/-- **Handle metrics have positive scalar curvature.** The product of the torpedo metric on `F`
with a metric `g` of positive scalar curvature has positive scalar curvature, in every dimension of
`F`: the torpedo factor contributes nonnegative scalar curvature. -/
theorem hasPositiveScalarCurvature_torpedoMetric_prodTangentSpace
    (hg : g.HasPositiveScalarCurvature) :
    ((torpedoMetric F).prodTangentSpace g).HasPositiveScalarCurvature := by
  refine (ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff _).2 fun p ↦ ?_
  rw [ContMDiffRiemannianMetric.scalarCurvature_prodTangentSpace]
  exact add_pos_of_nonneg_of_pos (scalarCurvature_torpedoMetric_nonneg p.1)
    ((ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff _).1 hg p.2)

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
