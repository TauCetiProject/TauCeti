/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic

/-!
# The Euclidean metric in polar coordinates

Polar coordinates `(u, t) ↦ e^t u` identify the cylinder `Sⁿ × ℝ` with the punctured space
(`TauCeti.sphereProdRealDiffeomorph`). This file shows that they pull the inner product of `V` back
to `e^(2 t)` times the cylinder metric `g_(Sⁿ) + dt²` over the round metric of the sphere.

## Main results

* `TauCeti.inner_mvfderiv_exp_smul_coe_sphere`: the Euclidean metric in polar coordinates.
-/

public section

noncomputable section

open Real Metric Module Bundle
open scoped ContDiff Manifold InnerProductSpace
open TauCeti.Manifold (tangentSpaceProdEquiv)

namespace TauCeti

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

end TauCeti
