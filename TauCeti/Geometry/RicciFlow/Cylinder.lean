/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
public import TauCeti.Geometry.RicciFlow.Einstein
public import TauCeti.Geometry.RicciFlow.Prod

/-!
# The shrinking round cylinder

The round cylinder `Sⁿ(r) × ℝ` is the unit `n`-sphere with the round metric of radius `r`, times
the line with its standard metric `dt²`. Under Ricci flow the sphere factor shrinks as an Einstein
solution while the flat line stays fixed. The result is the **shrinking round cylinder**

`g(τ) = (r² - 2 (n - 1) τ) g_round + dt²`,

a Ricci flow at every time with `2 (n - 1) τ < r²`, in particular at every negative time, so it
is an ancient solution. Its Ricci tensor `(n - 1) g_round` does not depend on time and vanishes in
the direction of the line. Its scalar curvature is `n (n - 1) / (r² - 2 (n - 1) τ)`. For `n ≥ 2`
this increases strictly in forward time and tends to `+∞` at the extinction time
`r² / (2 (n - 1))`, when the sphere factor collapses.

For `n = 2` and `r = √2` the cylinder `S²(√2) × ℝ` has scalar curvature one. It is the model of
the necks of three-dimensional Ricci flow with surgery: an `ε`-neck is, after rescaling, close to
it, and a strong neck is close to the shrinking cylinder, whose scalar curvature is
`1 / (1 - τ)` for `τ < 1`.

## Main definitions

* `TauCeti.shrinkingCylinder`: the shrinking round cylinder `Sⁿ(r) × ℝ`.

## Main results

* `TauCeti.shrinkingCylinder_zero` and `TauCeti.shrinkingCylinder_inner`: the shrinking cylinder
  starts at the round cylinder `Sⁿ(r) × ℝ` and is `(r² - 2 (n - 1) τ) g_round + dt²`.
* `TauCeti.ricciTensor_shrinkingCylinder`: its Ricci tensor is `(n - 1) g_round` at every time.
* `TauCeti.hasDerivAt_inner_shrinkingCylinder`: it is a Ricci flow.
* `TauCeti.scalarCurvature_shrinkingCylinder`: its scalar curvature is
  `n (n - 1) / (r² - 2 (n - 1) τ)`.
* `TauCeti.strictMonoOn_scalarCurvature_shrinkingCylinder` and
  `TauCeti.tendsto_scalarCurvature_shrinkingCylinder_nhdsLT_atTop`: for `n ≥ 2` its scalar
  curvature increases strictly in forward time and blows up at the extinction time.
* `TauCeti.scalarCurvature_shrinkingCylinder_sqrt_two`: the shrinking cylinder `S²(√2) × ℝ` has
  scalar curvature `1 / (1 - τ)`, and scalar curvature one at time zero.

## References

* P. Topping, *Lectures on the Ricci flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), §1.2 (the round sphere and products as Ricci flows).
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Chapter 9 (necks and strong necks modelled on the round cylinder).
-/

public section

open Bundle CovariantDerivative Filter Metric Module Set
open TauCeti.Manifold (tangentSpaceProdEquiv)
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

-- With this scoped product instance of `TauCeti` available, elaborating the Levi-Civita connection
-- of an installed product metric tries to unify that metric with the scoped product instance and
-- exceeds the heartbeat limit.
attribute [-instance] Manifold.instIsContMDiffRiemannianBundleProd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {r t : ℝ}

/-- The **shrinking round cylinder** `Sⁿ(r) × ℝ` at time `τ`: the metric
`(r² - 2 (n - 1) τ) g_round + dt²` on the product of the unit `n`-sphere with the line, for
`2 (n - 1) τ < r²`. It is the cylinder over the Einstein solution of the round metric of radius
`r`, which is defined to be the round metric of radius `r` at the remaining times; see
`TauCeti.shrinkingCylinder_eq_cylinder`. -/
def shrinkingCylinder (r : ℝ) (hr : 0 < r) (τ : ℝ) :
    ContMDiffRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) ∞ (EuclideanSpace ℝ (Fin n) × ℝ)
      (fun p : sphere (0 : E) 1 × ℝ ↦ TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :=
  ((sphereRoundMetricOfRadius r hr).einsteinFlow (((n : ℝ) - 1) / r ^ 2) τ).prodTangentSpace
    ((riemannianMetricVectorSpace ℝ).ofLE le_top)

/-- The shrinking cylinder is the cylinder `g + dt²` over the Einstein solution `g` of the round
metric of radius `r`. -/
theorem shrinkingCylinder_eq_cylinder (hr : 0 < r) (τ : ℝ) :
    shrinkingCylinder (E := E) (n := n) r hr τ =
      ((sphereRoundMetricOfRadius r hr).einsteinFlow (((n : ℝ) - 1) / r ^ 2) τ).cylinder :=
  (ContMDiffRiemannianMetric.cylinder_def _).symm

/-- The positive-scale interval of the Einstein solution with constant `c / r²` is
`2 c τ < r²`. -/
private theorem two_mul_div_sq_mul_lt_one_iff (hr : 0 < r) {c τ : ℝ} :
    2 * (c / r ^ 2) * τ < 1 ↔ 2 * c * τ < r ^ 2 := by
  rw [show 2 * (c / r ^ 2) * τ = 2 * c * τ / r ^ 2 by ring, div_lt_one (by positivity)]

/-- The shrinking cylinder starts at the round cylinder `Sⁿ(r) × ℝ`. -/
@[simp]
theorem shrinkingCylinder_zero (hr : 0 < r) :
    shrinkingCylinder (E := E) (n := n) r hr 0 = (sphereRoundMetricOfRadius r hr).cylinder := by
  simp [shrinkingCylinder_eq_cylinder]

/-- The shrinking cylinder at a time `τ` with `2 (n - 1) τ < r²` is the metric
`(r² - 2 (n - 1) τ) g_round + dt²`. -/
theorem shrinkingCylinder_inner (hr : 0 < r) (ht : 2 * ((n : ℝ) - 1) * t < r ^ 2)
    (p : sphere (0 : E) 1 × ℝ) (u v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    (shrinkingCylinder r hr t).inner p u v =
      (r ^ 2 - 2 * ((n : ℝ) - 1) * t) *
          inner ℝ (tangentSpaceProdEquiv p u).1 (tangentSpaceProdEquiv p v).1 +
        NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p u).2 *
          NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v).2 := by
  rw [shrinkingCylinder_eq_cylinder, ContMDiffRiemannianMetric.cylinder_inner,
    ContMDiffRiemannianMetric.einsteinFlow_inner ((two_mul_div_sq_mul_lt_one_iff hr).2 ht)]
  simp only [smul_apply, sphereRoundMetricOfRadius_inner, smul_eq_mul]
  field_simp

/-- **The Ricci tensor of the shrinking cylinder** is `(n - 1) g_round` at every time: the round
sphere factor contributes `(n - 1) / ρ²` times its metric `ρ² g_round`, and the line nothing. -/
theorem ricciTensor_shrinkingCylinder (hr : 0 < r) (p : sphere (0 : E) 1 × ℝ)
    (u v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    letI : RiemannianBundle (fun q : sphere (0 : E) 1 × ℝ ↦ TangentSpace ((𝓡 n).prod 𝓘(ℝ)) q) :=
      ⟨(shrinkingCylinder r hr t).toRiemannianMetric⟩
    (leviCivitaConnection ((𝓡 n).prod 𝓘(ℝ)) (sphere (0 : E) 1 × ℝ)).ricciTensor p u v =
      ((n : ℝ) - 1) * inner ℝ (tangentSpaceProdEquiv p u).1 (tangentSpaceProdEquiv p v).1 := by
  rw [shrinkingCylinder,
    ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_prodTangentSpace,
    ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_einsteinFlow,
    ricciTensor_sphereRoundMetricOfRadius hr,
    ricciTensor_eq_zero_of_finrank_le_one _ _ (by simp)]
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul, LinearMap.zero_apply,
    add_zero, ContMDiffRiemannianMetric.inner_riemannianBundle, sphereRoundMetricOfRadius_inner]
  field_simp

/-- **The shrinking cylinder is a Ricci flow.** At every time `t` with `2 (n - 1) t < r²` the
shrinking cylinder satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at every point. -/
theorem hasDerivAt_inner_shrinkingCylinder (hr : 0 < r) (ht : 2 * ((n : ℝ) - 1) * t < r ^ 2)
    (p : sphere (0 : E) 1 × ℝ) (u v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    HasDerivAt (fun τ ↦ (shrinkingCylinder r hr τ).inner p u v)
      (-2 * (letI : RiemannianBundle (fun q : sphere (0 : E) 1 × ℝ ↦
            TangentSpace ((𝓡 n).prod 𝓘(ℝ)) q) := ⟨(shrinkingCylinder r hr t).toRiemannianMetric⟩;
        (leviCivitaConnection ((𝓡 n).prod 𝓘(ℝ)) (sphere (0 : E) 1 × ℝ)).ricciTensor p u v)) t := by
  have ht' := (two_mul_div_sq_mul_lt_one_iff hr).2 ht
  have hs : IsOpen {τ : ℝ | 2 * (((n : ℝ) - 1) / r ^ 2) * τ < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  -- The sphere factor is an Einstein solution and the line factor is stationary.
  refine (ContMDiffRiemannianMetric.hasDerivWithinAt_inner_prodTangentSpace_neg_two_mul_ricciTensor
    (g₂ := fun _ ↦ (riemannianMetricVectorSpace ℝ).ofLE le_top)
    (fun u v ↦ (ContMDiffRiemannianMetric.hasDerivAt_inner_einsteinFlow ht'
      (ricciTensor_sphereRoundMetricOfRadius hr p.1) u v).hasDerivWithinAt)
    (fun u v ↦ hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_of_finrank_le_one
      (by simp) u v) u v).hasDerivAt (hs.mem_nhds ht')

/-- **The scalar curvature of the shrinking cylinder** at a time `t` with `2 (n - 1) t < r²` is
`n (n - 1) / (r² - 2 (n - 1) t)`, the scalar curvature of its sphere factor. -/
theorem scalarCurvature_shrinkingCylinder (hr : 0 < r) (ht : 2 * ((n : ℝ) - 1) * t < r ^ 2)
    (p : sphere (0 : E) 1 × ℝ) :
    (shrinkingCylinder (n := n) r hr t).scalarCurvature p =
      n * ((n : ℝ) - 1) / (r ^ 2 - 2 * ((n : ℝ) - 1) * t) := by
  have : r ^ 2 - 2 * ((n : ℝ) - 1) * t ≠ 0 := (sub_pos.2 ht).ne'
  rw [shrinkingCylinder_eq_cylinder, ContMDiffRiemannianMetric.scalarCurvature_cylinder,
    ContMDiffRiemannianMetric.scalarCurvature_einsteinFlow_of_ricciTensor_eq_smul_inner
      ((two_mul_div_sq_mul_lt_one_iff hr).2 ht) (ricciTensor_sphereRoundMetricOfRadius hr p.1),
    finrank_euclideanSpace_fin]
  field_simp

/-- **The scalar curvature of the shrinking cylinder increases.** For `n ≥ 2`, at every point the
scalar curvature of the shrinking cylinder increases strictly in forward time on the interval
`2 (n - 1) τ < r²` where it is a Ricci flow. -/
theorem strictMonoOn_scalarCurvature_shrinkingCylinder (hr : 0 < r) (hn : 2 ≤ n)
    (p : sphere (0 : E) 1 × ℝ) :
    StrictMonoOn (fun τ ↦ (shrinkingCylinder (n := n) r hr τ).scalarCurvature p)
      {τ | 2 * ((n : ℝ) - 1) * τ < r ^ 2} := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  intro a (ha : 2 * ((n : ℝ) - 1) * a < r ^ 2) b (hb : 2 * ((n : ℝ) - 1) * b < r ^ 2) hab
  dsimp only
  rw [scalarCurvature_shrinkingCylinder hr ha, scalarCurvature_shrinkingCylinder hr hb]
  exact div_lt_div_of_pos_left (by nlinarith) (sub_pos.2 hb) (by nlinarith)

/-- **Extinction of the shrinking cylinder.** For `n ≥ 2`, at every point the scalar curvature of
the shrinking cylinder tends to `+∞` as `τ` tends from below to the extinction time
`r² / (2 (n - 1))`. -/
theorem tendsto_scalarCurvature_shrinkingCylinder_nhdsLT_atTop (hr : 0 < r) (hn : 2 ≤ n)
    (p : sphere (0 : E) 1 × ℝ) :
    Tendsto (fun τ ↦ (shrinkingCylinder (n := n) r hr τ).scalarCurvature p)
      (𝓝[<] (r ^ 2 / (2 * ((n : ℝ) - 1)))) atTop := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < ((n : ℝ) - 1) / r ^ 2 := div_pos (by linarith) (by positivity)
  have hT : (2 * (((n : ℝ) - 1) / r ^ 2))⁻¹ = r ^ 2 / (2 * ((n : ℝ) - 1)) := by
    field_simp
  simp only [shrinkingCylinder_eq_cylinder, ContMDiffRiemannianMetric.scalarCurvature_cylinder]
  rw [← hT]
  refine ContMDiffRiemannianMetric.tendsto_scalarCurvature_einsteinFlow_nhdsLT_atTop hc ?_
    (ricciTensor_sphereRoundMetricOfRadius hr p.1)
  rw [finrank_euclideanSpace_fin]
  omega

/-- **The cylinder `S²(√2) × ℝ` and its shrinking flow.** The shrinking cylinder over the
two-sphere of radius `√2` has scalar curvature `1 / (1 - τ)` at every time `τ < 1`; in particular
the round cylinder `S²(√2) × ℝ` has scalar curvature one. -/
theorem scalarCurvature_shrinkingCylinder_sqrt_two [Fact (finrank ℝ E = 2 + 1)] (ht : t < 1)
    (p : sphere (0 : E) 1 × ℝ) :
    (shrinkingCylinder (n := 2) √2 (by positivity) t).scalarCurvature p = (1 - t)⁻¹ := by
  have : 1 - t ≠ 0 := sub_ne_zero.2 ht.ne'
  rw [scalarCurvature_shrinkingCylinder _ (by norm_num; linarith), Real.sq_sqrt zero_le_two]
  norm_num
  rw [show (2 : ℝ) - 2 * t = 2 * (1 - t) by ring]
  field_simp

end TauCeti
