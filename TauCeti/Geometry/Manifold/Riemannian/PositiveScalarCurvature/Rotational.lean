/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Radial

/-!
# Rotationally symmetric metrics and the Gromov–Lawson bending term

A rotationally symmetric metric on the cylinder `Sⁿ × ℝ` is `e^(2 w(t)) (g_(Sⁿ) + dt²)` for a
smooth *profile* `w : ℝ → ℝ`. In the arclength coordinate `σ = ∫ e^w dt` it is the warped product
`dσ² + f(σ)² g_(Sⁿ)` with `f = e^w`. Its scalar curvature is

`n e^(-2 w) ((n - 1) (1 - w'²) - 2 w'')`.

Under polar coordinates `y = e^t u` the cylinder is the punctured space `V ∖ {0}` of an inner
product space `V` of dimension `n + 1`, and the metric is the Euclidean metric multiplied by
`e^(2 (w(log ‖y‖) - log ‖y‖))`. The formula is therefore an instance of the conformal change of
scalar curvature, applied to a radial conformal exponent
(`TauCeti.scalarCurvature_rescale_exp_radial`); locality and diffeomorphism invariance of scalar
curvature transport it to the cylinder.

In the Gromov–Lawson surgery construction, a curve `u ↦ (r u, h u)` in the half-plane `r > 0` with
velocity `r u (-cos θ u, sin θ u)` sweeps out the hypersurface `{(r(u) x, h(u)) | x ∈ S^(q - 1)}`
of `ℝ^q × ℝ`, and its induced metric is `r² (g_(S^(q - 1)) + du²)`: the profile is `w = log r`,
with `w' = -cos θ`. The curve has curvature `k = θ' / r`, and the scalar curvature is the bending
term `(q - 1) (q - 2) sin² θ / r² - 2 (q - 1) k sin θ / r` of the construction. This is the case
of a point in flat space; around a sphere `S^k` in a curved manifold the bending term is the
leading part of the scalar curvature of the bent tube.

## Main definitions

* `TauCeti.rotationalMetric`: the rotationally symmetric metric `e^(2 w(t)) (g_(Sⁿ) + dt²)` on
  `Sⁿ × ℝ`.

## Main results

* `TauCeti.inner_mvfderiv_exp_smul_coe_sphere`: polar coordinates pull the Euclidean metric back to
  `e^(2 t) (g_(Sⁿ) + dt²)`.
* `TauCeti.scalarCurvature_rotationalMetric`: the scalar curvature of a rotationally symmetric
  metric.
* `TauCeti.inner_mvfderiv_smul_coe_sphere_add_mul_mvfderiv`: a curve with speed equal to its radius
  sweeps out a hypersurface with induced metric `r² (g_(Sⁿ) + du²)`.
* `TauCeti.scalarCurvature_rotationalMetric_log`: the Gromov–Lawson bending term is the scalar
  curvature of that induced metric.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), the rotationally
  symmetric metrics `dr² + f(r)² g_(Sⁿ)` of Chapter 4.
-/

public section

noncomputable section

open Real Set Metric Module Bundle Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace TauCeti

/-! ### Polar coordinates -/

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
  rw [inner_mvfderiv_smul_coe_sphere p (differentiable_exp p.2), Real.deriv_exp,
    ContMDiffRiemannianMetric.cylinder_inner, ContMDiffRiemannianMetric.ofLE_inner,
    sphereRoundMetric_inner, two_mul, exp_add]
  ring

end Polar

/-! ### Rotationally symmetric metrics on the cylinder -/

section Rotational

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

/-- The **rotationally symmetric metric** `e^(2 w(t)) (g_(Sⁿ) + dt²)` on the cylinder `Sⁿ × ℝ`
with smooth profile `w`. In the arclength coordinate `σ = ∫ e^w dt` it is the warped product
`dσ² + f(σ)² g_(Sⁿ)` with `f = e^w`. -/
def rotationalMetric {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    ContMDiffRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) ∞ (EuclideanSpace ℝ (Fin n) × ℝ)
      (fun p : sphere (0 : V) 1 × ℝ ↦ TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :=
  ((sphereRoundMetric (E := V)).ofLE le_top).cylinder.rescale (fun p ↦ exp (2 * w p.2))
    ((contDiff_const.mul hw).exp.contMDiff.comp contMDiff_snd) fun _ ↦ exp_pos _

variable {V}

/-- The rotationally symmetric metric is `e^(2 w(t))` times the cylinder metric. -/
@[simp]
theorem rotationalMetric_inner {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (p : sphere (0 : V) 1 × ℝ)
    (v v' : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    (rotationalMetric (n := n) V hw).inner p v v' =
      exp (2 * w p.2) * ((sphereRoundMetric (E := V)).ofLE le_top).cylinder.inner p v v' := by
  rw [rotationalMetric, ContMDiffRiemannianMetric.rescale_inner]

/-- **Scalar curvature of a rotationally symmetric metric.** The metric
`e^(2 w(t)) (g_(Sⁿ) + dt²)` on `Sⁿ × ℝ` has scalar curvature
`n e^(-2 w(t)) ((n - 1) (1 - w'(t)²) - 2 w''(t))` at `(u, t)`. -/
theorem scalarCurvature_rotationalMetric {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (p : sphere (0 : V) 1 × ℝ) :
    (rotationalMetric (n := n) V hw).scalarCurvature p =
      n * exp (-2 * w p.2) * ((n - 1) * (1 - deriv w p.2 ^ 2) - 2 * deriv (deriv w) p.2) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  -- Near `p`, the metric is the pullback along polar coordinates `P` of the Euclidean metric
  -- multiplied by `e^(2 φ)`, with `φ` the radial exponent of `w`, cut off near the origin.
  obtain ⟨φ, hφ, hφw⟩ := exists_contDiff_eq_comp_log_norm_sub_log_norm (E := V) hw (p.2 - 1)
  set G := ((riemannianMetricVectorSpace V).ofLE le_top).rescale (fun z ↦ exp (2 * φ z))
    (contDiff_const.mul hφ).exp.contMDiff fun _ ↦ exp_pos _
  set P : sphere (0 : V) 1 × ℝ → V := fun q ↦ exp q.2 • (q.1 : V)
  have hP : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V) (∞ + 1) P := contMDiff_exp_smul_coe_sphere
  have hnorm (q : sphere (0 : V) 1 × ℝ) : ‖P q‖ = exp q.2 := by
    simp only [P, norm_smul, norm_eq_of_mem_sphere q.1, mul_one, norm_of_nonneg (exp_pos _).le]
  have hloc : ∀ᶠ q in 𝓝 p, (rotationalMetric (n := n) V hw).inner q =
      (G.pullback P hP fun q ↦ (isInvertible_mfderiv_exp_smul_coe_sphere q).injective).inner q := by
    filter_upwards [(continuous_snd.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (show p.2 - 1 < p.2 by linarith : p ∈ Prod.snd ⁻¹' Ioi (p.2 - 1))] with q hq
    ext v v'
    rw [rotationalMetric_inner, ContMDiffRiemannianMetric.pullback_inner,
      ContMDiffRiemannianMetric.rescale_inner, ContMDiffRiemannianMetric.ofLE_inner]
    have h : ⟪mvfderiv ((𝓡 n).prod 𝓘(ℝ)) P q v, mvfderiv ((𝓡 n).prod 𝓘(ℝ)) P q v'⟫_ℝ =
        exp (2 * q.2) * ((sphereRoundMetric (E := V)).ofLE le_top).cylinder.inner q v v' :=
      inner_mvfderiv_exp_smul_coe_sphere q v v'
    -- The standard metric of `V` is its inner product, read through the identification of each
    -- tangent space of `V` with `V`, as in `TauCeti.Manifold.inner_tangentSpace_vectorSpace`.
    change _ = exp (2 * φ (P q)) * ⟪mvfderiv ((𝓡 n).prod 𝓘(ℝ)) P q v,
      mvfderiv ((𝓡 n).prod 𝓘(ℝ)) P q v'⟫_ℝ
    rw [h, hφw _ (by rw [hnorm]; exact exp_lt_exp.2 hq), hnorm, log_exp, ← mul_assoc, ← exp_add]
    ring_nf
  rw [ContMDiffRiemannianMetric.scalarCurvature_eq_of_eventually_inner_eq hloc,
    ContMDiffRiemannianMetric.scalarCurvature_pullback_of_isInvertible G hP
      isInvertible_mfderiv_exp_smul_coe_sphere]
  -- The radial formula applies at `P p`, where `φ` is the radial exponent of `w`.
  have heq : φ =ᶠ[𝓝 (P p)] fun z ↦ w (log ‖z‖) - log ‖z‖ := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (show exp (p.2 - 1) <
      ‖P p‖ by rw [hnorm]; exact exp_lt_exp.2 (by linarith))] with z hz using hφw z hz
  rw [scalarCurvature_rescale_exp_radial hφ (norm_pos_iff.1 (hnorm p ▸ exp_pos _))
      (by rw [hnorm, log_exp]; exact (hw.of_le (by simp)).contDiffAt) heq, hnorm, log_exp,
    (Fact.out : finrank ℝ V = n + 1)]
  push_cast
  ring

end Rotational

/-! ### The Gromov–Lawson bending term -/

section Bending

open TauCeti.Manifold (tangentSpaceProdEquiv)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

/-- **The hypersurface swept out by a bending curve.** Let `t ↦ (r t, h t)` be a curve in the
half-plane `r > 0` with velocity `r t (-cos θ t, sin θ t)`, so that its speed is its radius. The
hypersurface `{(r(t) u, h(t)) | u ∈ Sⁿ}` of `V × ℝ`, parametrised by `(u, t) ↦ (r(t) u, h(t))`,
has induced metric `r(t)² (g_(Sⁿ) + dt²)`: the rotationally symmetric metric with profile
`log r`. The Euclidean metric of `V × ℝ` pairs the `V`-components by the inner product of `V` and
multiplies the `ℝ`-components. Only the derivatives of `r` and `h` at `t` enter at `(u, t)`. -/
theorem inner_mvfderiv_smul_coe_sphere_add_mul_mvfderiv {r h θ : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hr_pos : ∀ t, 0 < r t) (p : sphere (0 : V) 1 × ℝ)
    (hr' : HasDerivAt r (-(r p.2 * cos (θ p.2))) p.2) (hh' : HasDerivAt h (r p.2 * sin (θ p.2)) p.2)
    (v v' : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    ⟪mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ r q.2 • (q.1 : V)) p v,
        mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ r q.2 • (q.1 : V)) p v'⟫_ℝ +
      mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ h q.2) p v *
        mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ h q.2) p v' =
      (rotationalMetric (n := n) V (hr.log fun t ↦ (hr_pos t).ne')).inner p v v' := by
  have hexp : exp (2 * log (r p.2)) = r p.2 ^ 2 := by
    rw [mul_comm, exp_mul, exp_log (hr_pos p.2), rpow_two]
  have hh (x : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
      mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ h q.2) p x =
        NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p x).2 * deriv h p.2 := by
    rw [Manifold.tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_snd_apply_eq_smul_deriv h p x
  rw [inner_mvfderiv_smul_coe_sphere p hr'.differentiableAt, hh, hh, rotationalMetric_inner,
    ContMDiffRiemannianMetric.cylinder_inner, ContMDiffRiemannianMetric.ofLE_inner,
    sphereRoundMetric_inner, hexp, hr'.deriv, hh'.deriv]
  linear_combination (r p.2 ^ 2 * NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v).2 *
    NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v').2) * sin_sq_add_cos_sq (θ p.2)

/-- **The Gromov–Lawson bending term.** Let `r > 0` be smooth with `r' = -r cos θ`: the radius of a
curve in the half-plane, parametrised with speed `r`, whose velocity makes the angle `θ` with the
`-r` direction. The rotationally symmetric metric `r(t)² (g_(Sⁿ) + dt²)`, the induced metric of the
hypersurface swept out by the curve
(`TauCeti.inner_mvfderiv_smul_coe_sphere_add_mul_mvfderiv`), has scalar curvature
`n (n - 1) sin² θ / r² - 2 n k sin θ / r`, where `k = θ' / r` is the curvature of the curve. With
`n = q - 1` this is the bending term of the Gromov–Lawson surgery construction in codimension `q`.
At `(u, t)` the equation `r' = -r cos θ` is only needed near `t`. -/
theorem scalarCurvature_rotationalMetric_log {r θ : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hr_pos : ∀ t, 0 < r t) (p : sphere (0 : V) 1 × ℝ)
    (hr' : ∀ᶠ t in 𝓝 p.2, HasDerivAt r (-(r t * cos (θ t))) t) (hθ : DifferentiableAt ℝ θ p.2) :
    (rotationalMetric (n := n) V (hr.log fun t ↦ (hr_pos t).ne')).scalarCurvature p =
      n * (n - 1) * sin (θ p.2) ^ 2 / r p.2 ^ 2 -
        2 * n * (deriv θ p.2 / r p.2) * sin (θ p.2) / r p.2 := by
  have hw : deriv (fun t ↦ log (r t)) =ᶠ[𝓝 p.2] fun t ↦ -cos (θ t) := by
    filter_upwards [hr'] with t ht
    rw [(ht.log (hr_pos t).ne').deriv]
    field_simp [(hr_pos t).ne']
  have hw' : deriv (fun t ↦ -cos (θ t)) p.2 = sin (θ p.2) * deriv θ p.2 := by
    have hd : HasDerivAt (fun t ↦ -cos (θ t)) (-(-sin (θ p.2) * deriv θ p.2)) p.2 :=
      hθ.hasDerivAt.cos.neg
    rw [hd.deriv]
    ring
  have hexp : exp (-2 * log (r p.2)) = (r p.2 ^ 2)⁻¹ := by
    rw [mul_comm, exp_mul, exp_log (hr_pos p.2), rpow_neg (hr_pos p.2).le, rpow_two]
  rw [scalarCurvature_rotationalMetric, hw.eq_of_nhds, hw.deriv_eq, hw', hexp]
  have hr₀ := (hr_pos p.2).ne'
  field_simp
  linear_combination (-(n * (n - 1) : ℝ)) * sin_sq_add_cos_sq (θ p.2)

end Bending

end TauCeti
