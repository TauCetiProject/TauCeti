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
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Rotationally symmetric metrics and the Gromov–Lawson bending term

A rotationally symmetric metric on the cylinder `Sⁿ × ℝ` is `e^(2 w(t)) (g_(Sⁿ) + dt²)` for a
smooth *profile* `w : ℝ → ℝ`. In the arclength coordinate `σ = ∫ e^w dt` it is the warped product
`dσ² + f(σ)² g_(Sⁿ)` with `f = e^w`. Its scalar curvature is

`n e^(-2 w) ((n - 1) (1 - w'²) - 2 w'')`.

Under polar coordinates `y = e^t u` the cylinder is the punctured space `V ∖ {0}` of an inner
product space `V` of dimension `n + 1`, and the metric is the Euclidean metric multiplied by
`e^(2 (w(log ‖y‖) - log ‖y‖))`. The formula is therefore an instance of the conformal change of
scalar curvature, applied to a radial conformal exponent; locality and diffeomorphism invariance
of scalar curvature transport it to the cylinder.

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

* `TauCeti.scalarCurvature_rescale_exp_radial`: the scalar curvature of the Euclidean metric
  multiplied by `e^(2 (w(log ‖y‖) - log ‖y‖))`, away from the origin.
* `TauCeti.inner_mvfderiv_exp_smul_coe_sphere`: polar coordinates pull the Euclidean metric back to
  `e^(2 t) (g_(Sⁿ) + dt²)`.
* `TauCeti.scalarCurvature_rotationalMetric`: the scalar curvature of a rotationally symmetric
  metric.
* `TauCeti.isInvertible_mfderiv_exp_smul_coe_sphere`: polar coordinates have invertible
  differentials.
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

/-! ### Radial conformal factors on an inner product space -/

section Radial

open InnerProductSpace Laplacian
open scoped Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Scalar curvature of a radial conformal metric.** Let `φ` be a smooth function on a real inner
product space of dimension `N` which, near a point `y ≠ 0`, is `w(log ‖z‖) - log ‖z‖` for a
function `w` that is `C²` at `s = log ‖y‖`. Then the Euclidean metric multiplied by `e^(2 φ)` has
scalar curvature `(N - 1) e^(-2 w(s)) ((N - 2) (1 - w'(s)²) - 2 w''(s))` at `y`. In polar
coordinates `y = e^s u` this metric is `e^(2 w(s)) (ds² + g_(S^(N - 1)))`. -/
theorem scalarCurvature_rescale_exp_radial {φ : F → ℝ} (hφ : ContDiff ℝ ∞ φ) {w : ℝ → ℝ} {y : F}
    (hy : y ≠ 0) (hw : ContDiffAt ℝ 2 w (log ‖y‖))
    (heq : φ =ᶠ[𝓝 y] fun z ↦ w (log ‖z‖) - log ‖z‖) :
    (((riemannianMetricVectorSpace F).ofLE le_top).rescale (fun z ↦ exp (2 * φ z))
        (contDiff_const.mul hφ).exp.contMDiff fun _ ↦ exp_pos _).scalarCurvature y =
      (finrank ℝ F - 1) * exp (-2 * w (log ‖y‖)) *
        ((finrank ℝ F - 2) * (1 - deriv w (log ‖y‖) ^ 2) - 2 * deriv (deriv w) (log ‖y‖)) := by
  have hρ : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hlog : ContDiffAt ℝ 2 (fun z : F ↦ log ‖z‖) y :=
    (contDiffAt_log.2 hρ.ne').comp y (contDiffAt_norm ℝ hy)
  -- The conformal exponent is `ψ (log ‖z‖)` near `y`, with `ψ s = w s - s`.
  have hψ : ContDiffAt ℝ 2 (fun s ↦ w s - s) (log ‖y‖) := hw.sub contDiffAt_id
  have hheq : φ =ᶠ[𝓝 y] (fun s ↦ w s - s) ∘ fun z : F ↦ log ‖z‖ := heq
  have hw₁ : DifferentiableAt ℝ w (log ‖y‖) := hw.differentiableAt (by simp)
  have hderiv : deriv (fun s ↦ w s - s) =ᶠ[𝓝 (log ‖y‖)] fun s ↦ deriv w s - 1 := by
    filter_upwards [hw.eventually (by simp)] with s hs
    exact ((hs.differentiableAt (by simp)).hasDerivAt.sub (hasDerivAt_id s)).deriv
  have hΔφ : Δ φ y = (deriv (deriv w) (log ‖y‖) + (deriv w (log ‖y‖) - 1) * (finrank ℝ F - 2)) /
      ‖y‖ ^ 2 := by
    rw [(laplacian_congr_nhds hheq).eq_of_nhds,
      ContDiffAt.laplacian_comp (q := fun z : F ↦ log ‖z‖) hψ hlog, hderiv.deriv_eq,
      hderiv.eq_of_nhds, deriv_sub_const, laplacian_log_norm_of_ne hy,
      norm_gradient_eq_norm_fderiv, norm_fderiv_log_norm_of_ne hy]
    field_simp
  have hGφ : ‖∇ φ y‖ = |deriv w (log ‖y‖) - 1| * ‖y‖⁻¹ := by
    have hd : HasFDerivAt φ ((deriv w (log ‖y‖) - 1) • fderiv ℝ (fun z : F ↦ log ‖z‖) y) y :=
      (hw₁.hasDerivAt.sub (hasDerivAt_id _)).comp_hasFDerivAt y
        (hasFDerivAt_log_norm_of_ne hy).differentiableAt.hasFDerivAt |>.congr_of_eventuallyEq hheq
    rw [norm_gradient_eq_norm_fderiv, hd.fderiv, norm_smul, norm_fderiv_log_norm_of_ne hy,
      Real.norm_eq_abs]
  have hgrad : DifferentiableAt ℝ (∇ φ) y :=
    ((hφ.gradient_right (m := 1) (by simp)).differentiable (by simp)) y
  -- The conformal change formula, applied to the flat Euclidean metric `g`, involves only the
  -- Laplacian and the gradient of `φ` for `g`. The formula installs `g` with lowered
  -- smoothness; the flat identifications are transported along `toRiemannianMetric_ofLE`.
  rw [ContMDiffRiemannianMetric.scalarCurvature_rescale _ _ _ (φ := φ) (fun _ ↦ rfl) y]
  have hscal : ((riemannianMetricVectorSpace F).ofLE
      (le_top : (∞ : WithTop ℕ∞) ≤ ω)).scalarCurvature y = 0 := by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection _
      -- Mathlib's `RiemannianBundle` instance on the tangent spaces of `F` is defined to be the
      -- standard metric `(riemannianMetricVectorSpace F).toRiemannianMetric`, so this is `rfl`.
      (by rw [ContMDiffRiemannianMetric.toRiemannianMetric_ofLE]; rfl),
      TauCeti.Manifold.scalarCurvature_leviCivitaConnection_model_space]
  have hm := ContMDiffRiemannianMetric.toRiemannianMetric_ofLE (riemannianMetricVectorSpace F)
    (le_top : (∞ : WithTop ℕ∞) ≤ ω)
  have hΔ : (letI : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨((riemannianMetricVectorSpace F).ofLE (le_top : (∞ : WithTop ℕ∞) ≤ ω)).toRiemannianMetric⟩
      Manifold.laplaceBeltrami 𝓘(ℝ, F) φ y) = Δ φ y :=
    TauCeti.Manifold.laplaceBeltrami_eq_laplacian_of_eq
      (inst := ⟨((riemannianMetricVectorSpace F).ofLE le_top).toRiemannianMetric⟩) hm hgrad
  have hG : (letI : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨((riemannianMetricVectorSpace F).ofLE (le_top : (∞ : WithTop ℕ∞) ≤ ω)).toRiemannianMetric⟩
      ‖Manifold.mgradient 𝓘(ℝ, F) φ y‖) = ‖∇ φ y‖ :=
    TauCeti.Manifold.norm_mgradient_eq_norm_gradient_of_eq
      (inst := ⟨((riemannianMetricVectorSpace F).ofLE le_top).toRiemannianMetric⟩) hm _ y
  have hexp : (exp (2 * φ y))⁻¹ = exp (-2 * w (log ‖y‖)) * ‖y‖ ^ 2 := by
    have harg : -(2 * (w (log ‖y‖) - log ‖y‖)) = -2 * w (log ‖y‖) + log (‖y‖ ^ 2) := by
      rw [log_pow]
      push_cast
      ring
    rw [heq.eq_of_nhds, ← exp_neg, harg, exp_add, exp_log (by positivity)]
  rw [hscal, hΔ, hG, hexp, hΔφ, hGφ, mul_pow, sq_abs]
  field_simp
  ring

end Radial

/-! ### Polar coordinates -/

section Polar

open TauCeti.Manifold (tangentSpaceProdEquiv)

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

/-- The differential of polar coordinates is invertible. -/
theorem isInvertible_mfderiv_exp_smul_coe_sphere (p : sphere (0 : V) 1 × ℝ) :
    (mfderiv ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V)
      (fun q : sphere (0 : V) 1 × ℝ ↦ exp q.2 • (q.1 : V)) p).IsInvertible := by
  have hV : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, V) (exp p.2 • (p.1 : V))) := hV
  set L := mfderiv ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V)
    (fun q : sphere (0 : V) 1 × ℝ ↦ exp q.2 • (q.1 : V)) p
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun v hv ↦ ?_
    by_contra hv₀
    have h := inner_mvfderiv_exp_smul_coe_sphere p v v
    rw [mvfderiv_apply_eq_mfderiv_apply] at h
    -- `h` pairs the vectors `L v` in the tangent space of `V`, which is `V` itself.
    change ⟪L v, L v⟫_ℝ = _ at h
    rw [show L v = 0 from hv, inner_zero_left] at h
    exact (mul_pos (exp_pos _)
      ((((sphereRoundMetric (E := V)).ofLE le_top).cylinder).pos p v hv₀)).ne' h.symm
  have hdim : finrank ℝ (TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) =
      finrank ℝ (TangentSpace 𝓘(ℝ, V) (exp p.2 • (p.1 : V))) := by
    -- Both tangent spaces are their model vector spaces by definition.
    change finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) = finrank ℝ V
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self,
      (Fact.out : finrank ℝ V = n + 1)]
  exact ⟨((L : _ →ₗ[ℝ] _).linearEquivOfInjective hinj hdim).toContinuousLinearEquiv,
    by ext v; simp⟩

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

omit [Fact (finrank ℝ V = n + 1)] in
/-- For a smooth `w` and every `c`, there is a smooth function on `V` equal to the radial
conformal exponent `w(log ‖z‖) - log ‖z‖` of `e^(2 w(t)) (g_(Sⁿ) + dt²)` where `‖z‖ > e^c`. The
exponent itself is singular at the origin; it is cut off below `log ‖z‖ = c - 1`. -/
private theorem exists_contDiff_eq_radial {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (c : ℝ) :
    ∃ φ : V → ℝ, ContDiff ℝ ∞ φ ∧ ∀ z : V, exp c < ‖z‖ → φ z = w (log ‖z‖) - log ‖z‖ := by
  classical
  set ψ : ℝ → ℝ := fun s ↦ smoothTransition (s - c + 1) * (w s - s)
  have hψ : ContDiff ℝ ∞ ψ := (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).add contDiff_const)).mul (hw.sub contDiff_id)
  refine ⟨fun z ↦ if z = 0 then 0 else ψ (log ‖z‖), ?_, fun z hz ↦ ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    rcases eq_or_ne z 0 with rfl | hz
    · -- Near the origin `log ‖x‖ < c - 1`, where the cutoff vanishes.
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds (0 : V) (exp_pos (c - 1))] with x hx
      rcases eq_or_ne x 0 with rfl | hx₀
      · simp
      have hlog : log ‖x‖ ≤ c - 1 :=
        ((log_lt_iff_lt_exp (norm_pos_iff.2 hx₀)).2 (mem_ball_zero_iff.1 hx)).le
      simp [hx₀, ψ, smoothTransition.zero_of_nonpos (by linarith : log ‖x‖ - c + 1 ≤ 0)]
    · refine (hψ.contDiffAt.comp z ((contDiffAt_log.2 (norm_ne_zero_iff.2 hz)).comp z
        (contDiffAt_norm ℝ hz))).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hz] with x hx
      simp [hx]
  · have hz₀ : z ≠ 0 := norm_pos_iff.1 ((exp_pos _).trans hz)
    have hlog : c < log ‖z‖ := (lt_log_iff_exp_lt (norm_pos_iff.2 hz₀)).2 hz
    simp [hz₀, ψ, smoothTransition.one_of_one_le (by linarith : 1 ≤ log ‖z‖ - c + 1)]

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
  obtain ⟨φ, hφ, hφw⟩ := exists_contDiff_eq_radial (V := V) hw (p.2 - 1)
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
  -- The height is differentiated by the chain rule through the projection to `ℝ`.
  have hh : ∀ w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p,
      mvfderiv ((𝓡 n).prod 𝓘(ℝ)) (fun q : sphere (0 : V) 1 × ℝ ↦ h q.2) p w =
        r p.2 * sin (θ p.2) * NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p w).2 := by
    intro w
    rw [show (fun q : sphere (0 : V) 1 × ℝ ↦ h q.2) = h ∘ Prod.snd from rfl,
      mvfderiv_comp_apply _ hh'.differentiableAt.mdifferentiableAt mdifferentiableAt_snd,
      mfderiv_snd, mvfderiv_eq_fderiv]
    simp only [ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul,
      Manifold.tangentSpaceProdEquiv_apply, hh'.deriv]
    exact mul_comm _ _
  have hu : ⟪(p.1 : V), (p.1 : V)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p.1, one_pow]
  have h₁ : ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.1 (tangentSpaceProdEquiv p v).1,
      (p.1 : V)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact inner_coe_mvfderiv_subtypeVal_sphere p.1 _
  have h₂ := inner_coe_mvfderiv_subtypeVal_sphere p.1 (tangentSpaceProdEquiv p v').1
  have hexp : exp (2 * log (r p.2)) = r p.2 ^ 2 := by
    rw [mul_comm, exp_mul, exp_log (hr_pos p.2), rpow_two]
  rw [mvfderiv_smul_coe_sphere_apply p hr'.differentiableAt,
    mvfderiv_smul_coe_sphere_apply p hr'.differentiableAt, hh, hh, rotationalMetric_inner,
    ContMDiffRiemannianMetric.cylinder_inner, ContMDiffRiemannianMetric.ofLE_inner,
    sphereRoundMetric_inner, hexp, hr'.deriv]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right, h₁, h₂,
    hu]
  linear_combination (r p.2 ^ 2 * NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v).2 *
    NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v').2) * sin_sq_add_cos_sq (θ p.2)

/-- **The Gromov–Lawson bending term.** Let `r > 0` be smooth with `r' = -r cos θ`: the radius of a
curve in the half-plane, parametrised with speed `r`, whose velocity makes the angle `θ` with the
`-r` direction. The rotationally symmetric metric `r(t)² (g_(Sⁿ) + dt²)`, the induced metric of the
hypersurface swept out by the curve
(`TauCeti.inner_mvfderiv_smul_coe_sphere_add_mul_mvfderiv`), has scalar curvature
`n (n - 1) sin² θ / r² - 2 n k sin θ / r`, where `k = θ' / r` is the curvature of the curve. With
`n = q - 1` this is the bending term of the Gromov–Lawson surgery construction in codimension `q`.
-/
theorem scalarCurvature_rotationalMetric_log {r θ : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hr_pos : ∀ t, 0 < r t) (hr' : ∀ t, HasDerivAt r (-(r t * cos (θ t))) t)
    (p : sphere (0 : V) 1 × ℝ) (hθ : DifferentiableAt ℝ θ p.2) :
    (rotationalMetric (n := n) V (hr.log fun t ↦ (hr_pos t).ne')).scalarCurvature p =
      n * (n - 1) * sin (θ p.2) ^ 2 / r p.2 ^ 2 -
        2 * n * (deriv θ p.2 / r p.2) * sin (θ p.2) / r p.2 := by
  have hw : deriv (fun t ↦ log (r t)) = fun t ↦ -cos (θ t) := by
    funext t
    rw [((hr' t).log (hr_pos t).ne').deriv]
    field_simp [(hr_pos t).ne']
  have hw' : deriv (fun t ↦ -cos (θ t)) p.2 = sin (θ p.2) * deriv θ p.2 := by
    have hd : HasDerivAt (fun t ↦ -cos (θ t)) (-(-sin (θ p.2) * deriv θ p.2)) p.2 :=
      hθ.hasDerivAt.cos.neg
    rw [hd.deriv]
    ring
  have hexp : exp (-2 * log (r p.2)) = (r p.2 ^ 2)⁻¹ := by
    rw [mul_comm, exp_mul, exp_log (hr_pos p.2), rpow_neg (hr_pos p.2).le, rpow_two]
  rw [scalarCurvature_rotationalMetric, hw, hw', hexp]
  have hr₀ := (hr_pos p.2).ne'
  field_simp
  linear_combination (-(n * (n - 1) : ℝ)) * sin_sq_add_cos_sq (θ p.2)

end Bending

end TauCeti
