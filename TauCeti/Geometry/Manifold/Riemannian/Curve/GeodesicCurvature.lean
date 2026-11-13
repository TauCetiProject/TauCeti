/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Geometry.Manifold.Riemannian.Curve.Speed
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# The signed geodesic curvature of a curve

Let `γ` be a curve in a Riemannian manifold and `n` a field of tangent vectors along `γ`. The
*signed geodesic curvature* of `γ` relative to `n` is

`k_g = ⟪D_t γ', n⟫ / ‖γ'‖²`,

where `D_t γ'` is the covariant acceleration of `γ` for the Levi-Civita connection. The intended
case is a regular curve on a surface with a unit normal field `n` along it: then `k_g` is the
geodesic curvature of `γ`, with the sign for which a curve bending towards `n` has positive
curvature. For a unit-speed curve `k_g = ⟪D_t γ', n⟫`; the division by the squared speed extends
this to regular curves that are not parametrized by arc length. On an oriented surface the normal
is usually `TauCeti.Manifold.orientedUnitNormal`, the velocity rotated by `+π/2`.

Replacing `n` by `-n` changes the sign of `k_g`. If `n` is orthogonal to `γ'` along the curve,
differentiating `⟪n, γ'⟫ = 0` gives `⟪D_t n, γ'⟫ = -k_g ‖γ'‖²`. On a surface the tangent plane is
spanned by `γ'` and `n`, which gives the two structure equations of the moving frame `(γ', n)`:
`D_t γ' = k_g n` for a unit-speed curve, and `D_t n = -k_g γ'`.

The geodesic curvature does not depend on the parametrization: for a change of parameter `φ` with
`φ' ≠ 0` and a normal orthogonal to the velocity, the acceleration of `γ ∘ φ` is
`φ'' γ' + φ'² D_t γ'`, whose normal component is `φ'²` times that of `D_t γ'`, while the squared
speed is multiplied by `φ'²`. The oriented unit normal is unchanged by increasing
reparametrizations and reversed by reversing the curve, so the geodesic curvature relative to it
changes sign when the curve is reversed. In particular the total geodesic curvature `∫ k_g ds` of
an arc shared by two adjacent domains, which traverse it in opposite directions, cancels when the
two are added. Relative to the oriented unit normal, `k_g` is the oriented area of `(γ', D_t γ')`
divided by `‖γ'‖³`, which makes it continuous along a regular `C²` curve.

## Main definitions and results

* `TauCeti.Manifold.geodesicCurvature`: the signed geodesic curvature of a curve relative to a
  field of tangent vectors along it, unfolded by `TauCeti.Manifold.geodesicCurvature_def`.
* `TauCeti.Manifold.geodesicCurvature_neg`: reversing the normal reverses the sign.
* `TauCeti.Manifold.geodesicCurvature_eq_inner_of_norm_curveVelocity_eq_one`: at a parameter of
  unit speed, `k_g = ⟪D_t γ', n⟫`.
* `TauCeti.Manifold.inner_alongCurve_curveVelocity_eq_neg_geodesicCurvature_mul`: for a field `n`
  orthogonal to the velocity, `⟪D_t n, γ'⟫ = -k_g ‖γ'‖²`.
* `TauCeti.Manifold.acceleration_eq_geodesicCurvature_smul`: on a surface, a unit-speed curve
  with unit normal `n` satisfies `D_t γ' = k_g n`.
* `TauCeti.Manifold.alongCurve_eq_neg_geodesicCurvature_smul_curveVelocity`: on a surface, a
  unit normal field `n` along a regular curve satisfies `D_t n = -k_g γ'`.
* `TauCeti.Manifold.geodesicCurvature_comp` and `TauCeti.Manifold.geodesicCurvature_comp_const_sub`:
  invariance under reparametrization.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal`: relative to the oriented unit normal,
  `k_g = vol(γ', D_t γ') / ‖γ'‖³`.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp` and
  `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp_const_sub`: relative to the oriented
  unit normal, `k_g` is unchanged by increasing reparametrizations and changes sign under reversal.
* `TauCeti.Manifold.integral_geodesicCurvature_orientedUnitNormal_comp_const_sub`: reversing an
  arc reverses the sign of its total geodesic curvature.
* `TauCeti.Manifold.continuous_geodesicCurvature_orientedUnitNormal`: along a regular `C²` curve,
  the geodesic curvature relative to the oriented unit normal is continuous.

## References

* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, Prentice-Hall, 1976, §4-4.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 9 (Gauss–Bonnet).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {n : ∀ r, TangentSpace I (γ r)} {t : ℝ}

/-- The **signed geodesic curvature** `k_g = ⟪D_t γ', n⟫ / ‖γ'‖²` of the curve `γ` relative to the
field `n` of tangent vectors along it, where `D_t γ'` is the covariant acceleration for the
Levi-Civita connection. For a regular curve on a surface and a unit normal field `n` this is the
geodesic curvature of `γ`, positive when `γ` bends towards `n`. It is `0` where the velocity
vanishes. -/
def geodesicCurvature (γ : ℝ → M) (n : ∀ r, TangentSpace I (γ r)) (t : ℝ) : ℝ :=
  ⟪acceleration (leviCivitaConnection I M) γ t, n t⟫_ℝ / ‖curveVelocity I γ t‖ ^ 2

/-- The defining formula for `geodesicCurvature`. -/
theorem geodesicCurvature_def (γ : ℝ → M) (n : ∀ r, TangentSpace I (γ r)) (t : ℝ) :
    geodesicCurvature γ n t =
      ⟪acceleration (leviCivitaConnection I M) γ t, n t⟫_ℝ / ‖curveVelocity I γ t‖ ^ 2 :=
  (rfl)

/-- Reversing the normal field reverses the sign of the geodesic curvature. -/
@[to_fun (attr := simp) geodesicCurvature_fun_neg]
theorem geodesicCurvature_neg (γ : ℝ → M) (n : ∀ r, TangentSpace I (γ r)) (t : ℝ) :
    geodesicCurvature γ (-n) t = -geodesicCurvature γ n t := by
  rw [geodesicCurvature_def, geodesicCurvature_def, Pi.neg_apply, inner_neg_right, neg_div]

/-- At a parameter where the curve has unit speed, the geodesic curvature is the component
`⟪D_t γ', n⟫` of the acceleration along the normal. -/
theorem geodesicCurvature_eq_inner_of_norm_curveVelocity_eq_one
    (n : ∀ r, TangentSpace I (γ r)) (hγ : ‖curveVelocity I γ t‖ = 1) :
    geodesicCurvature γ n t = ⟪acceleration (leviCivitaConnection I M) γ t, n t⟫_ℝ := by
  rw [geodesicCurvature_def, hγ, one_pow, div_one]

/-- At a parameter where the velocity does not vanish, the geodesic curvature times the squared
speed is the component `⟪D_t γ', n⟫` of the acceleration along the normal. -/
theorem geodesicCurvature_mul_norm_curveVelocity_sq
    (n : ∀ r, TangentSpace I (γ r)) (hγ : curveVelocity I γ t ≠ 0) :
    geodesicCurvature γ n t * ‖curveVelocity I γ t‖ ^ 2 =
      ⟪acceleration (leviCivitaConnection I M) γ t, n t⟫_ℝ := by
  rw [geodesicCurvature_def, div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hγ))]

/-- **The tangential part of the derivative of a normal field.** Let `γ` be a curve that is `C²`
at `t` and `n` a differentiable field along `γ` that is orthogonal to the velocity near `t`. Then
`⟪D_t n, γ'⟫ = -k_g ‖γ'‖²`, where `k_g` is the geodesic curvature of `γ` relative to `n`. For a
unit-speed curve this is `⟪D_t n, γ'⟫ = -k_g`. -/
theorem inner_alongCurve_curveVelocity_eq_neg_geodesicCurvature_mul
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hn : DifferentiableAt ℝ (sectionCoord (F := E) γ n (γ t)) t)
    (hnγ : ∀ᶠ r in 𝓝 t, ⟪n r, curveVelocity I γ r⟫_ℝ = 0) :
    ⟪alongCurve (leviCivitaConnection I M) γ n t, curveVelocity I γ t⟫_ℝ =
      -(geodesicCurvature γ n t * ‖curveVelocity I γ t‖ ^ 2) := by
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγ
  have hv := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := γ)
    (hγu.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hu)
  have hd := (isMetricCompatible_leviCivitaConnection (I := I) (M := M)).hasDerivAt_inner_alongCurve
    (hγ.mdifferentiableAt two_ne_zero) hn hv
  have h := hd.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hnγ)
  rw [← acceleration_def, real_inner_comm (acceleration (leviCivitaConnection I M) γ t)] at h
  rcases eq_or_ne (curveVelocity I γ t) 0 with h0 | h0
  · simp [h0]
  · rw [geodesicCurvature_mul_norm_curveVelocity_sq n h0]
    exact eq_neg_of_add_eq_zero_left h

/-- **The acceleration of a unit-speed curve on a surface** is `D_t γ' = k_g n`, where `n` is a
unit normal of the curve and `k_g` is the geodesic curvature relative to `n`. The tangent space at
`γ t` is two-dimensional, the curve is `C²` at `t` and has unit speed near `t`, and `n t` is a
unit vector orthogonal to the velocity. -/
theorem acceleration_eq_geodesicCurvature_smul
    (hdim : Module.finrank ℝ (TangentSpace I (γ t)) = 2)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t) (hγ₁ : ∀ᶠ r in 𝓝 t, ‖curveVelocity I γ r‖ = 1)
    (hn : ‖n t‖ = 1) (hnγ : ⟪n t, curveVelocity I γ t⟫_ℝ = 0) :
    acceleration (leviCivitaConnection I M) γ t = geodesicCurvature γ n t • n t := by
  have : Fact (Module.finrank ℝ (TangentSpace I (γ t)) = 2) := ⟨hdim⟩
  have hv : curveVelocity I γ t ≠ 0 :=
    norm_ne_zero_iff.mp (hγ₁.self_of_nhds.trans_ne one_ne_zero)
  have hn0 : n t ≠ 0 := norm_ne_zero_iff.mp (hn.trans_ne one_ne_zero)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hv hn0
      ((real_inner_comm _ _).trans (inner_acceleration_curveVelocity_eq_zero hγ hγ₁))
      ((real_inner_comm _ _).trans hnγ))
  rw [geodesicCurvature_eq_inner_of_norm_curveVelocity_eq_one n hγ₁.self_of_nhds, ← hc,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]

/-- **The derivative of a unit normal field along a curve on a surface** is `D_t n = -k_g γ'`,
where `k_g` is the geodesic curvature relative to `n`. The tangent space at `γ t` is
two-dimensional, the curve is `C²` at `t` with nonzero velocity there, and `n` is a differentiable
field along it which, near `t`, has unit length and is orthogonal to the velocity. -/
theorem alongCurve_eq_neg_geodesicCurvature_smul_curveVelocity
    (hdim : Module.finrank ℝ (TangentSpace I (γ t)) = 2)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t) (hγ₀ : curveVelocity I γ t ≠ 0)
    (hn : DifferentiableAt ℝ (sectionCoord (F := E) γ n (γ t)) t)
    (hn₁ : ∀ᶠ r in 𝓝 t, ‖n r‖ = 1)
    (hnγ : ∀ᶠ r in 𝓝 t, ⟪n r, curveVelocity I γ r⟫_ℝ = 0) :
    alongCurve (leviCivitaConnection I M) γ n t =
      -(geodesicCurvature γ n t • curveVelocity I γ t) := by
  have : Fact (Module.finrank ℝ (TangentSpace I (γ t)) = 2) := ⟨hdim⟩
  have hn0 : n t ≠ 0 := norm_ne_zero_iff.mp (hn₁.self_of_nhds.trans_ne one_ne_zero)
  have hperp := (isMetricCompatible_leviCivitaConnection (I := I)
    (M := M)).inner_alongCurve_self_eq_zero_of_eventually_norm_eq
      (hγ.mdifferentiableAt two_ne_zero) hn (hn₁.mono fun r hr ↦ hr.trans hn₁.self_of_nhds.symm)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hn0 hγ₀
      ((real_inner_comm _ _).trans hperp) hnγ.self_of_nhds)
  have hcoeff := inner_alongCurve_curveVelocity_eq_neg_geodesicCurvature_mul hγ hn hnγ
  rw [← hc, real_inner_smul_left, real_inner_self_eq_norm_sq, ← neg_mul] at hcoeff
  rw [← hc, mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hγ₀)) hcoeff, neg_smul]

/-- **Reparametrization invariance of the geodesic curvature.** Let `γ` be a `C²` curve and `φ` a
differentiable change of parameter with `φ'(t) ≠ 0` and `φ'` differentiable at `t`. If `n (φ t)`
is orthogonal to the velocity of `γ` at `φ t`, then the geodesic curvature of `γ ∘ φ` relative to
`n ∘ φ` at `t` is that of `γ` relative to `n` at `φ t`. -/
theorem geodesicCurvature_comp (hγ : ContMDiff 𝓘(ℝ) I 2 γ) {φ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hφ' : DifferentiableAt ℝ (deriv φ) t) (hφ₀ : deriv φ t ≠ 0)
    (hn : ⟪n (φ t), curveVelocity I γ (φ t)⟫_ℝ = 0) :
    geodesicCurvature (γ ∘ φ) (fun r ↦ n (φ r)) t = geodesicCurvature γ n (φ t) := by
  have hV := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := γ)
    hγ.contMDiffOn isOpen_univ (Set.mem_univ (φ t))
  rw [geodesicCurvature_def, geodesicCurvature_def,
    acceleration_comp _ γ hφ hφ' (hγ.mdifferentiable two_ne_zero) hV,
    curveVelocity_comp (hφ t).hasDerivAt (hγ.mdifferentiable two_ne_zero (φ t))]
  simp only [inner_add_left, real_inner_smul_left, (real_inner_comm _ _).trans hn,
    mul_zero, zero_add, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hφ₀)

/-- **Reversing the parametrization** of a `C²` curve together with its normal field does not
change the geodesic curvature. Unlike `TauCeti.Manifold.geodesicCurvature_comp`, the normal field
need not be orthogonal to the velocity, since the reversal `r ↦ d - r` has zero second derivative.
-/
theorem geodesicCurvature_comp_const_sub (hγ : ContMDiff 𝓘(ℝ) I 2 γ) (d t : ℝ) :
    geodesicCurvature (fun r ↦ γ (d - r)) (fun r ↦ n (d - r)) t =
      geodesicCurvature γ n (d - t) := by
  have hd : deriv (fun r : ℝ ↦ d - r) = fun _ ↦ -1 := by
    funext r
    simp
  have hV := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := γ)
    hγ.contMDiffOn isOpen_univ (Set.mem_univ (d - t))
  have hacc := acceleration_comp (leviCivitaConnection I M) γ (φ := fun r ↦ d - r) (t := t)
    (by fun_prop) (by rw [hd]; fun_prop) (hγ.mdifferentiable two_ne_zero) hV
  have hv := curveVelocity_comp ((hasDerivAt_id t).const_sub d)
    (hγ.mdifferentiable two_ne_zero (d - t))
  simp only [Function.comp_def, hd, deriv_const, zero_smul, neg_one_sq, one_smul,
    zero_add, id_eq, neg_smul] at hacc hv
  rw [geodesicCurvature_def, geodesicCurvature_def, hacc, hv, norm_neg]

section Oriented

/-! ### The oriented unit normal -/

variable (o : Orientation I M (Fin 2))

/-- **The geodesic curvature relative to the oriented unit normal** is the oriented area of the
velocity and the covariant acceleration divided by the cubed speed,
`k_g = vol(γ', D_t γ') / ‖γ'‖³`. -/
theorem geodesicCurvature_orientedUnitNormal (γ : ℝ → M) (t : ℝ) :
    geodesicCurvature γ (orientedUnitNormal o γ) t =
      riemannianVolumeForm o (γ t) ![curveVelocity I γ t,
        acceleration (leviCivitaConnection I M) γ t] / ‖curveVelocity I γ t‖ ^ 3 := by
  let := o.fact_finrank_tangentSpace (γ t)
  rw [geodesicCurvature_def, orientedUnitNormal_apply, NormedSpace.normalize, map_smul,
    real_inner_smul_right, real_inner_comm,
    (o.orientationAt (γ t)).inner_rightAngleRotation_left, riemannianVolumeForm_apply,
    ← (o.orientationAt (γ t)).areaForm_to_volumeForm]
  ring

/-- Positive reparametrization of a `C²` curve does not change its geodesic curvature relative to
the oriented unit normal. -/
theorem geodesicCurvature_orientedUnitNormal_comp (hγ : ContMDiff 𝓘(ℝ) I 2 γ) {φ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hφ' : DifferentiableAt ℝ (deriv φ) t) (hφ₀ : 0 < deriv φ t) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  rw [← geodesicCurvature_comp hγ hφ hφ' hφ₀.ne' (inner_orientedUnitNormal_curveVelocity o γ _),
    geodesicCurvature_def, geodesicCurvature_def,
    orientedUnitNormal_comp o (hφ t).hasDerivAt hφ₀ (hγ.mdifferentiable two_ne_zero (φ t))]

/-- Reversing the parametrization of a `C²` curve reverses the sign of its geodesic curvature
relative to the oriented unit normal. -/
theorem geodesicCurvature_orientedUnitNormal_comp_const_sub (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    (d t : ℝ) :
    geodesicCurvature (fun r ↦ γ (d - r)) (orientedUnitNormal o fun r ↦ γ (d - r)) t =
      -geodesicCurvature γ (orientedUnitNormal o γ) (d - t) := by
  rw [funext (orientedUnitNormal_comp_const_sub o γ d), geodesicCurvature_fun_neg,
    geodesicCurvature_comp_const_sub hγ]

/-- **Cancellation along a common arc.** Traversing a `C²` arc backwards reverses the sign of its
total geodesic curvature `∫ k_g ds` relative to the oriented unit normal. Hence the contributions
of an arc shared by two adjacent domains, each with its boundary oriented positively, cancel. -/
theorem integral_geodesicCurvature_orientedUnitNormal_comp_const_sub
    (hγ : ContMDiff 𝓘(ℝ) I 2 γ) (d a b : ℝ) :
    ∫ t in a..b, geodesicCurvature (fun r ↦ γ (d - r)) (orientedUnitNormal o fun r ↦ γ (d - r)) t *
        ‖curveVelocity I (fun r ↦ γ (d - r)) t‖ =
      -∫ t in d - b..d - a, geodesicCurvature γ (orientedUnitNormal o γ) t *
        ‖curveVelocity I γ t‖ := by
  have hv (t : ℝ) : curveVelocity I (fun r ↦ γ (d - r)) t = -curveVelocity I γ (d - t) := by
    simpa [Function.comp_def] using curveVelocity_comp ((hasDerivAt_id t).const_sub d)
      (hγ.mdifferentiable two_ne_zero (d - t))
  simp_rw [geodesicCurvature_orientedUnitNormal_comp_const_sub o hγ, hv, norm_neg, neg_mul]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_sub_left
      (fun r ↦ geodesicCurvature γ (orientedUnitNormal o γ) r * ‖curveVelocity I γ r‖) d]

/-- The geodesic curvature of a periodic `C²` curve relative to its oriented unit normal is
periodic, with the same period. -/
theorem _root_.Function.Periodic.geodesicCurvature_orientedUnitNormal (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    {a : ℝ} (hper : Function.Periodic γ a) :
    Function.Periodic (geodesicCurvature γ (orientedUnitNormal o γ)) a := by
  intro t
  have h := geodesicCurvature_orientedUnitNormal_comp o hγ (φ := (· + a)) (t := t) (by fun_prop)
    (by simp) (by simp)
  rwa [show γ ∘ (· + a) = γ from funext hper, eq_comm] at h

/-- The geodesic curvature of a `C²` curve relative to its oriented unit normal is continuous at
every parameter where the velocity does not vanish. -/
theorem continuousAt_geodesicCurvature_orientedUnitNormal (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    (hne : curveVelocity I γ t ≠ 0) :
    ContinuousAt (geodesicCurvature γ (orientedUnitNormal o γ)) t := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : ContMDiffVectorBundle (0 + 1) E (TangentSpace I : M → Type _) I := by
    simpa using (inferInstance : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I)
  have hV : ContMDiff 𝓘(ℝ) I.tangent (0 + 1)
      fun r ↦ TotalSpace.mk' E (γ r) (curveVelocity I γ r) := by
    rw [zero_add, ← funext fun r ↦ curveVelocityLift_apply (I := I) γ r, ← contMDiffOn_univ,
      ← curveVelocityLiftWithin_univ]
    exact hγ.contMDiffOn.contMDiffOn_curveVelocityLiftWithin (by norm_num) uniqueMDiffOn_univ
  have hA : ContMDiff 𝓘(ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (γ r) (acceleration (leviCivitaConnection I M) γ r)) := by
    simpa only [acceleration_def] using
      (leviCivitaConnection I M).contMDiff_alongCurve γ (curveVelocity I γ)
        (fun x ↦ contMDiffCovariantDerivativeOn_leviCivitaConnection (n := 0) (m := 2) (k := 1)
          (trivializationAt E (TangentSpace I) x).open_baseSet (by norm_num) (by norm_num)) hV
  have hvol := ((isSmoothForm_riemannianVolumeForm (n := 0) o).contMDiff (γ t)).comp t
    (hγ.of_le (by norm_num) t)
  have heval := hvol.continuousAlternatingMap_bundle_apply
    (v := fun i r ↦ ![curveVelocity I γ r, acceleration (leviCivitaConnection I M) γ r] i)
    (fun i ↦ by
      fin_cases i
      · exact (hV.of_le (by norm_num)) t
      · exact hA t)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  have hnorm : Continuous fun r ↦ ‖curveVelocity I γ r‖ :=
    (continuous_norm_bundle E (TangentSpace I)).comp hV.continuous
  exact ((contMDiffAt_totalSpace_iff.mp heval).2.continuousAt.div (hnorm.pow 3).continuousAt
    (pow_ne_zero 3 (norm_ne_zero_iff.mpr hne))).congr
    (Eventually.of_forall fun r ↦ (geodesicCurvature_orientedUnitNormal o γ r).symm)

/-- The geodesic curvature of a regular `C²` curve relative to its oriented unit normal is
continuous. -/
theorem continuous_geodesicCurvature_orientedUnitNormal (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    (hne : ∀ t, curveVelocity I γ t ≠ 0) :
    Continuous (geodesicCurvature γ (orientedUnitNormal o γ)) :=
  continuous_iff_continuousAt.mpr fun t ↦
    continuousAt_geodesicCurvature_orientedUnitNormal o hγ (hne t)

end Oriented

end TauCeti.Manifold
