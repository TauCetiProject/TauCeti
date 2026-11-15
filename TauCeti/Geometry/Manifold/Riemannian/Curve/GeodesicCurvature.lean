/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Geometry.Manifold.Riemannian.Curve.Speed
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

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

/-- Geodesic curvature depends only on the normal at the current parameter. -/
theorem geodesicCurvature_congr_normal {n₁ n₂ : ∀ r, TangentSpace I (γ r)}
    (hn : n₁ t = n₂ t) : geodesicCurvature γ n₁ t = geodesicCurvature γ n₂ t := by
  rw [geodesicCurvature_def, geodesicCurvature_def, hn]

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

end TauCeti.Manifold
