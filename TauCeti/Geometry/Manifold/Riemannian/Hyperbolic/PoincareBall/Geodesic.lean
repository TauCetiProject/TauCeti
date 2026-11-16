/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.PoincareBall.Connection

/-!
# Radial geodesics and the exponential map at the origin of the Poincaré ball

For a unit vector `u ∈ E` (`‖u‖ = 1`), the curve

`radialGeodesic hu (t : ℝ) = tanh (t / 2) • u`

traces the Euclidean diameter of `PoincareBall E` along `u` at unit hyperbolic speed: at parameter
`t`, its Euclidean velocity is `((1 - tanh² (t / 2)) / 2) • u` while the metric rescales Euclidean
norms by `2 / (1 - tanh² (t / 2))`, so the hyperbolic speed is identically `1` and the arc length
over `[a, b]` (`a ≤ b`) is `b - a`.

When `E` is finite-dimensional, substituting into the coordinate geodesic equation
`γ'' + Γ(γ', γ') = 0` shows that `radialGeodesic hu` is an all-time geodesic with initial velocity
`(1 / 2) • u` at the origin. Rescaling the parameter yields the closed-form formula for the
Riemannian exponential map at `0`:

`(riemannianExp 𝓘(ℝ, E) (PoincareBall E) 0 v : E) = (2 * tanh (‖v‖ / 2) / ‖v‖) • v_E`,

valid for every tangent vector `v` at `0` (including `v = 0` via `0 / 0 = 0`), where `v_E` is `v`
read in the model space `E` and `‖v‖ = 2 ‖v_E‖` is its hyperbolic norm.

## Main definitions

* `TauCeti.PoincareBall.radialGeodesic`: the unit-speed radial geodesic `t ↦ tanh (t / 2) • u` for
  `‖u‖ = 1`.

## Main results

* `TauCeti.PoincareBall.norm_mfderiv_radialGeodesic_one`,
  `TauCeti.PoincareBall.norm_curveVelocity_radialGeodesic`, and
  `TauCeti.PoincareBall.pathELength_radialGeodesic`: unit hyperbolic speed and arc length `b - a`
  in arbitrary real inner product spaces.
* `TauCeti.PoincareBall.isGeodesicCurve_radialGeodesic` and
  `TauCeti.PoincareBall.isGeodesicCurveOnFrom_radialGeodesic`: `radialGeodesic hu` is an all-time
  geodesic of the Levi-Civita connection.
* `TauCeti.PoincareBall.coe_riemannianExp_zero`,
  `TauCeti.PoincareBall.norm_coe_riemannianExp_zero`, and
  `TauCeti.PoincareBall.surjective_riemannianExp_zero`: explicit formula, Euclidean radius
  `tanh (‖v‖ / 2)`, and surjectivity of the Riemannian exponential map at the origin.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5
  and Proposition 5.27 (geodesics of the Poincaré ball).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 3, §2.
-/

public section

open Bundle Manifold MeasureTheory Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold

noncomputable section

namespace TauCeti.PoincareBall

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unit-speed radial curve `t ↦ tanh (t / 2) • u` through the origin of `PoincareBall E` along
a Euclidean unit vector `u ∈ E`. -/
def radialGeodesic {u : E} (hu : ‖u‖ = 1) (t : ℝ) : PoincareBall E :=
  mk (Real.tanh (t / 2) • u) (by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
    exact abs_lt.2 ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩)

@[simp]
theorem coe_radialGeodesic {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    (radialGeodesic hu t : E) = Real.tanh (t / 2) • u :=
  coe_mk _ _

@[simp]
theorem radialGeodesic_zero {u : E} (hu : ‖u‖ = 1) : radialGeodesic hu 0 = 0 :=
  ext (by simp)

@[simp]
theorem radialGeodesic_neg {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    radialGeodesic hu (-t) = -radialGeodesic hu t :=
  ext (by simp [neg_div, Real.tanh_neg, neg_smul])

/-- Every radial geodesic is analytic. -/
theorem contMDiff_radialGeodesic {n : WithTop ℕ∞} {u : E} (hu : ‖u‖ = 1) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) n (radialGeodesic hu) := by
  have hcomp : coe ∘ radialGeodesic hu = fun t : ℝ ↦ Real.tanh (t / 2) • u :=
    funext (coe_radialGeodesic hu)
  rw [← contMDiff_coe_comp_iff, hcomp, contMDiff_iff_contDiff]
  exact (Real.contDiff_tanh.comp (contDiff_id.div_const 2)).smul contDiff_const

/-- The Euclidean derivative of `coe ∘ radialGeodesic hu` at `t` is
`((1 - tanh (t / 2) ^ 2) / 2) • u`. -/
theorem hasDerivAt_coe_radialGeodesic {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (radialGeodesic hu s : E))
      (((1 - Real.tanh (t / 2) ^ 2) / 2) • u) t := by
  simp_rw [coe_radialGeodesic]
  have htanh : HasDerivAt (fun s : ℝ ↦ Real.tanh (s / 2))
      ((1 - Real.tanh (t / 2) ^ 2) / 2) t := by
    simpa only [mul_one_div] using ((hasDerivAt_id' (x := t)).div_const 2).tanh'
  exact htanh.smul_const u

private theorem hasDerivAt_second_radialGeodesic {u : E} (hu : ‖u‖ = 1) (r : ℝ) :
    HasDerivAt (deriv (fun s : ℝ ↦ (radialGeodesic hu s : E)))
      ((-(Real.tanh (r / 2) * (1 - Real.tanh (r / 2) ^ 2) / 2)) • u) r := by
  have hfirst : deriv (fun s : ℝ ↦ (radialGeodesic hu s : E)) =
      fun s : ℝ ↦ ((1 - Real.tanh (s / 2) ^ 2) / 2) • u :=
    funext fun s ↦ (hasDerivAt_coe_radialGeodesic hu s).deriv
  rw [hfirst]
  have htanh : HasDerivAt (fun s : ℝ ↦ Real.tanh (s / 2))
      ((1 - Real.tanh (r / 2) ^ 2) / 2) r := by
    simpa only [mul_one_div] using ((hasDerivAt_id' (x := r)).div_const 2).tanh'
  have hsq : HasDerivAt (fun s : ℝ ↦ Real.tanh (s / 2) ^ 2)
      ((2 : ℕ) * Real.tanh (r / 2) ^ (2 - 1) * ((1 - Real.tanh (r / 2) ^ 2) / 2)) r :=
    htanh.pow 2
  have hscalar : HasDerivAt (fun s : ℝ ↦ (1 - Real.tanh (s / 2) ^ 2) / 2)
      (-(Real.tanh (r / 2) * (1 - Real.tanh (r / 2) ^ 2) / 2)) r := by
    convert ((hasDerivAt_const r (1 : ℝ)).sub hsq).div_const 2 using 1
    push_cast
    ring
  exact hscalar.smul_const u

/-- The differential of `radialGeodesic hu` at `t` sends `1` to
`((1 - tanh (t / 2) ^ 2) / 2) • u` in the model space `E`. -/
theorem tangentSpaceCastModel_mfderiv_radialGeodesic_one {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    tangentSpaceCastModel 𝓘(ℝ, E) (radialGeodesic hu t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (radialGeodesic hu) t 1) =
      ((1 - Real.tanh (t / 2) ^ 2) / 2) • u := by
  -- Mathlib's `One (TangentSpace 𝓘(ℝ) t)` instance defines `1` as `(1 : ℝ)` (`Icc.lean`).
  have h1 : NormedSpace.fromTangentSpace (𝕜 := ℝ) t 1 = (1 : ℝ) := (rfl)
  rw [tangentSpaceCastModel_mfderiv_coe_comp, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, h1, Function.comp_def,
    (hasDerivAt_coe_radialGeodesic hu t).hasFDerivAt.fderiv]
  simp

/-- The velocity of `radialGeodesic hu` at `t` in the model space `E`. -/
theorem tangentSpaceCastModel_curveVelocity_radialGeodesic {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    tangentSpaceCastModel 𝓘(ℝ, E) (radialGeodesic hu t)
        (curveVelocity 𝓘(ℝ, E) (radialGeodesic hu) t) =
      ((1 - Real.tanh (t / 2) ^ 2) / 2) • u := by
  rw [curveVelocity_apply]
  exact tangentSpaceCastModel_mfderiv_radialGeodesic_one hu t

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every radial geodesic has unit hyperbolic speed at every time `t`. -/
@[simp 1100]
theorem norm_mfderiv_radialGeodesic_one {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (radialGeodesic hu) t 1‖ = 1 := by
  have hpos : 0 < 1 - Real.tanh (t / 2) ^ 2 := by
    rw [Real.one_sub_tanh_sq]
    positivity
  have hnorm_pt : ‖(radialGeodesic hu t : E)‖ ^ 2 = Real.tanh (t / 2) ^ 2 := by
    rw [coe_radialGeodesic, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  rw [norm_def, tangentSpaceCastModel_mfderiv_radialGeodesic_one, hnorm_pt, norm_smul, hu,
    mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hpos)]
  field_simp [hpos.ne']

@[simp 1100]
theorem eNorm_mfderiv_radialGeodesic_one {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (radialGeodesic hu) t 1‖ₑ = 1 := by
  rw [← ofReal_norm, norm_mfderiv_radialGeodesic_one, ENNReal.ofReal_one]

/-- The curve velocity of `radialGeodesic hu` has unit hyperbolic norm everywhere. -/
@[simp 1100]
theorem norm_curveVelocity_radialGeodesic {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    ‖curveVelocity 𝓘(ℝ, E) (radialGeodesic hu) t‖ = 1 := by
  rw [curveVelocity_apply]
  exact norm_mfderiv_radialGeodesic_one hu t

/-- The hyperbolic path length of `radialGeodesic hu` on `[a, b]` is `ENNReal.ofReal (b - a)`. -/
@[simp]
theorem pathELength_radialGeodesic {u : E} (hu : ‖u‖ = 1) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, E) (radialGeodesic hu) a b = ENNReal.ofReal (b - a) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  simp [Real.volume_Icc]

end InnerProductSpace

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "J" => 𝓘(ℝ, E)

/-- Every radial curve `t ↦ tanh (t / 2) • u` (`‖u‖ = 1`) is an all-time geodesic of
`PoincareBall E`. -/
theorem isGeodesicCurve_radialGeodesic {u : E} (hu : ‖u‖ = 1) :
    IsGeodesicCurve J (radialGeodesic hu) := by
  rw [← isGeodesicCurveOn_univ, isGeodesicCurveOn_iff_chart uniqueDiffOn_univ, contMDiffOn_univ]
  refine ⟨contMDiff_radialGeodesic hu, fun r _ ↦ ?_⟩
  have hcomp : extChartAt J (radialGeodesic hu r) ∘ radialGeodesic hu =
      fun s : ℝ ↦ (radialGeodesic hu s : E) :=
    funext fun s ↦ extChartAt_apply _ _
  simp only [hcomp, derivWithin_univ]
  rw [(hasDerivAt_second_radialGeodesic hu r).deriv, (hasDerivAt_coe_radialGeodesic hu r).deriv,
    christoffelMap_leviCivitaConnection_apply]
  let s : ℝ := Real.tanh (r / 2)
  have hpos : 0 < 1 - s ^ 2 := by
    dsimp only [s]
    rw [Real.one_sub_tanh_sq]
    positivity
  have hnorm_pt : ‖(radialGeodesic hu r : E)‖ ^ 2 = s ^ 2 := by
    rw [coe_radialGeodesic, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu, one_pow]
  rw [hnorm_pt, coe_radialGeodesic]
  simp only [real_inner_smul_left, real_inner_smul_right, huu, mul_one, smul_smul, ← add_smul,
    ← sub_smul]
  dsimp only [s] at hpos ⊢
  convert zero_smul ℝ u using 2
  field_simp [hpos.ne']
  ring

/-- `radialGeodesic hu` is a geodesic on `ℝ` starting at `0` with initial velocity
`(1 / 2) • u` in the model space `E`. -/
theorem isGeodesicCurveOnFrom_radialGeodesic {u : E} (hu : ‖u‖ = 1)
    {v : TangentSpace J (0 : PoincareBall E)}
    (hv : tangentSpaceCastModel J 0 v = (1 / 2 : ℝ) • u) :
    IsGeodesicCurveOnFrom J (radialGeodesic hu) univ 0 v := by
  refine ⟨isGeodesicCurveOn_univ.2 (isGeodesicCurve_radialGeodesic hu), mem_univ 0, ?_⟩
  have h0 : radialGeodesic hu 0 = 0 := radialGeodesic_zero hu
  have htransport {x y : PoincareBall E} (h : x = y) (w : TangentSpace J x) :
      tangentSpaceCastModel J y (cast (congrArg (TangentSpace J) h) w) =
        tangentSpaceCastModel J x w := by
    subst h
    rfl
  have hvel : cast (congrArg (TangentSpace J) h0)
      (curveVelocityWithin J (radialGeodesic hu) univ 0) = v := by
    apply (tangentSpaceCastModel J 0).injective
    rw [htransport h0, curveVelocityWithin_univ, tangentSpaceCastModel_curveVelocity_radialGeodesic]
    simp [hv]
  exact TotalSpace.ext h0 ((cast_heq _ _).symm.trans (heq_of_eq hvel))

/-- Along a unit tangent vector at the origin (Euclidean length `1 / 2`), the Riemannian
exponential map traces `radialGeodesic hu`. -/
theorem riemannianExp_smul_eq_radialGeodesic {u : E} (hu : ‖u‖ = 1)
    {v : TangentSpace J (0 : PoincareBall E)}
    (hv : tangentSpaceCastModel J 0 v = (1 / 2 : ℝ) • u) (t : ℝ) :
    riemannianExp J (PoincareBall E) 0 (t • v) = radialGeodesic hu t := by
  have h := (isGeodesicCurveOnFrom_radialGeodesic hu hv).comp_mul_left t
    uniqueDiffOn_univ (mapsTo_univ _ _) (mem_univ _)
  simpa only [riemannianExp_def, Function.comp_apply, mul_one] using
    h.eq_maximalGeodesic_of_univ 1

/-- Explicit formula for the Riemannian exponential map of `PoincareBall E` at the origin, valid for
every tangent vector `v` (including `v = 0` via `0 / 0 = 0`). -/
theorem coe_riemannianExp_zero (v : TangentSpace J (0 : PoincareBall E)) :
    (riemannianExp J (PoincareBall E) 0 v : E) =
      (2 * Real.tanh (‖v‖ / 2) / ‖v‖) • tangentSpaceCastModel J 0 v := by
  by_cases hv : v = 0
  · subst hv
    simp
  set w : E := tangentSpaceCastModel J 0 v
  have hv_norm : ‖v‖ = 2 * ‖w‖ := by
    simp [w, norm_def]
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have hw0 : ‖w‖ ≠ 0 := by
    intro hw0
    exact hv0 (by simp [hv_norm, hw0])
  let u : E := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hw0]
  let v₀ : TangentSpace J (0 : PoincareBall E) :=
    (tangentSpaceCastModel J 0).symm ((1 / 2 : ℝ) • u)
  have hv₀ : tangentSpaceCastModel J 0 v₀ = (1 / 2 : ℝ) • u :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  have hscale : ‖v‖ • v₀ = v := by
    apply (tangentSpaceCastModel J 0).injective
    rw [map_smul, hv₀, smul_smul]
    dsimp only [u]
    rw [smul_smul, hv_norm]
    have hc : 2 * ‖w‖ * (1 / 2) * ‖w‖⁻¹ = 1 := by field_simp [hw0]
    rw [hc, one_smul]
  have hexp := congrArg PoincareBall.coe (riemannianExp_smul_eq_radialGeodesic hu hv₀ ‖v‖)
  rw [hscale, coe_radialGeodesic] at hexp
  rw [hexp, hv_norm]
  dsimp only [u]
  rw [smul_smul]
  congr 1
  field_simp [hw0]

/-- The Euclidean norm of `riemannianExp 0 v` is `tanh (‖v‖ / 2)` for every tangent vector `v` at
the origin. -/
@[simp]
theorem norm_coe_riemannianExp_zero (v : TangentSpace J (0 : PoincareBall E)) :
    ‖(riemannianExp J (PoincareBall E) 0 v : E)‖ = Real.tanh (‖v‖ / 2) := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hv_norm : ‖v‖ = 2 * ‖tangentSpaceCastModel J 0 v‖ := by simp [norm_def]
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hw0 : ‖tangentSpaceCastModel J 0 v‖ ≠ 0 := by linarith
  have htanh : 0 ≤ Real.tanh (‖v‖ / 2) := Real.tanh_nonneg (by positivity)
  rw [coe_riemannianExp_zero, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg zero_le_two htanh) hv_pos.le), hv_norm]
  field_simp [hw0]

/-- The Riemannian exponential map of `PoincareBall E` at the origin is surjective. -/
theorem surjective_riemannianExp_zero :
    Function.Surjective (riemannianExp J (PoincareBall E) 0) := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, riemannianExp_zero 0⟩
  have hx_pos : 0 < ‖(x : E)‖ := norm_pos_iff.2 (coe_eq_zero.not.2 hx)
  have hx0 : ‖(x : E)‖ ≠ 0 := hx_pos.ne'
  have hx_mem : ‖(x : E)‖ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, norm_lt_one x⟩
  have hartanh : 0 < Real.artanh ‖(x : E)‖ := Real.artanh_pos ⟨hx_pos, norm_lt_one x⟩
  let v : TangentSpace J (0 : PoincareBall E) :=
    (tangentSpaceCastModel J 0).symm ((Real.artanh ‖(x : E)‖ / ‖(x : E)‖) • (x : E))
  refine ⟨v, ext ?_⟩
  have hv_cast : tangentSpaceCastModel J 0 v = (Real.artanh ‖(x : E)‖ / ‖(x : E)‖) • (x : E) :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  have hv_norm : ‖v‖ = 2 * Real.artanh ‖(x : E)‖ := by
    simp [norm_def, hv_cast, norm_smul, abs_of_nonneg hartanh.le, hx0]
  rw [coe_riemannianExp_zero, hv_cast, hv_norm, smul_smul]
  have hhalf : 2 * Real.artanh ‖(x : E)‖ / 2 = Real.artanh ‖(x : E)‖ := by ring
  rw [hhalf, Real.tanh_artanh hx_mem]
  have hc : 2 * ‖(x : E)‖ / (2 * Real.artanh ‖(x : E)‖) *
      (Real.artanh ‖(x : E)‖ / ‖(x : E)‖) = 1 := by
    field_simp [hx0, hartanh.ne']
  rw [hc, one_smul]

end FiniteDimensional

end TauCeti.PoincareBall

end
