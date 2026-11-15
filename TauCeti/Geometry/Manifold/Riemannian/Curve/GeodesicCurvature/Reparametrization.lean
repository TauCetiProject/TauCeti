/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# Reparametrization of signed geodesic curvature

The geodesic curvature relative to a chosen normal field is invariant under regular
reparametrization. The chain rule for the covariant acceleration gives
`D_t (γ ∘ φ)' = φ'' γ' + (φ')² D_t γ'`. The first term is orthogonal to the chosen normal,
and the factor `(φ')²` in the second term cancels the same factor in the squared speed.
This statement holds in any dimension and also at points where the velocity of `γ` vanishes.

On an oriented surface, an orientation-preserving regular reparametrization preserves signed
geodesic curvature relative to the oriented unit normal, while an orientation-reversing one
negates it. In particular, the affine parameter reflection `r ↦ γ (d - r)` negates this curvature
without any regularity assumption on the original curve.

The signed density `k_g ‖γ'‖` pulls back by the parameter derivative, so its interval
integral obeys change of variables. Germ and open-interval congruence allow comparison of
curves sharing an arc; reflection negates the integral. The volume-form expression
`k_g = vol(γ', D_t γ') / ‖γ'‖³` also gives continuity at regular `C²` parameters.

## Main results

* `TauCeti.Manifold.geodesicCurvature_comp`: invariance relative to a transported normal field.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp`: the sign law for a general
  reparametrization, including at zero derivative.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp_const_sub`: reflecting a curve
  changes the sign of its curvature relative to the oriented unit normal.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 9.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ}

/-- **Reparametrization invariance of the geodesic curvature.** Let `γ` be `C²` at `φ t` and
let `φ` be a change of parameter with `φ'(t) ≠ 0` and `φ'` differentiable at `t`. If `n (φ t)`
is orthogonal to the velocity of `γ` at `φ t`, then the geodesic curvature of `γ ∘ φ` relative to
`n ∘ φ` at `t` is that of `γ` relative to `n` at `φ t`. -/
theorem geodesicCurvature_comp (n : ∀ r, TangentSpace I (γ r)) (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t))
    (hφ' : DifferentiableAt ℝ (deriv φ) t) (hφ₀ : deriv φ t ≠ 0)
    (hn : ⟪n (φ t), curveVelocity I γ (φ t)⟫_ℝ = 0) :
    geodesicCurvature (γ ∘ φ) (fun r ↦ n (φ r)) t = geodesicCurvature γ n (φ t) := by
  have hφ : ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ φ r :=
    (hφ'.continuousAt.eventually_ne hφ₀).mono fun _ hr ↦ differentiableAt_of_deriv_ne_zero hr
  rw [geodesicCurvature_def, geodesicCurvature_def,
    acceleration_comp _ γ hφ hφ' (hγ.eventually_mdifferentiableAt two_ne_zero)
      hγ.differentiableAt_sectionCoord_curveVelocity,
    curveVelocity_comp hφ.self_of_nhds.hasDerivAt (hγ.mdifferentiableAt two_ne_zero)]
  simp only [inner_add_left, real_inner_smul_left, (real_inner_comm _ _).trans hn,
    mul_zero, zero_add, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hφ₀)

/-- Reparametrization multiplies signed geodesic curvature relative to the oriented unit
normal by the sign of the derivative. At zero derivative both sides vanish. -/
theorem geodesicCurvature_orientedUnitNormal_comp (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ : DifferentiableAt ℝ φ t)
    (hφ' : DifferentiableAt ℝ (deriv φ) t) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      (SignType.sign (deriv φ t) : ℝ) *
        geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  by_cases hφ₀ : deriv φ t = 0
  · rw [geodesicCurvature_def,
      curveVelocity_comp hφ.hasDerivAt
        (hγ.mdifferentiableAt two_ne_zero)]
    simp [hφ₀]
  · have hcomp := geodesicCurvature_comp (orientedUnitNormal o γ) hγ hφ' hφ₀
      (inner_orientedUnitNormal_curveVelocity o γ (φ t))
    rw [geodesicCurvature_def,
      orientedUnitNormal_comp o (hγ.mdifferentiableAt two_ne_zero)
        hφ, real_inner_smul_right, mul_div_assoc]
    rw [geodesicCurvature_def] at hcomp
    rw [hcomp]

/-- An orientation-preserving regular reparametrization preserves signed geodesic curvature
relative to the oriented unit normal. -/
theorem geodesicCurvature_orientedUnitNormal_comp_of_deriv_pos (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ' : DifferentiableAt ℝ (deriv φ) t)
    (hφ₀ : 0 < deriv φ t) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  rw [geodesicCurvature_orientedUnitNormal_comp o hγ
    (differentiableAt_of_deriv_ne_zero hφ₀.ne') hφ']
  simp [hφ₀]

/-- An orientation-reversing regular reparametrization negates signed geodesic curvature
relative to the oriented unit normal. -/
theorem geodesicCurvature_orientedUnitNormal_comp_of_deriv_neg (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ' : DifferentiableAt ℝ (deriv φ) t)
    (hφ₀ : deriv φ t < 0) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      -geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  rw [geodesicCurvature_orientedUnitNormal_comp o hγ
    (differentiableAt_of_deriv_ne_zero hφ₀.ne) hφ']
  simp [hφ₀]

/-- Reflecting the parameter via `r ↦ γ (d - r)` negates signed geodesic curvature relative to
the oriented unit normal, without any regularity assumption on the original curve. -/
theorem geodesicCurvature_orientedUnitNormal_comp_const_sub
    (o : Orientation I M (Fin 2)) (γ : ℝ → M) (d t : ℝ) :
    geodesicCurvature (fun r ↦ γ (d - r))
      (orientedUnitNormal o (fun r ↦ γ (d - r))) t =
        -geodesicCurvature γ (orientedUnitNormal o γ) (d - t) := by
  rw [geodesicCurvature_def, geodesicCurvature_def, acceleration_comp_const_sub,
    curveVelocity_comp_const_sub, orientedUnitNormal_comp_const_sub,
    norm_neg, inner_neg_right, neg_div]

/-- Reversing a curve together with its normal field preserves geodesic curvature.
The normal need not be orthogonal to the velocity, and no regularity is assumed. -/
theorem geodesicCurvature_comp_const_sub (n : ∀ r, TangentSpace I (γ r)) (d t : ℝ) :
    geodesicCurvature (fun r ↦ γ (d - r)) (fun r ↦ n (d - r)) t =
      geodesicCurvature γ n (d - t) := by
  rw [geodesicCurvature_def, geodesicCurvature_def, acceleration_comp_const_sub,
    curveVelocity_comp_const_sub, norm_neg]

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

/-- The signed geodesic-curvature density pulls back by the derivative of a regular change of
parameter. This formula applies to both signs of the derivative. -/
theorem geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp {φ : ℝ → ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t))
    (hφ' : DifferentiableAt ℝ (deriv φ) t) (hφ₀ : deriv φ t ≠ 0) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t * ‖curveVelocity I (γ ∘ φ) t‖ =
      geodesicCurvature γ (orientedUnitNormal o γ) (φ t) * ‖curveVelocity I γ (φ t)‖ *
        deriv φ t := by
  rw [geodesicCurvature_orientedUnitNormal_comp o hγ
    (differentiableAt_of_deriv_ne_zero hφ₀) hφ',
    curveVelocity_comp (differentiableAt_of_deriv_ne_zero hφ₀).hasDerivAt
      (hγ.mdifferentiableAt two_ne_zero), norm_smul, Real.norm_eq_abs]
  rcases hφ₀.lt_or_gt with hneg | hpos
  · simp [hneg, abs_of_neg hneg, mul_comm, mul_assoc]
  · simp [hpos, abs_of_pos hpos, mul_comm, mul_assoc]

/-- Curves agreeing near a parameter have the same geodesic curvature relative to the oriented
unit normal there. -/
theorem _root_.Filter.EventuallyEq.geodesicCurvature_orientedUnitNormal_eq
    {η : ℝ → M} (h : γ =ᶠ[𝓝 t] η) (o : Orientation I M (Fin 2)) :
    geodesicCurvature γ (orientedUnitNormal o γ) t =
      geodesicCurvature η (orientedUnitNormal o η) t := by
  rw [geodesicCurvature_orientedUnitNormal, geodesicCurvature_orientedUnitNormal,
    h.self_of_nhds, h.curveVelocity_eq, h.acceleration_eq]

/-- Curves agreeing on the open interval have the same total geodesic curvature there.
Endpoint values and regularity at the endpoints do not affect the integral. -/
theorem
    _root_.Set.EqOn.integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_eq
    {η : ℝ → M} {a b : ℝ} (h : Set.EqOn γ η (Set.uIoo a b))
    (o : Orientation I M (Fin 2)) :
    ∫ t in a..b, geodesicCurvature γ (orientedUnitNormal o γ) t * ‖curveVelocity I γ t‖ =
      ∫ t in a..b, geodesicCurvature η (orientedUnitNormal o η) t * ‖curveVelocity I η t‖ := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have heq := h.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
  dsimp only
  rw [heq.geodesicCurvature_orientedUnitNormal_eq o, heq.self_of_nhds, heq.curveVelocity_eq]

/-- Reflection `r ↦ d - r` negates the interval integral of geodesic curvature times speed
relative to the oriented unit normal. No regularity or integrability assumptions are needed. -/
theorem integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp_const_sub
    (d a b : ℝ) :
    ∫ t in a..b, geodesicCurvature (fun r ↦ γ (d - r)) (orientedUnitNormal o fun r ↦ γ (d - r)) t *
        ‖curveVelocity I (fun r ↦ γ (d - r)) t‖ =
      -∫ t in d - b..d - a, geodesicCurvature γ (orientedUnitNormal o γ) t *
        ‖curveVelocity I γ t‖ := by
  simp_rw [geodesicCurvature_orientedUnitNormal_comp_const_sub o γ,
    curveVelocity_comp_const_sub, norm_neg, neg_mul]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_sub_left
      (fun r ↦ geodesicCurvature γ (orientedUnitNormal o γ) r * ‖curveVelocity I γ r‖) d]

/-- The geodesic curvature of a periodic curve relative to its oriented unit normal is
periodic, with the same period. No regularity is assumed. -/
theorem _root_.Function.Periodic.geodesicCurvature_orientedUnitNormal
    {a : ℝ} (hper : Function.Periodic γ a) :
    Function.Periodic (geodesicCurvature γ (orientedUnitNormal o γ)) a := by
  intro t
  have hcurve : (fun r ↦ γ (r + a)) = γ := hper.funext
  have hv := curveVelocity_comp_add_right (I := I) γ t a
  have hacc := acceleration_comp_add_const (leviCivitaConnection I M) γ a t
  rw [hcurve] at hv hacc
  rw [TauCeti.Manifold.geodesicCurvature_orientedUnitNormal,
    TauCeti.Manifold.geodesicCurvature_orientedUnitNormal, hper t, ← hv, ← hacc]

/-- If a curve is `C²` at a parameter with nonzero velocity, its geodesic curvature relative to
the oriented unit normal is continuous there. -/
theorem continuousAt_geodesicCurvature_orientedUnitNormal (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hne : curveVelocity I γ t ≠ 0) :
    ContinuousAt (geodesicCurvature γ (orientedUnitNormal o γ)) t := by
  have hV : ContMDiffAt 𝓘(ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocity I γ r)) t := by
    rw [← funext (curveVelocityLift_apply (I := I) γ)]
    exact hγ.contMDiffAt_curveVelocityLift (by norm_num)
  have hA := contMDiffAt_acceleration_leviCivitaConnection (n := 0) (m := 2) (k := 1)
    (by norm_num) (by norm_num) hγ
  -- Normalize the regularity indices required by the volume-form evaluation API.
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : ContMDiffVectorBundle (0 + 1) E (TangentSpace I : M → Type _) I := by
    simpa using (inferInstance : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I)
  have hvol := ((isSmoothForm_riemannianVolumeForm (n := 0) o).contMDiff (γ t)).comp t
    (hγ.of_le (by norm_num))
  have heval := hvol.continuousAlternatingMap_bundle_apply
    (v := fun i r ↦ ![curveVelocity I γ r, acceleration (leviCivitaConnection I M) γ r] i)
    (fun i ↦ by
      fin_cases i
      · exact hV.of_le (by norm_num)
      · exact hA)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  have hnorm : ContinuousAt (fun r ↦ ‖curveVelocity I γ r‖) t :=
    (continuous_norm_bundle E (TangentSpace I)).continuousAt.comp hV.continuousAt
  exact ((contMDiffAt_totalSpace_iff.mp heval).2.continuousAt.div (hnorm.pow 3)
    (pow_ne_zero 3 (norm_ne_zero_iff.mpr hne))).congr
    (Eventually.of_forall fun r ↦ (geodesicCurvature_orientedUnitNormal o γ r).symm)

/-- The geodesic curvature of a regular `C²` curve relative to its oriented unit normal is
continuous. -/
theorem continuous_geodesicCurvature_orientedUnitNormal (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    (hne : ∀ t, curveVelocity I γ t ≠ 0) :
    Continuous (geodesicCurvature γ (orientedUnitNormal o γ)) :=
  continuous_iff_continuousAt.mpr fun t ↦
    continuousAt_geodesicCurvature_orientedUnitNormal o hγ.contMDiffAt (hne t)

/-- A regular change of parameter preserves the interval integral of signed geodesic curvature
times speed, with the endpoints transported by the change of parameter. The derivative may have
either sign. Smoothness and nonvanishing are only required along the interval and its image. -/
theorem integral_geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp
    {φ : ℝ → ℝ} {a b : ℝ}
    (hγ : ∀ r ∈ φ '' Set.uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ r)
    (hφ' : ∀ r ∈ Set.uIcc a b, DifferentiableAt ℝ (deriv φ) r)
    (hφ₀ : ∀ r ∈ Set.uIcc a b, deriv φ r ≠ 0)
    (hne : ∀ r ∈ φ '' Set.uIcc a b, curveVelocity I γ r ≠ 0) :
    ∫ t in a..b, geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t *
        ‖curveVelocity I (γ ∘ φ) t‖ =
      ∫ t in φ a..φ b, geodesicCurvature γ (orientedUnitNormal o γ) t *
        ‖curveVelocity I γ t‖ := by
  have hnorm : ∀ r ∈ φ '' Set.uIcc a b, ContinuousAt (fun r ↦ ‖curveVelocity I γ r‖) r := by
    intro r hr
    have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
      (F := E) (V := fun x : M ↦ TangentSpace I x)
    have hV : ContMDiffAt 𝓘(ℝ) I.tangent 0
        (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocity I γ r)) r := by
      rw [← funext (curveVelocityLift_apply (I := I) γ)]
      exact (hγ r hr).contMDiffAt_curveVelocityLift (by norm_num)
    exact (continuous_norm_bundle E (TangentSpace I)).continuousAt.comp hV.continuousAt
  calc
    _ = ∫ t in a..b, (geodesicCurvature γ (orientedUnitNormal o γ) (φ t) *
        ‖curveVelocity I γ (φ t)‖) * deriv φ t := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp o
        (hγ (φ r) ⟨r, hr, rfl⟩) (hφ' r hr) (hφ₀ r hr)
    _ = _ := intervalIntegral.integral_comp_mul_deriv'
      (fun r hr ↦ (differentiableAt_of_deriv_ne_zero (hφ₀ r hr)).hasDerivAt)
      (fun r hr ↦ (hφ' r hr).continuousAt.continuousWithinAt)
      (fun r hr ↦ ((continuousAt_geodesicCurvature_orientedUnitNormal o (hγ r hr) (hne r hr)).mul
        (hnorm r hr)).continuousWithinAt)

end TauCeti.Manifold
