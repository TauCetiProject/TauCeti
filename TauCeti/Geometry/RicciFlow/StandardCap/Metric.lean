/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.RicciFlow.StandardCap.PuncturedMetric
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.SpecialFunctions.Trigonometric.CosSqrt
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Riemannian.Coercive
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic

/-!
# The standard cap metric

A standard cap profile `f` gives the standard cap metric `dr² + f(r)² g_(Sⁿ)` on a real inner
product space `V` of dimension `n + 1`; for `V = ℝ³` this is Perelman's standard initial metric,
which Ricci flow with surgery glues in along the necks it cuts. In Cartesian coordinates the metric
at `x` pairs tangent vectors `v`, `w` to

`a(x) ⟪v, w⟫ + ((1 - a(x)) / ‖x‖²) ⟪x, v⟫ ⟪x, w⟫`,  with  `a(x) = (f(‖x‖) / ‖x‖)²`,

so that the radial direction has unit length and the spheres about the tip are scaled by
`f(r) / r`. At the tip `a = f'(0)² = 1` and the metric is Euclidean.

The norm `‖x‖` is not differentiable at the tip, and the two coefficients `a` and
`(1 - a) / ‖x‖²` are smooth there because, near the tip, `f` is the odd profile `2 sin (r / 2)` of
a round sphere: then `a = 2 (1 - cos ‖x‖) / ‖x‖²` and
`(1 - a) / ‖x‖² = (‖x‖² - 2 (1 - cos ‖x‖)) / ‖x‖⁴` are analytic functions of `‖x‖²`, namely
difference quotients at `0` of the entire function `TauCeti.cosSqrt` with
`cosSqrt (r²) = cos r`.

Polar coordinates `(r, u) ↦ r u` on `(0, ∞) × Sⁿ` pull the standard cap metric back to the
punctured standard cap metric `TauCeti.IsStandardCapProfile.puncturedMetric`. Since curvature is
natural under local isometries, its scalar curvature transfers to the standard cap away from the
tip, and by continuity also at the tip: the scalar curvature is nonnegative, equal to that of the
round sphere of radius `2` near the tip and to that of the round cylinder `ℝ × Sⁿ(√2)` on the end.
For `V = ℝ³` these are `3 / 2` and `1`.

## Main definitions

* `TauCeti.standardCapPolar`: polar coordinates `(r, u) ↦ r u` from `(0, ∞) × Sⁿ` to `V`.
* `TauCeti.IsStandardCapProfile.metric`: the standard cap metric on `V`, a smooth Riemannian
  metric also at the tip.

## Main results

* `TauCeti.IsStandardCapProfile.metric_inner`, `TauCeti.IsStandardCapProfile.metric_inner_zero`:
  the standard cap metric in Cartesian coordinates, and its Euclidean value at the tip.
* `TauCeti.IsStandardCapProfile.pullback_metric_standardCapPolar`: in polar coordinates the
  standard cap metric is the punctured standard cap metric `dr² + f(r)² g_(Sⁿ)`.
* `TauCeti.IsStandardCapProfile.scalarCurvature_metric_nonneg`: the standard cap has nonnegative
  scalar curvature.
* `TauCeti.IsStandardCapProfile.exists_scalarCurvature_metric_eq_round`,
  `TauCeti.IsStandardCapProfile.exists_scalarCurvature_metric_eq_cylinder`: the scalar curvature
  near the tip and on the cylindrical end.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Definition 12.1.
* G. Perelman, *Ricci flow with surgery on three-manifolds*, arXiv:math/0303109 (2003), §2.
-/

public noncomputable section

open Bundle Set Real Filter Topology
open scoped ContDiff Manifold InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Polar coordinates on `(0, ∞) × Sⁿ` -/

section Polar

open Metric (sphere)
open TauCeti.Manifold

variable (V) in
/-- Polar coordinates `(r, u) ↦ r u` from `(0, ∞) × Sⁿ` to `V`, the coordinates in which the
standard cap metric is `dr² + f(r)² g_(Sⁿ)`. -/
def standardCapPolar (p : standardCapRadialDomain × sphere (0 : V) 1) : V :=
  (p.1 : ℝ) • (p.2 : V)

@[simp]
theorem standardCapPolar_apply (p : standardCapRadialDomain × sphere (0 : V) 1) :
    standardCapPolar V p = (p.1 : ℝ) • (p.2 : V) :=
  (rfl)

theorem standardCapPolar_def :
    standardCapPolar V =
      fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V) :=
  (rfl)

/-- The point `r u` in polar coordinates has norm `r`. -/
theorem norm_standardCapPolar (p : standardCapRadialDomain × sphere (0 : V) 1) :
    ‖standardCapPolar V p‖ = p.1 := by
  rw [standardCapPolar_apply, norm_smul, norm_eq_of_mem_sphere p.2, mul_one,
    Real.norm_of_nonneg p.1.property.le]

/-- Polar coordinates `(r, u) ↦ r u` on `(0, ∞) × Sⁿ` cover every point of `V` except the
origin: `x ≠ 0` is `r u` for `r = ‖x‖` and `u = x / ‖x‖`. -/
theorem range_standardCapPolar : range (standardCapPolar V) = {0}ᶜ := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    exact norm_ne_zero_iff.1 ((norm_standardCapPolar p).trans_ne p.1.property.ne')
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine ⟨(⟨‖x‖, hr⟩, ⟨‖x‖⁻¹ • x, ?_⟩), ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  · simp [smul_smul, mul_inv_cancel₀ hr.ne']

variable {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

/-- The differential of polar coordinates `(r, u) ↦ r u` on `(0, ∞) × Sⁿ`: a tangent vector
`(ρ, ξ)` at `(r, u)` is sent to `r ξ + ρ u`, where `ξ` is read in `V`. -/
theorem mvfderiv_standardCapPolar_apply (p : standardCapRadialDomain × sphere (0 : V) 1)
    (v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    mvfderiv (𝓘(ℝ).prod (𝓡 n)) (standardCapPolar V) p v =
      (p.1 : ℝ) • mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2 +
        NormedSpace.fromTangentSpace (p.1 : ℝ)
          (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1) • (p.2 : V) := by
  have hι := (contMDiff_coe_sphere (E := V) (n := n) (m := 1) p.2).mdifferentiableAt one_ne_zero
  have h₁ : mvfderiv (𝓘(ℝ).prod (𝓡 n))
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.2 : V)) p v =
      mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2 := by
    rw [tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_snd_apply _ p v
  have h₂ : mvfderiv (𝓘(ℝ).prod (𝓡 n))
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ)) p v =
      NormedSpace.fromTangentSpace (p.1 : ℝ)
        (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1) := by
    rw [tangentSpaceProdEquiv_apply, tangentSpaceOpenEquiv_apply]
    exact (mvfderiv_comp_fst_apply _ p v).trans (mvfderiv_subtype_val_apply p.1 v.1)
  have hd₁ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.2 : V)) p :=
    hι.comp p mdifferentiableAt_snd
  have hd₂ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ)
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ)) p :=
    (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero).comp p mdifferentiableAt_fst
  rw [standardCapPolar_def, mvfderiv_fun_smul hd₂ hd₁]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, h₁, h₂]

/-- Polar coordinates `(r, u) ↦ r u` on `(0, ∞) × Sⁿ` are smooth. -/
theorem contMDiff_standardCapPolar {m : ℕ∞ω} :
    ContMDiff (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) m (standardCapPolar V) :=
  (contMDiff_subtypeVal.comp contMDiff_fst).smul (contMDiff_coe_sphere.comp contMDiff_snd)

/-- Polar coordinates `(r, u) ↦ r u` on `(0, ∞) × Sⁿ` have injective differentials: the image
`r ξ + ρ u` of `(ρ, ξ)` has radial component `ρ` and tangential component `r ξ`. -/
theorem injective_mfderiv_standardCapPolar (p : standardCapRadialDomain × sphere (0 : V) 1) :
    Function.Injective (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (standardCapPolar V) p) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  have hv' := congrArg (NormedSpace.fromTangentSpace _) hv
  rw [NormedSpace.fromTangentSpace_apply, ← mvfderiv_apply_eq_mfderiv_apply,
    mvfderiv_standardCapPolar_apply, map_zero] at hv'
  -- The radial component vanishes, since `ξ` is orthogonal to `u`.
  have hρ : NormedSpace.fromTangentSpace (p.1 : ℝ)
      (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1 (tangentSpaceProdEquiv p v).1) = 0 := by
    have h := congrArg (fun z : V ↦ ⟪(p.2 : V), z⟫_ℝ) hv'
    simp only [inner_add_right, real_inner_smul_right, inner_coe_mvfderiv_subtypeVal_sphere,
      real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, inner_zero_right] at h
    linarith
  rw [hρ, zero_smul, add_zero, smul_eq_zero_iff_right p.1.property.ne'] at hv'
  have hξ : (tangentSpaceProdEquiv p v).2 = 0 :=
    (injective_mvfderiv_subtypeVal_sphere p.2).eq_iff' (map_zero _) |>.1 hv'
  have h₁ : (tangentSpaceProdEquiv p v).1 = 0 :=
    (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) p.1).injective
      ((NormedSpace.fromTangentSpace _).injective (by rw [hρ, map_zero, map_zero]))
  exact (tangentSpaceProdEquiv p).injective (by rw [map_zero]; exact Prod.ext h₁ hξ)

/-- Polar coordinates `(r, u) ↦ r u` on `(0, ∞) × Sⁿ` have invertible differentials. -/
theorem isInvertible_mfderiv_standardCapPolar (p : standardCapRadialDomain × sphere (0 : V) 1) :
    (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (standardCapPolar V) p).IsInvertible := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  -- The tangent spaces are the model spaces `ℝ × ℝⁿ` and `V`, of the same dimension `n + 1`.
  refine ContinuousLinearMap.isInvertible_of_injective_of_finrank_eq
    (U := ℝ × EuclideanSpace ℝ (Fin n)) (G := V) _ ?_ (injective_mfderiv_standardCapPolar p)
  rw [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self,
    Fact.out (p := Module.finrank ℝ V = n + 1), add_comm]

end Polar

namespace IsStandardCapProfile

variable {f : ℝ → ℝ} (V)

/-- The inner product of `V` as a continuous bilinear form over `ℝ`. -/
private abbrev realInner : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ

/-- The standard cap metric at `x` as a bilinear form on `V`:
`a ⟪v, w⟫ + ((1 - a) / ‖x‖²) ⟪x, v⟫ ⟪x, w⟫` with `a = (f(‖x‖) / ‖x‖)²`, read as `1` at
the tip. -/
private def capForm (f : ℝ → ℝ) (x : V) : V →L[ℝ] V →L[ℝ] ℝ :=
  dslope f 0 ‖x‖ ^ 2 • realInner V +
    ((1 - dslope f 0 ‖x‖ ^ 2) / ‖x‖ ^ 2) • (innerSL ℝ x).smulRight (innerSL ℝ x)

variable {V}

private theorem combination_apply (a b : ℝ) (x v w : V) :
    (a • realInner V + b • (innerSL ℝ x).smulRight (innerSL ℝ x)) v w =
      a * ⟪v, w⟫_ℝ + b * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) := by
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    innerSL_apply_apply]
  -- `realInner V` is `innerSL ℝ`, read as a bilinear rather than sesquilinear map.
  rfl

private theorem capForm_apply (x v w : V) :
    capForm V f x v w = dslope f 0 ‖x‖ ^ 2 * ⟪v, w⟫_ℝ +
      (1 - dslope f 0 ‖x‖ ^ 2) / ‖x‖ ^ 2 * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) :=
  combination_apply _ _ x v w

variable (hf : IsStandardCapProfile f)
include hf

/-- Near the tip, the coefficients of the cap form are analytic functions of `‖x‖²`, built from
the difference quotients of `cosSqrt`. -/
private theorem capForm_eventuallyEq_tip :
    capForm V f =ᶠ[𝓝 0] fun y ↦ (-2 * dslope cosSqrt 0 (‖y‖ ^ 2)) • realInner V +
      (2 * dslope (dslope cosSqrt 0) 0 (‖y‖ ^ 2)) • (innerSL ℝ y).smulRight (innerSL ℝ y) := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin
  filter_upwards [Metric.ball_mem_nhds (0 : V) hr₀] with y hy
  rw [mem_ball_zero_iff] at hy
  rcases eq_or_ne y 0 with rfl | hy0
  · ext v w
    rw [capForm_apply, combination_apply]
    simp [dslope_same, hf.deriv_zero, deriv_cosSqrt_zero]
    ring
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hr2 : ‖y‖ ^ 2 ≠ 0 := by positivity
  -- With `r = ‖y‖`, `f r = 2 sin (r / 2)` and `cos r = 1 - 2 sin² (r / 2)`.
  have hcos : cos ‖y‖ = 1 - 2 * sin (‖y‖ / 2) ^ 2 := by
    rw [← cos_two_mul_eq_one_sub, mul_div_cancel₀ _ two_ne_zero]
  have hD₁ : dslope cosSqrt 0 (‖y‖ ^ 2) = (cos ‖y‖ - 1) / ‖y‖ ^ 2 := by
    rw [dslope_of_ne _ hr2, slope_def_field, cosSqrt_sq, cosSqrt_zero, sub_zero]
  have hD₂ : dslope (dslope cosSqrt 0) 0 (‖y‖ ^ 2) =
      ((cos ‖y‖ - 1) / ‖y‖ ^ 2 + 1 / 2) / ‖y‖ ^ 2 := by
    rw [dslope_of_ne _ hr2, slope_def_field, hD₁, dslope_same, deriv_cosSqrt_zero]
    ring
  have ha : dslope f 0 ‖y‖ ^ 2 = -2 * dslope cosSqrt 0 (‖y‖ ^ 2) := by
    rw [hf.dslope_zero_of_ne_zero hr.ne', h _ ⟨hr.le, hy⟩, hD₁, hcos]
    field_simp
    ring
  have hb : (1 - dslope f 0 ‖y‖ ^ 2) / ‖y‖ ^ 2 = 2 * dslope (dslope cosSqrt 0) 0 (‖y‖ ^ 2) := by
    rw [ha, hD₁, hD₂]
    field_simp
    ring
  rw [capForm, hb, ha]

/-- The cap form is smooth, also at the tip. -/
private theorem contDiff_capForm : ContDiff ℝ ∞ (capForm V f) := by
  -- Use Mathlib's operator-norm scalar-action instance, without exporting another instance.
  let : IsBoundedSMul ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := V →L[ℝ] V →L[ℝ] ℝ)
  have hrank : ContDiff ℝ ∞ fun y : V ↦ (innerSL ℝ y).smulRight (innerSL ℝ y) :=
    (innerSL ℝ).contDiff.smulRight (innerSL ℝ).contDiff
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have hD₁ : ContDiff ℝ ∞ (dslope cosSqrt 0) := (analyticOnNhd_cosSqrt.dslope 0).contDiff
    have hD₂ : ContDiff ℝ ∞ (dslope (dslope cosSqrt 0) 0) :=
      ((analyticOnNhd_cosSqrt.dslope 0).dslope 0).contDiff
    refine ContDiffAt.congr_of_eventuallyEq ?_ hf.capForm_eventuallyEq_tip
    refine ContDiff.contDiffAt (ContDiff.add ?_ ?_)
    · exact (contDiff_const.mul (hD₁.comp (contDiff_norm_sq ℝ))).smul contDiff_const
    · exact (contDiff_const.mul (hD₂.comp (contDiff_norm_sq ℝ))).smul hrank
  · -- Away from the tip `dslope f 0 ‖y‖ = f ‖y‖ / ‖y‖`, a quotient of smooth functions.
    have hnorm : ContDiffAt ℝ ∞ (fun y : V ↦ ‖y‖) x := contDiffAt_norm ℝ hx
    have hq : ContDiffAt ℝ ∞ (fun y : V ↦ f ‖y‖ / ‖y‖) x :=
      (hf.contDiff.contDiffAt.comp x hnorm).div hnorm (norm_ne_zero_iff.2 hx)
    have hev : capForm V f =ᶠ[𝓝 x] fun y ↦ (f ‖y‖ / ‖y‖) ^ 2 • realInner V +
        ((1 - (f ‖y‖ / ‖y‖) ^ 2) / ‖y‖ ^ 2) • (innerSL ℝ y).smulRight (innerSL ℝ y) := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      rw [capForm, hf.dslope_zero_of_ne_zero (norm_ne_zero_iff.2 hy)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact ((hq.pow 2).smul contDiffAt_const).add
      (((contDiffAt_const.sub (hq.pow 2)).div (hnorm.pow 2) (by positivity)).smul
        hrank.contDiffAt)

/-- The cap form dominates `min (f(‖x‖) / ‖x‖)² 1` times the Euclidean form on the diagonal. -/
private theorem min_mul_inner_self_le_capForm (x v : V) :
    min (dslope f 0 ‖x‖ ^ 2) 1 * ⟪v, v⟫_ℝ ≤ capForm V f x v v := by
  rw [capForm_apply, real_inner_self_eq_norm_sq]
  set a := dslope f 0 ‖x‖ ^ 2
  have ha : 0 < a := pow_pos (hf.dslope_zero_pos (norm_nonneg x)) 2
  have hm₁ : min a 1 ≤ a := min_le_left _ _
  have hm₂ : min a 1 ≤ 1 := min_le_right _ _
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [inner_zero_left, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right hm₁ (sq_nonneg _)
  -- With `t = ⟪x, v⟫² / ‖x‖² ∈ [0, ‖v‖²]`, the form is `a (‖v‖² - t) + t`.
  have hN : 0 < ‖x‖ ^ 2 := by positivity
  set t := ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2
  have ht₀ : 0 ≤ t := by positivity
  have ht₁ : t ≤ ‖v‖ ^ 2 := by
    rw [div_le_iff₀ hN]
    have := abs_real_inner_le_norm x v
    nlinarith [abs_nonneg ⟪x, v⟫_ℝ, sq_abs ⟪x, v⟫_ℝ, norm_nonneg x, norm_nonneg v]
  have heq : (1 - a) / ‖x‖ ^ 2 * (⟪x, v⟫_ℝ * ⟪x, v⟫_ℝ) = (1 - a) * t := by
    simp only [t]
    ring
  rw [heq]
  nlinarith [mul_nonneg (sub_nonneg.2 hm₁) (sub_nonneg.2 ht₁), mul_nonneg (sub_nonneg.2 hm₂) ht₀]

/-- The cap form is coercive at every point: it dominates `min (f(‖x‖) / ‖x‖)² 1` times the
Euclidean form. -/
private theorem isCoercive_capForm (x : V) : IsCoercive (capForm V f x) :=
  ⟨_, lt_min (pow_pos (hf.dslope_zero_pos (norm_nonneg x)) 2) one_pos, fun v ↦ by
    rw [mul_assoc, ← sq, ← real_inner_self_eq_norm_sq]
    exact hf.min_mul_inner_self_le_capForm x v⟩

omit hf in
private theorem capForm_symm (x v w : V) : capForm V f x v w = capForm V f x w v := by
  rw [capForm_apply, capForm_apply, real_inner_comm v w]
  ring

variable (V) in
/-- **The standard cap metric** on a real inner product space `V`. At `x`, tangent vectors
`v`, `w` are paired to
`(f(‖x‖) / ‖x‖)² ⟪v, w⟫ + ((1 - (f(‖x‖) / ‖x‖)²) / ‖x‖²) ⟪x, v⟫ ⟪x, w⟫`,
the Euclidean metric at the tip `x = 0`. The radial direction has unit length and the sphere of
radius `r` about the tip is scaled by `f(r) / r`, so in polar coordinates this is
`dr² + f(r)² g_(Sⁿ)` (`TauCeti.IsStandardCapProfile.metric_inner_mfderiv_standardCapPolar`). Near
the tip, where `f(r) = 2 sin (r / 2)`, its coefficients `(f(‖x‖) / ‖x‖)²` and
`(1 - (f(‖x‖) / ‖x‖)²) / ‖x‖²` are analytic functions of `‖x‖²`, so it is smooth across the
tip. -/
def metric : ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
  coerciveRiemannianMetric (capForm V f) hf.contDiff_capForm capForm_symm hf.isCoercive_capForm

/-- The standard cap metric pairs `v` and `w` at `x` to
`a ⟪v, w⟫ + ((1 - a) / ‖x‖²) ⟪x, v⟫ ⟪x, w⟫`, where `a = (dslope f 0 ‖x‖)²` is `(f(‖x‖) / ‖x‖)²`
away from the tip and `1` at the tip. -/
@[simp]
theorem metric_inner (x : V) (v w : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v w = dslope f 0 ‖x‖ ^ 2 *
        ⟪NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w⟫_ℝ +
      (1 - dslope f 0 ‖x‖ ^ 2) / ‖x‖ ^ 2 *
        (⟪x, NormedSpace.fromTangentSpace x v⟫_ℝ * ⟪x, NormedSpace.fromTangentSpace x w⟫_ℝ) :=
  (coerciveRiemannianMetric_inner _ _ _ _ x v w).trans (capForm_apply _ _ _)

/-- Away from the tip, the standard cap metric is
`(f(‖x‖) / ‖x‖)² ⟪v, w⟫ + ((1 - (f(‖x‖) / ‖x‖)²) / ‖x‖²) ⟪x, v⟫ ⟪x, w⟫`. -/
theorem metric_inner_of_ne_zero {x : V} (hx : x ≠ 0) (v w : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v w = (f ‖x‖ / ‖x‖) ^ 2 *
        ⟪NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w⟫_ℝ +
      (1 - (f ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2 *
        (⟪x, NormedSpace.fromTangentSpace x v⟫_ℝ * ⟪x, NormedSpace.fromTangentSpace x w⟫_ℝ) := by
  rw [metric_inner, hf.dslope_zero_of_ne_zero (norm_ne_zero_iff.2 hx)]

/-- At the tip, the standard cap metric is the Euclidean metric. -/
theorem metric_inner_zero (v w : TangentSpace 𝓘(ℝ, V) (0 : V)) :
    (hf.metric V).inner 0 v w =
      ⟪NormedSpace.fromTangentSpace (0 : V) v, NormedSpace.fromTangentSpace (0 : V) w⟫_ℝ := by
  rw [metric_inner, norm_zero, dslope_same, hf.deriv_zero]
  simp

section Polar

open Metric (sphere)
open TauCeti.Manifold

variable {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

/-- **The standard cap metric in polar coordinates** is `dr² + f(r)² g_(Sⁿ)`: polar coordinates
`(r, u) ↦ r u` on `(0, ∞) × Sⁿ` pull the standard cap metric back to the punctured standard cap
metric `TauCeti.IsStandardCapProfile.puncturedMetric`. -/
theorem metric_inner_mfderiv_standardCapPolar (p : standardCapRadialDomain × sphere (0 : V) 1)
    (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    (hf.metric V).inner (standardCapPolar V p)
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          (standardCapPolar V) p v)
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          (standardCapPolar V) p w) =
      (hf.puncturedMetric V).inner p v w := by
  have hr : 0 < (p.1 : ℝ) := p.1.property
  have hnorm := norm_standardCapPolar p
  have hx : standardCapPolar V p ≠ 0 := norm_ne_zero_iff.1 (hnorm.trans_ne hr.ne')
  have hu : ⟪(p.2 : V), (p.2 : V)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p.2, one_pow]
  have hξ (v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) : ⟪(p.2 : V),
      mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2⟫_ℝ = 0 :=
    inner_coe_mvfderiv_subtypeVal_sphere p.2 _
  have hξ' (v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
      ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2 (tangentSpaceProdEquiv p v).2,
        (p.2 : V)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hξ v
  rw [hf.metric_inner_of_ne_zero hx, hnorm, NormedSpace.fromTangentSpace_apply,
    NormedSpace.fromTangentSpace_apply, ← mvfderiv_apply_eq_mfderiv_apply,
    ← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_standardCapPolar_apply,
    mvfderiv_standardCapPolar_apply, puncturedMetric_inner,
    ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
    ContMDiffRiemannianMetric.ofLE_inner, ContMDiffRiemannianMetric.ofLE_inner,
    sphereRoundMetric_inner]
  simp only [standardCapPolar_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hu, hξ, hξ', riemannianMetricVectorSpace_inner, Real.inner_apply]
  field_simp
  ring

/-- **The punctured standard cap is the standard cap in polar coordinates**: pulling the standard
cap metric back along `(r, u) ↦ r u` gives the punctured standard cap metric. -/
theorem pullback_metric_standardCapPolar :
    (hf.metric V).pullback (standardCapPolar V) contMDiff_standardCapPolar
        injective_mfderiv_standardCapPolar =
      hf.puncturedMetric (n := n) V := by
  ext p v w
  rw [ContMDiffRiemannianMetric.pullback_inner, hf.metric_inner_mfderiv_standardCapPolar]

end Polar

/-! ### Scalar curvature -/

section ScalarCurvature

open Metric (sphere)
open Module

variable [FiniteDimensional ℝ V]

omit hf in
/-- A nontrivial finite-dimensional space has dimension `n + 1` for some `n`, recorded as the
instance that the polar coordinates on `(0, ∞) × Sⁿ` take. -/
private theorem exists_fact_finrank_eq_succ [Nontrivial V] :
    ∃ n : ℕ, Fact (finrank ℝ V = n + 1) :=
  (Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := V)).ne').imp fun _ hn ↦ ⟨hn⟩

/-- The scalar curvature of the standard cap at `r u`, for `r > 0` and `u` in the unit sphere,
is the scalar curvature of the punctured standard cap at `(r, u)`. -/
theorem scalarCurvature_metric_standardCapPolar {n : ℕ} [Fact (finrank ℝ V = n + 1)]
    (p : standardCapRadialDomain × sphere (0 : V) 1) :
    (hf.metric V).scalarCurvature (standardCapPolar V p) =
      (hf.puncturedMetric (n := n) V).scalarCurvature p := by
  rw [← hf.pullback_metric_standardCapPolar,
    ContMDiffRiemannianMetric.scalarCurvature_pullback_of_isInvertible _ contMDiff_standardCapPolar
      isInvertible_mfderiv_standardCapPolar]

/-- Away from the tip, the scalar curvature of the standard cap at `x` is the scalar curvature of
the punctured standard cap at a point of `(0, ∞) × Sⁿ` of radius `‖x‖`. -/
theorem exists_scalarCurvature_metric_eq_puncturedMetric {n : ℕ} [Fact (finrank ℝ V = n + 1)]
    {x : V} (hx : x ≠ 0) :
    ∃ p : standardCapRadialDomain × sphere (0 : V) 1, (p.1 : ℝ) = ‖x‖ ∧
      (hf.metric V).scalarCurvature x = (hf.puncturedMetric (n := n) V).scalarCurvature p := by
  obtain ⟨p, rfl⟩ : x ∈ range (standardCapPolar V) := by rwa [range_standardCapPolar]
  exact ⟨p, (norm_standardCapPolar p).symm, hf.scalarCurvature_metric_standardCapPolar p⟩

/-- **The standard cap has nonnegative scalar curvature**, also at its tip. -/
theorem scalarCurvature_metric_nonneg (x : V) : 0 ≤ (hf.metric V).scalarCurvature x := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ((hf.metric V).scalarCurvature_eq_zero_of_subsingleton x).ge
  obtain ⟨n, _⟩ := exists_fact_finrank_eq_succ (V := V)
  refine (hf.metric V).le_scalarCurvature_of_dense (dense_compl_singleton 0) (fun y hy ↦ ?_) x
  obtain ⟨p, -, hp⟩ := hf.exists_scalarCurvature_metric_eq_puncturedMetric (n := n) hy
  exact hp ▸ hf.scalarCurvature_puncturedMetric_nonneg p

/-- **The cylindrical end of the standard cap**: far from the tip the scalar curvature of the
standard cap on a space of dimension `d` is `(d - 1)(d - 2) / 2`, the scalar curvature of the round
cylinder `ℝ × S^(d - 1)(√2)`. For `V = ℝ³` it is one. -/
theorem exists_scalarCurvature_metric_eq_cylinder :
    ∃ R > 0, ∀ x : V, R ≤ ‖x‖ →
      (hf.metric V).scalarCurvature x = (finrank ℝ V - 1) * (finrank ℝ V - 2) / 2 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨1, one_pos, fun x hx ↦ by simp [Subsingleton.elim x 0] at hx; linarith⟩
  obtain ⟨n, hn⟩ := exists_fact_finrank_eq_succ (V := V)
  obtain ⟨R, hR, h⟩ := hf.exists_scalarCurvature_puncturedMetric_eq_cylinder (V := V) (n := n)
  refine ⟨R, hR, fun x hx ↦ ?_⟩
  obtain ⟨p, hp, hpx⟩ :=
    hf.exists_scalarCurvature_metric_eq_puncturedMetric (n := n) (norm_pos_iff.1 (hR.trans_le hx))
  rw [hpx, h p (hp ▸ hx), hn.out]
  push_cast
  ring

/-- **The round tip of the standard cap**: near the tip, including at the tip itself, the scalar
curvature of the standard cap on a space of dimension `d` is `d (d - 1) / 4`, the scalar curvature
of the round sphere of radius `2`. -/
theorem exists_scalarCurvature_metric_eq_round :
    ∃ r₀ > 0, ∀ x : V, ‖x‖ < r₀ →
      (hf.metric V).scalarCurvature x = finrank ℝ V * (finrank ℝ V - 1) / 4 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨1, one_pos, fun x _ ↦ by
    simp [(hf.metric V).scalarCurvature_eq_zero_of_subsingleton,
      Module.finrank_zero_of_subsingleton]⟩
  obtain ⟨n, hn⟩ := exists_fact_finrank_eq_succ (V := V)
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_scalarCurvature_puncturedMetric_eq_round (V := V) (n := n)
  have hne (x : V) (hx : ‖x‖ < r₀) (hx0 : x ≠ 0) :
      (hf.metric V).scalarCurvature x = finrank ℝ V * (finrank ℝ V - 1) / 4 := by
    obtain ⟨p, hp, hpx⟩ := hf.exists_scalarCurvature_metric_eq_puncturedMetric (n := n) hx0
    rw [hpx, h p (hp ▸ hx), hn.out]
    push_cast
    ring
  refine ⟨r₀, hr₀, fun x hx ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact (hf.metric V).scalarCurvature_eq_of_eventually_nhdsNE <| eventually_nhdsWithin_iff.2 <|
      Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr₀) fun y hy hy0 ↦
        hne y (mem_ball_zero_iff.1 hy) hy0
  · exact hne x hx hx0

end ScalarCurvature

end IsStandardCapProfile

end TauCeti
