/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Normal
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FirstVariation
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# The second variation of length

Let `F : ℝ → ℝ → M` be a two-parameter family of curves in a Riemannian manifold, with central
curve `γ = F 0`, variation field `V(t) = ∂_s F (0, t)` and transverse acceleration
`A(t) = D_s ∂_s F (0, t)`. This file computes the second derivative at `s = 0` of the length
`L(s) = ∫_a^b ‖∂_t F (s, t)‖ dt` of the curves `F s`, for a family which is `C³` near
`{0} × [a, b]`.

At a regular parameter, the speed is the square root of the squared speed, whose first two
transverse derivatives are `2 ⟪D_t V, γ'⟫` and `2 (‖D_t V‖² - ⟪R(V, γ') γ', V⟫ + ⟪D_t A, γ'⟫)`
(`TauCeti.Manifold.hasDerivAt_deriv_norm_sq_curveVelocity`). Hence the second transverse
derivative of the speed is

`(‖D_t V‖² - ⟪R(V, γ') γ', V⟫ + ⟪D_t A, γ'⟫) / ‖γ'‖ - ⟪D_t V, γ'⟫² / ‖γ'‖³`.

If `γ` has constant speed `C > 0`, integrating and comparing with the second variation of energy
`TauCeti.Manifold.hasDerivAt_deriv_energy` gives

`L''(0) = E''(0) / C - (∫_a^b ⟪D_t V, γ'⟫² dt) / C³`.

Along a geodesic, write `V^⊥ = V - ⟪V, γ'⟫ γ' / ‖γ'‖²` for the normal part of `V`, the orthogonal
projection of `V` onto the orthogonal complement of the velocity. Covariant differentiation
commutes with this projection, and the curvature term does not see the tangential part, so the
index-form integrand of `V^⊥` is that of `V` minus `⟪D_t V, γ'⟫² / ‖γ'‖²`
(`TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton`, in
`TauCeti.Geometry.Manifold.Riemannian.IndexForm.Normal`). For a unit-speed
geodesic this gives the **second variation of length with free endpoints**

`L''(0) = ∫_a^b (‖D_t V^⊥‖² - ⟪R(V^⊥, γ') γ', V^⊥⟫) dt + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`.

Only the normal part of `V` enters the integral. In particular, a variation with fixed endpoints
whose variation field is tangent to `γ`, such as a reparametrization, has vanishing second
variation of length.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_norm_curveVelocity`: the second transverse derivative of the
  speed at a regular parameter.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero`: the second
  variation of length of a regular curve, as the integral of the second transverse derivatives of
  the speed.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength`: the second variation of length of a
  constant-speed curve, in terms of the second variation of energy.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one`: **the second
  variation of length** of a unit-speed geodesic with free endpoints, and its constant-speed
  version `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_acceleration_eq_zero`.
* `IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one`:
  with fixed endpoints, the second variation of length of a unit-speed geodesic is the index form
  of the normal part of the variation field, and it vanishes for tangential variation fields
  (`TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_mem_span`).
* `hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn`,
  `IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn`,
  `hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_curveVelocityLift_eq`,
  `hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_mem_span_curveVelocity`,
  and `IsGeodesicCurveOn.hasDerivAt_deriv_toReal_pathELength_exponentialVariation`:
  second variation of length along `IsGeodesicCurveOn` geodesics, smoothly closed variations, and
  exponential variations.
* `indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength`,
  `IsFixedEndpointVariation.indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength`,
  `indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength_of_curveVelocityLift_eq`,
  `indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength_exponentialVariation`,
  and `eventually_pathELength_exponentialVariation_lt_of_indexForm_sub_starProjection_neg`:
  normal index-form nonnegativity at local minima of length and strict `pathELength` shortening.

## References

* J. Cheeger, D. G. Ebin, *Comparison Theorems in Riemannian Geometry*, North-Holland, 1975,
  Ch. 1, the second variation formula for arc length.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 10, the second
  variation formula.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-! ### The second transverse derivative of the speed -/

omit [T2Space M] in
/-- The squared speed `s ↦ ‖∂_t F (s, t)‖²` is differentiable at every `q` where the family is
`C²` at `(q, t)`. -/
private theorem differentiableAt_norm_sq_curveVelocity {q t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t)) :
    DifferentiableAt ℝ (fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) q := by
  have hshift : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F (q + z.1) z.2) (0, t) :=
    hF.comp_of_eq (contMDiff_iff_contDiff.mpr
      ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)).contMDiffAt (by simp)
  have hd : DifferentiableAt ℝ (fun s ↦ ‖curveVelocity I (F (q + s)) t‖ ^ 2) 0 :=
    (hasDerivAt_norm_sq_curveVelocity (F := fun s ↦ F (q + s)) hshift).differentiableAt
  have h := (differentiableAt_comp_sub_const (f := fun s ↦ ‖curveVelocity I (F (q + s)) t‖ ^ 2)
    (a := q) (b := q)).2 (by rwa [sub_self])
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [add_sub_cancel]

/-- **The second transverse derivative of the speed.** At a parameter `t` where the family is `C³`
and the central curve `γ = F 0` has nonzero velocity, the derivative at `s = 0` of
`s ↦ d/ds ‖∂_t F (s, t)‖` is

`(I_t(V, V) + ⟪D_t A(t), γ'(t)⟫) / ‖γ'(t)‖ - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖³`,

where `V` is the variation field, `A(r) = D_s ∂_s F (0, r)` is the transverse acceleration and
`I_t(V, V) = ‖D_t V‖² - ⟪R(V, γ') γ', V⟫` is the integrand of the index form. -/
theorem hasDerivAt_deriv_norm_curveVelocity {t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ ‖curveVelocity I (F s) t‖)
      ((indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
          ⟪alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t,
            curveVelocity I (F 0) t⟫_ℝ) / ‖curveVelocity I (F 0) t‖ -
        ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
            curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 3) 0 := by
  set g : ℝ → ℝ := fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2
  have hF2 : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    hF.of_le (by norm_num)
  have hnear : ∀ᶠ q in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t) :=
    ((continuous_id.prodMk continuous_const).tendsto 0).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF2)
  have hnorm := hasDerivAt_norm_curveVelocity hF2 hγ
  have hne : ∀ᶠ q in 𝓝 0, ‖curveVelocity I (F q) t‖ ≠ 0 :=
    hnorm.continuousAt.eventually_ne (norm_ne_zero_iff.2 hγ)
  -- Near `0`, the derivative of the speed `√g` is `g' / (2 ‖∂_t F‖)`.
  have hderiv : deriv (fun s ↦ ‖curveVelocity I (F s) t‖) =ᶠ[𝓝 0]
      fun q ↦ deriv g q / (2 * ‖curveVelocity I (F q) t‖) := by
    filter_upwards [hnear, hne] with q hq hqne
    have h := (differentiableAt_norm_sq_curveVelocity hq).hasDerivAt.sqrt
      (pow_ne_zero 2 hqne)
    simp only [Real.sqrt_sq (norm_nonneg _)] at h
    exact h.deriv
  have hg' := (hasDerivAt_norm_sq_curveVelocity hF2).deriv
  refine ((HasDerivAt.div (hasDerivAt_deriv_norm_sq_curveVelocity hF) (hnorm.const_mul 2)
    (mul_ne_zero two_ne_zero (norm_ne_zero_iff.2 hγ))).congr_of_eventuallyEq hderiv).congr_deriv ?_
  rw [hg']
  have hpos : ‖curveVelocity I (F 0) t‖ ≠ 0 := norm_ne_zero_iff.2 hγ
  field_simp

/-! ### Differentiating the length twice -/

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Differentiating the length twice under the integral sign.** For a family which is `C³` at
every point of `{0} × [a, b]` and whose central curve has nonzero velocity on `[a, b]`, the
derivative of the length of `F s` has at `s = 0` the derivative the integral of the second
transverse derivatives of the speed. -/
private theorem hasDerivAt_deriv_toReal_pathELength_integral {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (∫ t in a..b, deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖) 0) 0 := by
  obtain ⟨W, hWo, hsub, hL, hlength⟩ :=
    exists_isOpen_contDiffOn_norm_curveVelocity (m := 2) (by norm_num) (by simp) hab hF hγ
  exact (TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn hWo hL hsub).2
    |>.congr_of_eventuallyEq hlength.deriv

/-- **The second variation of length of a regular curve.** Let `F` be a two-parameter family which
is `C³` at every point of `{0} × [a, b]`, whose central curve `γ = F 0` has nonzero velocity on
`[a, b]`. Then the derivative of the length of `F s` between `a` and `b` is differentiable at
`s = 0`, with derivative

`∫_a^b (I_t(V, V) + ⟪D_t A, γ'⟫) / ‖γ'‖ - ⟪D_t V, γ'⟫² / ‖γ'‖³ dt`,

where `V` is the variation field, `A(t) = D_s ∂_s F (0, t)` the transverse acceleration and `I_t`
the integrand of the index form. The endpoints of the curves `F s` are not required to be fixed. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (∫ t in a..b,
        ((indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
            ⟪alongCurve (leviCivitaConnection I M) (F 0)
              (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t,
              curveVelocity I (F 0) t⟫_ℝ) / ‖curveVelocity I (F 0) t‖ -
          ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
              curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 3)) 0 :=
  (hasDerivAt_deriv_toReal_pathELength_integral hab hF hγ).congr_deriv
    (intervalIntegral.integral_congr fun t ht ↦ by
      rw [uIcc_of_le hab] at ht
      exact (hasDerivAt_deriv_norm_curveVelocity (hF t ht) (hγ t ht)).deriv)

/-- **The second variation of length of a constant-speed curve.** Let `F` be a two-parameter
family which is `C³` at every point of `{0} × [a, b]`, whose central curve `γ = F 0` has constant
speed `C > 0` on `[a, b]`. Then the derivative of the length of `F s` between `a` and `b` is
differentiable at `s = 0`, with derivative

`(I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A, D_t γ'⟫ dt) / C -
  (∫_a^b ⟪D_t V, γ'⟫² dt) / C³`,

where `I` is the index form, `V` the variation field and `A(t) = D_s ∂_s F (0, t)` the transverse
acceleration. The first term is the second variation of energy
`TauCeti.Manifold.hasDerivAt_deriv_energy` divided by `C`. -/
theorem hasDerivAt_deriv_toReal_pathELength {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0) (variationField I F) (variationField I F) a b +
          ⟪acceleration (leviCivitaConnection I M) (fun q ↦ F q b) 0, curveVelocity I (F 0) b⟫_ℝ -
          ⟪acceleration (leviCivitaConnection I M) (fun q ↦ F q a) 0, curveVelocity I (F 0) a⟫_ℝ -
          ∫ t in a..b, ⟪acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0,
            acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) / C -
        (∫ t in a..b, ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
          curveVelocity I (F 0) t⟫_ℝ ^ 2) / C ^ 3) 0 := by
  have hγ0 : ∀ t ∈ Icc a b, curveVelocity I (F 0) t ≠ 0 := fun t ht ↦
    norm_ne_zero_iff.1 (by rw [hγ t ht]; exact hC.ne')
  refine (hasDerivAt_deriv_toReal_pathELength_integral hab hF hγ0).congr_deriv ?_
  have hF' : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) := by
    rwa [uIcc_of_le hab]
  -- The second variation of energy is half the integral of the second derivatives of the
  -- squared speed.
  obtain ⟨hint, hE⟩ := hasDerivAt_deriv_energy_integral hF'
  have henergy := hE.unique (hasDerivAt_deriv_energy hF')
  -- Pointwise on `[a, b]`, the second derivative of the speed is the second derivative of the
  -- squared speed divided by `2 C`, minus `⟪D_t V, γ'⟫² / C³`.
  set c : ℝ → ℝ := fun t ↦ ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
    curveVelocity I (F 0) t⟫_ℝ
  have hpt : EqOn (fun t ↦ deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖) 0)
      (fun t ↦ deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0 / 2 / C - c t ^ 2 / C ^ 3)
      (uIcc a b) := fun t ht ↦ by
    rw [uIcc_of_le hab] at ht
    dsimp only
    rw [(hasDerivAt_deriv_norm_curveVelocity (hF t ht) (hγ0 t ht)).deriv,
      (hasDerivAt_deriv_norm_sq_curveVelocity (hF t ht)).deriv, hγ t ht]
    ring
  have hcint : IntervalIntegrable (fun t ↦ c t ^ 2 / C ^ 3) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (((continuousAt_inner_alongCurve_variationField_curveVelocity
        ((hF' t ht).of_le (by norm_num))).pow 2).div_const _).continuousWithinAt
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub
    ((hint.div_const 2).div_const C) hcint, intervalIntegral.integral_div,
    intervalIntegral.integral_div, intervalIntegral.integral_div, henergy]

/-! ### The second variation of length along a geodesic -/

/-- **The second variation of length of a constant-speed geodesic.** Let `F` be a two-parameter
family which is `C³` at every point of `{0} × [a, b]`, whose central curve `γ = F 0` has
vanishing covariant acceleration on `(a, b)` and constant speed `C > 0` on `[a, b]`. Let
`V^⊥ = V - proj_{γ'} V` be the normal part of the variation field `V`, and `A(t) = D_s ∂_s F (0, t)`
the transverse acceleration. Then the derivative of the length of `F s` between `a` and `b` is
differentiable at `s = 0`, with derivative `(I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`,
where `I` is the index form. The endpoints of the curves `F s` are not required to be fixed. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_acceleration_eq_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hacc : ∀ t ∈ Ioo a b, acceleration (leviCivitaConnection I M) (F 0) t = 0)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0)
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b +
          ⟪acceleration (leviCivitaConnection I M) (fun q ↦ F q b) 0, curveVelocity I (F 0) b⟫_ℝ -
          ⟪acceleration (leviCivitaConnection I M) (fun q ↦ F q a) 0,
            curveVelocity I (F 0) a⟫_ℝ) / C) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength hab hF hC hγ).congr_deriv ?_
  set cov := leviCivitaConnection I M
  set V := variationField I F
  set c : ℝ → ℝ := fun t ↦ ⟪alongCurve cov (F 0) V t, curveVelocity I (F 0) t⟫_ℝ
  -- the acceleration term of the central curve vanishes
  have hzero : ∫ t in a..b, ⟪acceleration cov (fun q ↦ F q t) 0, acceleration cov (F 0) t⟫_ℝ =
      0 := by
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ 0) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [hacc t (by rwa [uIoo_of_le hab] at ht), inner_zero_right]
  -- on `(a, b)` the central curve is a geodesic
  have hgeod : IsGeodesicCurveOn I (F 0) (Ioo a b) :=
    (isGeodesicCurveOn_iff_of_isOpen isOpen_Ioo).2 ⟨fun t ht ↦
      ((hF t (Ioo_subset_Icc_self ht)).comp t (contMDiff_iff_contDiff.mpr
        (contDiff_prodMk_right (n := 3) (0 : ℝ))).contMDiffAt).contMDiffWithinAt.of_le
          (by norm_num), hacc⟩
  -- the index form of the normal part is `I(V, V) - ∫ ⟪D_t V, γ'⟫² / C²`
  have hVlift : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (F 0 r) (V r))
      (uIcc a b) := fun t ht ↦ by
    rw [uIcc_of_le hab] at ht
    exact ((hF t ht).contMDiffAt_variationField (by norm_num)).contMDiffWithinAt
  have hcint : IntervalIntegrable (fun t ↦ c t ^ 2 / C ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦ by
      rw [uIcc_of_le hab] at ht
      exact (((continuousAt_inner_alongCurve_variationField_curveVelocity
        ((hF t ht).of_le (by norm_num))).pow 2).div_const _).continuousWithinAt
  have hnormal : indexForm I (F 0)
      (fun t ↦ V t - (ℝ ∙ curveVelocity I (F 0) t).starProjection (V t))
      (fun t ↦ V t - (ℝ ∙ curveVelocity I (F 0) t).starProjection (V t)) a b =
        indexForm I (F 0) V V a b - (∫ t in a..b, c t ^ 2) / C ^ 2 := by
    rw [indexForm_def, indexForm_def, ← intervalIntegral.integral_div,
      ← intervalIntegral.integral_sub (intervalIntegrable_indexFormIntegrand hVlift hVlift) hcint]
    refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
    rw [uIoo_of_le hab] at ht
    have hdiff : DifferentiableAt ℝ
        (sectionCoord ℝ (F := E) (F 0) (variationField I F) (F 0 t)) t := by
      rw [variationField_def]
      exact ((hF t (Ioo_subset_Icc_self ht)).of_le (by norm_num))
        |>.differentiableAt_sectionCoord_curveVelocity_fst (f := F)
          (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t))
    rw [hgeod.indexFormIntegrand_sub_starProjection_singleton isPreconnected_Ioo
      (isOpen_Ioo.mem_nhds ht) hdiff]
    -- `‖proj_{γ'} D_t V‖² = ⟪γ', D_t V⟫² / ‖γ'‖²`
    simp only [Submodule.starProjection_singleton, norm_smul, norm_div, norm_pow, Real.norm_eq_abs,
      RCLike.ofReal_real_eq_id, id_eq, mul_pow, div_pow, sq_abs, hγ t (Ioo_subset_Icc_self ht),
      abs_of_pos hC, real_inner_comm _ (curveVelocity I (F 0) t)]
    field_simp
    ring
  rw [hzero, hnormal]
  field_simp
  ring

/-- **The second variation of length of a unit-speed geodesic.** Let `F` be a two-parameter family
which is `C³` at every point of `{0} × [a, b]`, whose central curve `γ = F 0` has vanishing
covariant acceleration on `(a, b)` and unit speed on `[a, b]`. Then the derivative of the length
of `F s` between `a` and `b` is differentiable at `s = 0`, with derivative

`∫_a^b (‖D_t V^⊥‖² - ⟪R(V^⊥, γ') γ', V^⊥⟫) dt + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`,

where `V^⊥ = V - ⟪V, γ'⟫ γ'` is the normal part of the variation field `V`, written as
`V - proj_{γ'} V`, and `A(t) = D_s ∂_s F (0, t)` is the transverse acceleration. The integral is
the index form of `V^⊥`. The endpoints of the curves `F s` are not required to be fixed. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one {a b : ℝ}
    (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hacc : ∀ t ∈ Ioo a b, acceleration (leviCivitaConnection I M) (F 0) t = 0)
    (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun q ↦ F q b) 0, curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun q ↦ F q a) 0, curveVelocity I (F 0) a⟫_ℝ)
      0 := by
  simpa only [div_one] using
    hasDerivAt_deriv_toReal_pathELength_of_acceleration_eq_zero hab hF hacc zero_lt_one hγ

/-- **The second variation of length with fixed endpoints.** For a `C³` variation `F` with fixed
endpoints of a curve `γ = F 0` which has vanishing covariant acceleration on `(a, b)` and unit
speed on `[a, b]`, the derivative of the length of `F s` between `a` and `b` is differentiable at
`s = 0`, with derivative the index form `I(V^⊥, V^⊥)` of the normal part
`V^⊥ = V - proj_{γ'} V` of the variation field `V`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one
    {a b : ℝ} (hab : a ≤ b) (hF : IsFixedEndpointVariation I 3 F a b)
    (hacc : ∀ t ∈ Ioo a b, acceleration (leviCivitaConnection I M) (F 0) t = 0)
    (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b) 0 := by
  have hA {t : ℝ} (h : (fun q ↦ F q t) =ᶠ[𝓝 0] fun _ ↦ F 0 t) :
      acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0 = 0 := by
    rw [h.acceleration_eq, acceleration_const]
  have hF' : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    fun t ht ↦ hF.contMDiffAt t (by rwa [uIcc_of_le hab])
  simpa only [hA hF.eventually_apply_left, hA hF.eventually_apply_right, inner_zero_left,
    add_zero, sub_zero] using
    TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one hab hF' hacc
      hγ

/-- **Tangential variations do not change length to second order.** For a `C³` variation `F` with
fixed endpoints of a curve `γ = F 0` which has vanishing covariant acceleration on `(a, b)` and
unit speed on `[a, b]`, if the variation field is tangent to `γ` on `(a, b)`, as for a family of
reparametrizations, then the second derivative of the length of `F s` vanishes at `s = 0`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_mem_span
    {a b : ℝ} (hab : a ≤ b) (hF : IsFixedEndpointVariation I 3 F a b)
    (hacc : ∀ t ∈ Ioo a b, acceleration (leviCivitaConnection I M) (F 0) t = 0)
    (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1)
    (hV : ∀ t ∈ Ioo a b, variationField I F t ∈ ℝ ∙ curveVelocity I (F 0) t) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 0 := by
  refine (hF.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one hab hacc
    hγ).congr_deriv ?_
  have hpt : ∀ t ∈ uIoo a b, variationField I F t -
      (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t) = 0 := fun t ht ↦ by
    rw [uIoo_of_le hab] at ht
    rw [(Submodule.starProjection_eq_self_iff).2 (hV t ht), sub_self]
  have hzero : indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b =
      indexForm I (F 0) (fun _ ↦ 0) (fun _ ↦ 0) a b :=
    indexForm_congr (fun _ _ ↦ rfl) (fun t ht ↦ heq_of_eq (hpt t ht))
      (fun t ht ↦ heq_of_eq (hpt t ht))
  rw [hzero, indexForm_fun_zero_left]

/-- **Second variation of length of a constant-speed geodesic.** Let `F` be `C³` along
`{0} × [a, b]` with `a ≤ b`, whose central curve `γ = F 0` is a geodesic on `(a, b)` of constant
speed `C > 0` on `[a, b]`. Then

`d²/ds² L(F s) |₀ = (I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`,

where `V^⊥(t) = V(t) - (ℝ ∙ γ'(t)).starProjection (V(t))` is the normal component of the
variation field `V = ∂_s F (0, ·)` and `A(t) = D_s ∂_s F (0, t)` is the transverse acceleration. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0)
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C) 0 := by
  have hacc : ∀ t ∈ Ioo a b, acceleration (leviCivitaConnection I M) (F 0) t = 0 := fun t ht ↦ by
    rw [← accelerationWithin_of_mem_nhds (leviCivitaConnection I M) (F 0)
      (isOpen_Ioo.mem_nhds ht)]
    exact hγ.accelerationWithin_eq_zero t ht
  exact hasDerivAt_deriv_toReal_pathELength_of_acceleration_eq_zero hab hF hacc hC hspeed

private theorem indexForm_sub_starProjection_eq_of_norm_curveVelocity_eq_one
    {a b : ℝ} {γ : ℝ → M} (hspeed : ∀ t ∈ uIoo a b, ‖curveVelocity I γ t‖ = 1)
    (V : ∀ t, TangentSpace I (γ t)) :
    indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b =
      indexForm I γ
        (fun t ↦ V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t)
        (fun t ↦ V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t) a b := by
  have hproj (t : ℝ) (ht : t ∈ uIoo a b) :
      HEq (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t) := by
    rw [heq_eq_eq, Submodule.starProjection_unit_singleton ℝ (hspeed t ht), real_inner_comm]
  exact indexForm_congr (fun _ _ ↦ rfl) hproj hproj

/-- **Second variation of length for a fixed-endpoint variation of a constant-speed geodesic.** For
a `C³` fixed-endpoint variation `F` on `[a, b]` (`a ≤ b`) whose central curve `γ = F 0` is a
geodesic on `(a, b)` of constant speed `C > 0` on `[a, b]`, the second derivative of length at
`s = 0` is `I(V^⊥, V^⊥) / C`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn
    {a b : ℝ} (hab : a ≤ b) (hF : IsFixedEndpointVariation I 3 F a b)
    (hγ : IsGeodesicCurveOn I (F 0) (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C) 0 := by
  refine (TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab
    (fun t ht ↦ hF.contMDiffAt t (by rwa [uIcc_of_le hab])) hγ hC hspeed).congr_deriv ?_
  simp [hF.acceleration_left_eq_zero, hF.acceleration_right_eq_zero]

/-- **Second variation of length of a smoothly closed geodesic.** If `F` is `C³` along
`{0} × [a, b]` (`a ≤ b`), its nearby curves are closed (`F s a = F s b` near `0`), and its central
curve `γ = F 0` is a geodesic on `(a, b)` of constant speed `C > 0` on `[a, b]` with matching
endpoint velocity lifts `curveVelocityLift I γ a = curveVelocityLift I γ b`, then the boundary
transverse-acceleration pairings cancel and `d²/ds² L(F s) |₀ = I(V^⊥, V^⊥) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_curveVelocityLift_eq
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : curveVelocityLift I (F 0) a = curveVelocityLift I (F 0) b) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hγ hC hspeed).congr_deriv
    ?_
  rw [inner_acceleration_fst_curveVelocity_eq_of_curveVelocityLift_eq hper hvel,
    add_sub_cancel_right]

/-- **Tangential variations do not affect the second variation of length.** Along a constant-speed
geodesic (`C > 0`) on `(a, b)` (`a ≤ b`), if the variation field `V` is tangential on `(a, b)`,
then `I(V^⊥, V^⊥) = 0`, leaving only the boundary term `(⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_mem_span_curveVelocity
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (htan : ∀ t ∈ Ioo a b, variationField I F t ∈ ℝ ∙ curveVelocity I (F 0) t) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hγ hC hspeed).congr_deriv
    ?_
  have hzero (t : ℝ) (ht : t ∈ uIoo a b) : HEq (variationField I F t -
      (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      ((0 : ∀ r, TangentSpace I (F 0 r)) t) := by
    rw [uIoo_of_le hab] at ht; simp [Submodule.starProjection_eq_self_iff.mpr (htan t ht)]
  rw [indexForm_congr (fun _ _ ↦ rfl) hzero hzero, indexForm_zero_right, zero_add]

/-! ### Nonnegativity of `I(V^⊥, V^⊥)` at local minima of length -/

/-- **Nonnegativity of `I(V^⊥, V^⊥)` at a local minimum of length.** Let `F` be `C³` along
`{0} × [a, b]` (`a ≤ b`), whose central curve `γ = F 0` is a geodesic on `(a, b)` of constant speed
`C > 0` on `[a, b]` with endpoint transverse-acceleration pairings satisfying
`⟪A(b), γ'(b)⟫ ≤ ⟪A(a), γ'(a)⟫`. If `s ↦ pathELength I (F s) a b` has a local minimum at `s = 0`,
then `0 ≤ I(V^⊥, V^⊥)`. -/
theorem indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hbdry : ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
        curveVelocity I (F 0) b⟫_ℝ ≤
      ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
        curveVelocity I (F 0) a⟫_ℝ)
    (hmin : IsLocalMin (fun s ↦ Manifold.pathELength I (F s) a b) 0) :
    0 ≤ indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hfin := eventually_pathELength_ne_top (I := I) (a := a) (b := b) (F := F) fun t ht ↦
    (hF t (by rwa [uIcc_of_le hab] at ht)).of_le (by norm_num)
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin (hasDerivAt_toReal_pathELength hab
    (fun t ht ↦ (hF t ht).of_le (by norm_num)) hC hspeed).continuousAt
    (hmin.mp (hfin.mono fun s hfs hs ↦ ENNReal.toReal_mono hfs hs))
  rw [(hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hγ hC hspeed).deriv,
    div_nonneg_iff] at hnn
  linarith [hnn.resolve_right (not_and_of_not_right _ hC.not_ge) |>.1]

/-- **Nonnegativity of `I(V^⊥, V^⊥)` at a local minimum of length for fixed endpoints.** If `F` is
a `C³` fixed-endpoint variation on `[a, b]` (`a ≤ b`) of a geodesic `γ = F 0` on `(a, b)` of
constant speed `C > 0` on `[a, b]` and `s ↦ pathELength I (F s) a b` has a local minimum at
`s = 0`, then `0 ≤ I(V^⊥, V^⊥)`. -/
theorem IsFixedEndpointVariation.indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength
    {a b : ℝ} (hab : a ≤ b) (hF : IsFixedEndpointVariation I 3 F a b)
    (hγ : IsGeodesicCurveOn I (F 0) (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hmin : IsLocalMin (fun s ↦ Manifold.pathELength I (F s) a b) 0) :
    0 ≤ indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b :=
  TauCeti.Manifold.indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength hab
    (fun t ht ↦ hF.contMDiffAt t (by rwa [uIcc_of_le hab])) hγ hC hspeed
    (by simp [hF.acceleration_left_eq_zero, hF.acceleration_right_eq_zero]) hmin

/-- **Nonnegativity of `I(V^⊥, V^⊥)` at a local minimum of length for closed geodesics.** If `F` is
`C³` along `{0} × [a, b]` (`a ≤ b`) with `F s a = F s b` near `0`, `γ = F 0` is a geodesic on
`(a, b)` of constant speed `C > 0` on `[a, b]` with matching endpoint velocity lifts, and
`s ↦ pathELength I (F s) a b` has a local minimum at `s = 0`, then `0 ≤ I(V^⊥, V^⊥)`. -/
theorem indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength_of_curveVelocityLift_eq
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : curveVelocityLift I (F 0) a = curveVelocityLift I (F 0) b)
    (hmin : IsLocalMin (fun s ↦ Manifold.pathELength I (F s) a b) 0) :
    0 ≤ indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b :=
  indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength hab hF hγ hC hspeed
    (inner_acceleration_fst_curveVelocity_eq_of_curveVelocityLift_eq hper hvel).symm.le hmin

/-! ### Exponential variations and length shortening -/

section ExponentialLength

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

namespace IsGeodesicCurveOn

/-- **Second variation of length along an exponential variation of a constant-speed geodesic.** For
a geodesic `γ` on `(a, b)` of constant speed `C > 0` on `(a, b)` (`a ≤ b`) and any field `V` along
`γ` whose lift to the tangent bundle is `C³` on `[a, b]` (even with moving endpoints),
`d²/ds² L(exp_(γ ·) (s • V ·)) |₀ = I(V^⊥, V^⊥) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_exponentialVariation
    {a b : ℝ} (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hab : a ≤ b)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (Icc a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      (indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b / C) 0 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simpa only [Manifold.pathELength_self, ENNReal.toReal_zero, deriv_const', indexForm_same,
      zero_div] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  obtain ⟨γ', V', hV', hEq, hExp⟩ :=
    exists_contMDiffAt_exponentialVariation_eqOn γ V (by rwa [uIcc_of_le hab])
  have hγEq : EqOn γ' γ (Icc a b) := fun r hr ↦
    congrArg TotalSpace.proj (hEq r (by rwa [uIcc_of_le hab]))
  have hspeed' := norm_curveVelocity_eq_Icc_of_totalSpaceMk_eq (by norm_num) hlt hV' hEq hspeed
  have hd' : HasDerivAt
      (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ' V' s) a b).toReal)
      (indexForm I γ'
        (fun t ↦ V' t - (ℝ ∙ curveVelocity I γ' t).starProjection (V' t))
        (fun t ↦ V' t - (ℝ ∙ curveVelocity I γ' t).starProjection (V' t)) a b / C) 0 := by
    have h := hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab
      (fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t (by rwa [uIcc_of_le hab])))
      (by rw [exponentialVariation_zero]; exact hγ.congr fun r hr ↦ hγEq (Ioo_subset_Icc_self hr))
      hC (fun t ht ↦ by rw [exponentialVariation_zero]; exact hspeed' t ht)
    simp only [acceleration_exponentialVariation_zero, inner_zero_left, add_zero, sub_zero] at h
    rwa [variationField_exponentialVariation_eq, exponentialVariation_zero] at h
  have hVperp (t : ℝ) (ht : t ∈ uIoo a b) :
      TotalSpace.mk' E (γ' t) (V' t - (ℝ ∙ curveVelocity I γ' t).starProjection (V' t)) =
        TotalSpace.mk' E (γ t) (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) := by
    have hti : t ∈ Ioo a b := by rwa [uIoo_of_le hab] at ht
    have hnear : γ' =ᶠ[𝓝 t] γ := eventuallyEq_of_mem (Icc_mem_nhds hti.1 hti.2) hγEq
    have hvel : TotalSpace.mk' E (γ' t) (curveVelocity I γ' t) =
        TotalSpace.mk' E (γ t) (curveVelocity I γ t) :=
      Bundle.TotalSpace.ext hnear.self_of_nhds
        (heq_of_eq (Filter.EventuallyEq.curveVelocity_eq hnear))
    exact TauCeti.totalSpaceMk_sub_starProjection_singleton_eq
      (hEq t (uIoo_subset_uIcc_self ht)) hvel
  rw [congrArg (fun f s ↦ (f s).toReal) (pathELength_exponentialVariation_eq_of_eqOn hExp)]
  exact hd'.congr_deriv (congrArg (· / C) (indexForm_congr_of_totalSpaceMk_eq hVperp hVperp))

/-- **Second variation of length along an exponential variation of a unit-speed geodesic.** For a
geodesic `γ` on `(a, b)` of unit speed on `(a, b)` (`a ≤ b`) and any field `V` along `γ` whose lift
to the tangent bundle is `C³` on `[a, b]` (with free or fixed endpoints),
`d²/ds² L(exp_(γ ·) (s • V ·)) |₀ = I(V^⊥, V^⊥)` where `V^⊥ = V - ⟪V, γ'⟫ γ'`. -/
theorem hasDerivAt_deriv_toReal_pathELength_exponentialVariation_of_norm_curveVelocity_eq_one
    {a b : ℝ} (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hab : a ≤ b)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (Icc a b))
    (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = 1) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      (indexForm I γ
        (fun t ↦ V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t)
        (fun t ↦ V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t) a b) 0 := by
  refine (hγ.hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV
    zero_lt_one hspeed).congr_deriv ?_
  rw [indexForm_sub_starProjection_eq_of_norm_curveVelocity_eq_one (by rwa [uIoo_of_le hab]) V,
    div_one]

/-- **Second variation of length along a normal exponential variation.** For a geodesic `γ` on
`(a, b)` of constant speed `C > 0` on `(a, b)` (`a ≤ b`) and a field `V` along `γ` with a `C³` lift
on `[a, b]` which is orthogonal to `γ'` on `(a, b)`, the normal component of `V` agrees with `V`
on `(a, b)`, which suffices for equality of the index forms, so
`d²/ds² L(exp_(γ ·) (s • V ·)) |₀ = I(V, V) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_exponentialVariation_of_orthogonal
    {a b : ℝ} (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hab : a ≤ b)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (Icc a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = C)
    (horth : ∀ t ∈ Ioo a b, ⟪V t, curveVelocity I γ t⟫_ℝ = 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      (indexForm I γ V V a b / C) 0 := by
  refine (hγ.hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hC hspeed).congr_deriv
    ?_
  congr 1; refine indexForm_congr (fun _ _ ↦ rfl) (fun t ht ↦ ?_) (fun t ht ↦ ?_) <;>
  · rw [uIoo_of_le hab] at ht
    simp [Submodule.starProjection_singleton, real_inner_comm, horth t ht]

end IsGeodesicCurveOn

/-- **Nonnegativity of `I(V^⊥, V^⊥)` at a local minimum of length along an exponential variation.**
Let `γ` be a geodesic on `(a, b)` of constant speed `C > 0` on `(a, b)` (`a ≤ b`), and `V` a field
along `γ` with a `C³` lift on `[a, b]`. If `s ↦ pathELength I (exponentialVariation I γ V s) a b`
has a local minimum at `s = 0`, then `0 ≤ I(V^⊥, V^⊥)`. -/
theorem indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength_exponentialVariation
    {a b : ℝ} (hab : a ≤ b)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (Icc a b))
    (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = C)
    (hmin : IsLocalMin (fun s ↦ Manifold.pathELength I (exponentialVariation I γ V s) a b) 0) :
    0 ≤ indexForm I γ
      (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
      (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b := by
  have hfin := eventually_pathELength_exponentialVariation_ne_top
    (by rw [uIcc_of_le hab]; exact hV.of_le (by norm_num))
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin
    (hasDerivAt_toReal_pathELength_exponentialVariation hab (hV.of_le (by norm_num)) hC
      hspeed).continuousAt (hmin.mp (hfin.mono fun s hfs hs ↦ ENNReal.toReal_mono hfs hs))
  rw [(hγ.hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hC hspeed).deriv] at hnn
  exact (div_nonneg_iff.mp hnn).resolve_right (not_and_of_not_right _ hC.not_ge) |>.1

/-- **Negative normal index form strictly decreases `pathELength`.** Let `γ` be a geodesic on
`(a, b)` of constant speed `C > 0` on `(a, b)` (`a ≤ b`), and `V` a field along `γ` with a `C³`
lift on `[a, b]` whose endpoint pairings satisfy `⟪V(b), γ'_[a,b](b)⟫ = ⟪V(a), γ'_[a,b](a)⟫`. If
`I(V^⊥, V^⊥) < 0`, then for every sufficiently small `s ≠ 0` the curve `exp_(γ ·) (s • V ·)` has
strictly smaller `pathELength` (in `ℝ≥0∞`) than `γ`. -/
theorem eventually_pathELength_exponentialVariation_lt_of_indexForm_sub_starProjection_neg
    {a b : ℝ} (hab : a ≤ b)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (Icc a b))
    (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = C)
    (hbdry : ⟪V b, curveVelocityWithin I γ (Icc a b) b⟫_ℝ =
      ⟪V a, curveVelocityWithin I γ (Icc a b) a⟫_ℝ)
    (hneg : indexForm I γ
      (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
      (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b < 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      Manifold.pathELength I (exponentialVariation I γ V s) a b <
        Manifold.pathELength I γ a b := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hd₁ :=
    hasDerivAt_toReal_pathELength_exponentialVariation hab (hV.of_le (by norm_num)) hC hspeed
  have hd₁_zero :
      deriv (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal) 0 = 0 := by
    rw [hd₁.deriv, hγ.integral_inner_acceleration_eq_zero (by rw [uIoo_of_le hab]),
      hbdry, sub_self, sub_zero, zero_div]
  have hltR : ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal <
        (Manifold.pathELength I γ a b).toReal := by
    have hneg' : deriv (deriv fun s ↦
        (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal) 0 < 0 := by
      rw [(hγ.hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hC hspeed).deriv]
      exact div_neg_of_neg_of_pos hneg hC
    simpa only [exponentialVariation_zero] using TauCeti.eventually_gt_of_deriv_deriv_neg
      hneg' hd₁_zero hd₁.continuousAt
  have hfin := eventually_pathELength_exponentialVariation_ne_top
    (by rw [uIcc_of_le hab]; exact hV.of_le (by norm_num))
  filter_upwards [hltR, nhdsWithin_le_nhds hfin] with s hs hfs
  exact (ENNReal.toReal_lt_toReal hfs (by simpa only [exponentialVariation_zero] using
    hfin.self_of_nhds)).mp hs

end ExponentialLength

end TauCeti.Manifold

end
