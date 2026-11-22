/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Tangential
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FirstVariation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# The second variation of length

Let `F : ℝ → ℝ → M` be a two-parameter family of curves in a smooth Riemannian manifold, with
central curve `γ = F 0`, variation field `V(t) = ∂_s F (0, t)`, and transverse acceleration
`A(t) = D_s ∂_s F (0, t)` at `s = 0`. At a parameter `t` where `F` is `C³` and `γ'(t) ≠ 0`,
differentiating `s ↦ ‖∂_t F (s, t)‖` twice at `s = 0` yields

`d²/ds² ‖∂_t F (s, t)‖ |₀ =
  (I_t(V, V) - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖² + ⟪D_t A(t), γ'(t)⟫) / ‖γ'(t)‖`.

When `γ` has constant speed `C > 0` on `[a, b]` (`a ≤ b`), differentiating under the integral sign
twice via `TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn` and integrating `⟪D_t A, γ'⟫`
by parts via `TauCeti.Manifold.integral_inner_alongCurve_acceleration_fst_curveVelocity` gives the
second variation of length. When `γ` is moreover a geodesic on `(a, b)`,
`TauCeti.Manifold.IsGeodesicCurveOn.indexForm_sub_starProjection_singleton` turns
`I(V, V) - ∫_a^b ⟪D_t V, γ'⟫² / ‖γ'‖² dt` into the index form `I(V^⊥, V^⊥)` of the normal
component `V^⊥(t) = V(t) - (ℝ ∙ γ'(t)).starProjection (V(t))`. In particular:

* for a constant-speed `C > 0` geodesic `γ` on `(a, b)`,
  `d²/ds² L(F s) |₀ = (I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`;
* for a unit-speed geodesic `γ`, `V^⊥ = V - ⟪V, γ'⟫ γ'` and
  `d²/ds² L(F s) |₀ = I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`;
* the boundary terms cancel for fixed-endpoint variations, periodic variations of smoothly closed
  geodesics, and exponential variations of closed-interval `C³` fields;
* tangential variations (which correspond to reparametrizations of `γ`) have `I(V^⊥, V^⊥) = 0`.

Applying the second-derivative tests gives `I(V^⊥, V^⊥) ≥ 0` at a local minimum of `pathELength`
(for any `C³` family with `⟪A(b), γ'(b)⟫ ≤ ⟪A(a), γ'(a)⟫`, as well as fixed-endpoint, periodic,
and exponential variations) and strict `pathELength` decrease (in `ℝ≥0∞`) along the exponential
variation when `I(V^⊥, V^⊥) < 0` and the first-variation endpoint pairings cancel.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_norm_curveVelocity`: pointwise second transverse derivative of
  the speed at a regular parameter.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero`: second variation
  of length of a regular `C³` family.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength`: second variation of length of a
  constant-speed curve, with boundary and longitudinal-acceleration terms.
* `hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn`,
  `hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_norm_curveVelocity_eq_one`,
  `IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn`,
  `hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_curveVelocityLift_eq`, and
  `hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_mem_span_curveVelocity` (in
  `TauCeti.Manifold`): **the second variation of length** of constant-speed, unit-speed,
  fixed-endpoint, periodic, and tangential variations of a geodesic in terms of `I(V^⊥, V^⊥)`.
* `indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength`,
  `IsFixedEndpointVariation.indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength`, and
  `indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength_of_curveVelocityLift_eq` (in
  `TauCeti.Manifold`): local-minimum nonnegativity of `I(V^⊥, V^⊥)` for general, fixed-endpoint,
  and periodic `C³` families.
* `hasDerivAt_deriv_toReal_pathELength_exponentialVariation`,
  `hasDerivAt_deriv_toReal_pathELength_exponentialVariation_of_norm_curveVelocity_eq_one`, and
  `hasDerivAt_deriv_toReal_pathELength_exponentialVariation_of_orthogonal` (in
  `TauCeti.Manifold.IsGeodesicCurveOn`): closed-interval exponential-variation length formulas.
* `indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength_exponentialVariation` and
  `eventually_pathELength_exponentialVariation_lt_of_indexForm_sub_starProjection_neg` (in
  `TauCeti.Manifold`): local-minimum nonnegativity and strict `pathELength` shortening along
  exponential variations.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 10
  (the second variation of length and normal variations).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 9, §2 and Chapter 10, §2.
-/

public noncomputable section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-! ### Pointwise second transverse derivative of the speed -/

/-- **Second transverse derivative of the speed.** At a parameter `t` where `F` is `C³` at `(0, t)`
and the central curve `γ = F 0` has nonzero velocity, `s ↦ d/ds ‖∂_t F (s, t)‖` has derivative
`(I_t(V, V) - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖² + ⟪D_t A(t), γ'(t)⟫) / ‖γ'(t)‖` at `s = 0`. -/
theorem hasDerivAt_deriv_norm_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ ‖curveVelocity I (F s) t‖)
      ((indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t -
          ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
            curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 2 +
          ⟪alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
            curveVelocity I (F 0) t⟫_ℝ) /
        ‖curveVelocity I (F 0) t‖) 0 := by
  -- Express `d/ds ‖∂_t F (s, t)‖` near `s = 0` via the chain rule on `√(‖∂_t F (s, t)‖²)`.
  let σ : ℝ → M := fun s ↦ F s t
  let P : ∀ s, TangentSpace I (σ s) := fun s ↦ curveVelocity I (F s) t
  let q : ℝ → ℝ := fun s ↦ ‖P s‖ ^ 2
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hPnear : ∀ᶠ s in 𝓝 (0 : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (σ r) (P r)) s :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp
      (((hf.contMDiffAt_curveVelocity_snd (m := 2) (by norm_num)).comp 0
        (contDiff_prodMk_left t).contMDiff.contMDiffAt).of_le one_le_two)
  have hvel_cont : ContinuousAt (fun s ↦ ‖P s‖) 0 :=
    (hasDerivAt_norm_curveVelocity (hf.of_le (by norm_num)) hγ).continuousAt
  have hd₁ : (deriv fun s ↦ ‖P s‖) =ᶠ[𝓝 0] fun s ↦ deriv q s / (2 * ‖P s‖) := by
    filter_upwards [hPnear, hvel_cont.eventually_ne (norm_ne_zero_iff.mpr hγ)] with s hs hns
    have hq2 := hm.hasDerivAt_norm_sq_alongCurve
      (((contMDiff_proj (TangentSpace I)).contMDiffAt.comp s hs).mdifferentiableAt one_ne_zero)
      (differentiableAt_sectionCoord σ P (hs.mdifferentiableAt one_ne_zero)
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (σ s)))
    simpa only [q, Real.sqrt_sq (norm_nonneg _), ← hq2.deriv] using
      (hq2.sqrt (pow_ne_zero 2 hns)).deriv
  -- Differentiate the quotient `deriv q s / (2 * ‖P s‖)` at `s = 0`.
  have hq0 : deriv (fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0 =
      2 * ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ :=
    (hasDerivAt_norm_sq_curveVelocity (hf.of_le (by norm_num))).deriv
  have hden := (hasDerivAt_norm_curveVelocity (hf.of_le (by norm_num)) hγ).const_mul 2
  refine (((hasDerivAt_deriv_norm_sq_curveVelocity hf).div hden
    (mul_ne_zero two_ne_zero (norm_ne_zero_iff.mpr hγ))).congr_of_eventuallyEq hd₁).congr_deriv ?_
  rw [hq0]
  field_simp
  ring

/-! ### Second variation of length of regular and constant-speed curves -/

/-- **Second variation of length of a regular curve.** Let `F` be `C³` at every point of
`{0} × [a, b]` with `a ≤ b`, and suppose `γ = F 0` has nonzero velocity on `[a, b]`. Then
`s ↦ d/ds L(F s)` is differentiable at `s = 0`, with derivative equal to the integral of the
second transverse speed derivative `hasDerivAt_deriv_norm_curveVelocity`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (∫ t in a..b,
        (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t -
            ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
              curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 2 +
            ⟪alongCurve (leviCivitaConnection I M) (F 0)
              (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
              curveVelocity I (F 0) t⟫_ℝ) /
          ‖curveVelocity I (F 0) t‖) 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  rw [← uIcc_of_le hab] at hF hγ
  obtain ⟨U₀, V₀, L, hU₀o, hV₀o, h0U₀, hV₀, hL, hLeq, hlen⟩ :=
    exists_contDiffOn_norm_curveVelocity (m := 2) (n := 3) (by norm_num) (by simp) hab hF hγ
  have hdL := (TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn (hU₀o.prod hV₀o) hL
    (prod_mono (singleton_subset_iff.mpr h0U₀) hV₀)).2
  refine (hdL.congr_of_eventuallyEq (EventuallyEq.deriv <|
    eventually_of_mem (hU₀o.mem_nhds h0U₀) hlen)).congr_deriv
    (intervalIntegral.integral_congr fun t ht ↦ ?_)
  have hnorm_eq : (fun s ↦ L (s, t)) =ᶠ[𝓝 0] fun s ↦ ‖curveVelocity I (F s) t‖ :=
    eventually_of_mem (hU₀o.mem_nhds h0U₀) fun s hs ↦ hLeq s hs t ht
  rw [hnorm_eq.deriv.deriv.self_of_nhds,
    (hasDerivAt_deriv_norm_curveVelocity (hF t ht) (hγ t ht)).deriv]

/-- **The second variation of length of a constant-speed curve.** Let `F` be `C³` along
`{0} × [a, b]` with `a ≤ b`, whose central curve `γ = F 0` has constant speed `C > 0` on `[a, b]`.
Then `s ↦ d/ds L(F s)` has derivative at `s = 0` equal to

`(I(V, V) - ∫_a^b ⟪D_t V, γ'⟫² / C² dt + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫
  - ∫_a^b ⟪A, D_t γ'⟫ dt) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0) (variationField I F) (variationField I F) a b -
          (∫ t in a..b,
            ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
              curveVelocity I (F 0) t⟫_ℝ ^ 2 / C ^ 2) +
          ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
            curveVelocity I (F 0) b⟫_ℝ -
          ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
            curveVelocity I (F 0) a⟫_ℝ -
          ∫ t in a..b,
            ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0,
              acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) / C) 0 := by
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  refine (hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero hab hF fun t ht ↦
    norm_ne_zero_iff.1 (by rw [hγ t ht]; exact hC.ne')).congr_deriv ?_
  rw [← uIcc_of_le hab] at hF hγ
  have hVF : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) :=
    fun r hr ↦ ((hF r hr).contMDiffAt_variationField (by norm_num)).contMDiffWithinAt
  have hintI : IntervalIntegrable
      (indexFormIntegrand I (F 0) (variationField I F) (variationField I F)) volume a b :=
    intervalIntegrable_indexFormIntegrand hVF hVF
  have hintT : IntervalIntegrable (fun t ↦
      ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ ^ 2 / C ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (((continuousAt_inner_alongCurve_variationField_curveVelocity
        ((hF t ht).of_le (by norm_num))).pow 2).div_const (C ^ 2)).continuousWithinAt
  have hintDA : IntervalIntegrable (fun t ↦
      ⟪alongCurve (leviCivitaConnection I M) (F 0)
        (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
        curveVelocity I (F 0) t⟫_ℝ) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_alongCurve_acceleration_fst_curveVelocity (hF t ht)).continuousWithinAt
  rw [intervalIntegral.integral_congr fun t ht ↦ by rw [hγ t ht],
    intervalIntegral.integral_div, intervalIntegral.integral_add (hintI.sub hintT) hintDA,
    intervalIntegral.integral_sub hintI hintT, ← indexForm_def,
    integral_inner_alongCurve_acceleration_fst_curveVelocity hF]
  ring

/-! ### Second variation of length of constant-speed and unit-speed geodesics -/

/-- **Second variation of length of a constant-speed geodesic.** Let `F` be `C³` along
`{0} × [a, b]` with `a ≤ b`, whose central curve `γ = F 0` is a geodesic on `(a, b)` of constant
speed `C > 0` on `[a, b]`. Then `s ↦ d/ds L(F s)` has derivative at `s = 0` equal to

`(I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`,

where `V^⊥(t) = V(t) - (ℝ ∙ γ'(t)).starProjection (V(t))` is the normal component of the variation
field `V` and `A(t) = D_s ∂_s F (0, t)` is the transverse acceleration. -/
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
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  refine (hasDerivAt_deriv_toReal_pathELength hab hF hC hspeed).congr_deriv ?_
  have hγu : IsGeodesicCurveOn I (F 0) (uIoo a b) := by rwa [uIoo_of_le hab]
  have hVF : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun r hr ↦ ((hF r hr).contMDiffAt_variationField (by norm_num)).contMDiffWithinAt
  rw [hγu.indexForm_sub_starProjection_singleton hVF hVF,
    hγu.integral_inner_acceleration_eq_zero Subset.rfl, sub_zero]
  congr 4
  exact intervalIntegral.integral_congr fun t ht ↦ by
    rw [uIcc_of_le hab] at ht; rw [← sq, hspeed t ht]

/-- **Second variation of length of a unit-speed geodesic.** Let `F` be `C³` along `{0} × [a, b]`
with `a ≤ b`, whose central curve `γ = F 0` is a geodesic on `(a, b)` of unit speed on `[a, b]`.
Then

`d²/ds² L(F s) |₀ = I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`,

where `V^⊥(t) = V(t) - ⟪V(t), γ'(t)⟫ γ'(t)` is the normal component of `V`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_norm_curveVelocity_eq_one
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
          (fun t ↦ variationField I F t -
            ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t)
          (fun t ↦ variationField I F t -
            ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hγ zero_lt_one
    hspeed).congr_deriv ?_
  have hproj (t : ℝ) (ht : t ∈ uIoo a b) :
      HEq (variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (variationField I F t -
          ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t) := by
    rw [uIoo_of_le hab] at ht
    rw [heq_eq_eq, Submodule.starProjection_unit_singleton ℝ (hspeed t (Ioo_subset_Icc_self ht)),
      real_inner_comm]
  rw [indexForm_congr (fun _ _ ↦ rfl) hproj hproj, div_one]

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
  rw [(Filter.EventuallyEq.acceleration_eq _ hF.eventually_apply_left).trans
      (acceleration_const _ _ 0),
    (Filter.EventuallyEq.acceleration_eq _ hF.eventually_apply_right).trans
      (acceleration_const _ _ 0),
    inner_zero_left, inner_zero_left, add_zero, sub_zero]

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
  rw [curveVelocityLift_apply, curveVelocityLift_apply] at hvel
  rw [TauCeti.inner_eq_of_totalSpaceMk_eq
    (Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M) hper) hvel]
  ring

/-- **Tangential degeneracy of the second variation of length.** Along a geodesic `γ = F 0` on
`(a, b)` of constant speed `C > 0` on `[a, b]` (`a ≤ b`), if the variation field `V` lies in the
tangent line `ℝ ∙ γ'(t)` for every `t ∈ (a, b)` (for instance when `F` reparametrizes `γ`), then
`I(V^⊥, V^⊥) = 0` and only the endpoint transverse-acceleration pairings
`(⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C` remain; in particular the second variation of length vanishes
for fixed-endpoint tangential variations. -/
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
  have hzero_field (t : ℝ) (ht : t ∈ uIoo a b) :
      HEq (variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        ((0 : ∀ r, TangentSpace I (F 0 r)) t) := by
    rw [uIoo_of_le hab] at ht
    simp [Submodule.starProjection_eq_self_iff.mpr (htan t ht)]
  rw [indexForm_congr (fun _ _ ↦ rfl) hzero_field hzero_field, indexForm_zero_right, zero_add]

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
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin
    (hasDerivAt_toReal_pathELength hab (fun t ht ↦ (hF t ht).of_le (by norm_num)) hC
      hspeed).continuousAt
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
    (by rw [(Filter.EventuallyEq.acceleration_eq _ hF.eventually_apply_left).trans
        (acceleration_const _ _ 0),
      (Filter.EventuallyEq.acceleration_eq _ hF.eventually_apply_right).trans
        (acceleration_const _ _ 0),
      inner_zero_left, inner_zero_left]) hmin

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
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b := by
  rw [curveVelocityLift_apply, curveVelocityLift_apply] at hvel
  exact indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength hab hF hγ hC hspeed
    (TauCeti.inner_eq_of_totalSpaceMk_eq
      (Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M) hper)
      hvel).symm.le
    hmin

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
  have hspeed' : ∀ t ∈ Icc a b, ‖curveVelocity I γ' t‖ = C := by
    have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    exact norm_curveVelocity_eq_Icc_of_Ioo hlt
      (fun t ht ↦ (contMDiff_proj (TangentSpace I)).contMDiffAt.comp t
        ((hV' t (by rwa [uIcc_of_le hab])).of_le (by norm_num)))
      fun t ht ↦ by
        rw [(eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2) hγEq).norm_curveVelocity_eq, hspeed t ht]
  have hd' : HasDerivAt
      (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ' V' s) a b).toReal)
      (indexForm I γ'
        (fun t ↦ V' t - (ℝ ∙ curveVelocity I γ' t).starProjection (V' t))
        (fun t ↦ V' t - (ℝ ∙ curveVelocity I γ' t).starProjection (V' t)) a b / C) 0 := by
    have hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3
        (fun z : ℝ × ℝ ↦ exponentialVariation I γ' V' z.1 z.2) (0, t) :=
      fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t (by rwa [uIcc_of_le hab]))
    have h0 := exponentialVariation_zero γ' V'
    have hVF : ∀ t, HEq (variationField I (exponentialVariation I γ' V') t) (V' t) :=
      fun t ↦ heq_of_eq (variationField_exponentialVariation γ' V' t)
    have hA := acceleration_exponentialVariation_zero γ' V'
    generalize exponentialVariation I γ' V' = G at hF h0 hVF hA ⊢
    subst h0
    simpa only [funext fun t ↦ eq_of_heq (hVF t), hA, inner_zero_left, add_zero, sub_zero] using
      hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF
        (hγ.congr fun r hr ↦ hγEq (Ioo_subset_Icc_self hr)) hC hspeed'
  have hVperp (t : ℝ) (ht : t ∈ uIoo a b) :
      HEq (V' t - (ℝ ∙ curveVelocity I γ' t).starProjection (V' t))
        (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) := by
    have hti : t ∈ Ioo a b := by rwa [uIoo_of_le hab] at ht
    have hnear : γ' =ᶠ[𝓝 t] γ := eventuallyEq_of_mem (Icc_mem_nhds hti.1 hti.2) hγEq
    have hcongr : ∀ {x₁ x₂ : M}, x₁ = x₂ →
        ∀ {v₁ : TangentSpace I x₁} {v₂ : TangentSpace I x₂}, HEq v₁ v₂ →
        ∀ {w₁ : TangentSpace I x₁} {w₂ : TangentSpace I x₂}, HEq w₁ w₂ →
        HEq (v₁ - (ℝ ∙ w₁).starProjection v₁) (v₂ - (ℝ ∙ w₂).starProjection v₂) := by
      rintro x₁ _ rfl v₁ v₂ hv w₁ w₂ hw; rw [eq_of_heq hv, eq_of_heq hw]
    exact hcongr hnear.self_of_nhds
      (Bundle.TotalSpace.ext_iff.mp (hEq t (uIoo_subset_uIcc_self ht))).2
      (heq_of_eq (Filter.EventuallyEq.curveVelocity_eq hnear))
  rw [funext fun s ↦ congrArg ENNReal.toReal
    (Manifold.pathELength_congr ((hExp s).mono (by rw [uIcc_of_le hab]))).symm]
  exact hd'.congr_deriv (congrArg (· / C) (indexForm_congr
    (fun t ht ↦ congrArg TotalSpace.proj (hEq t (uIoo_subset_uIcc_self ht))) hVperp hVperp))

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
  have hproj (t : ℝ) (ht : t ∈ uIoo a b) :
      HEq (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t) := by
    rw [uIoo_of_le hab] at ht
    rw [heq_eq_eq, Submodule.starProjection_unit_singleton ℝ (hspeed t ht), real_inner_comm]
  rw [indexForm_congr (fun _ _ ↦ rfl) hproj hproj, div_one]

/-- **Second variation of length along a normal exponential variation.** For a geodesic `γ` on
`(a, b)` of constant speed `C > 0` on `(a, b)` (`a ≤ b`) and a field `V` along `γ` with a `C³` lift
on `[a, b]` which is orthogonal to `γ'` on `(a, b)`, the normal projection of `V` is `V` itself, so
`d²/ds² L(exp_(γ ·) (s • V ·)) |₀ = I(V, V) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_exponentialVariation_of_orthogonal
    {a b : ℝ} (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hab : a ≤ b)
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (Icc a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity I γ t‖ = C)
    (horth : ∀ t ∈ Ioo a b, ⟪V t, curveVelocity I γ t⟫_ℝ = 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      (indexForm I γ V V a b / C) 0 := by
  refine (hγ.hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV
    hC hspeed).congr_deriv ?_
  congr 1
  refine indexForm_congr (fun _ _ ↦ rfl) (fun t ht ↦ ?_) (fun t ht ↦ ?_) <;>
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
      hspeed).continuousAt
    (hmin.mp (hfin.mono fun s hfs hs ↦ ENNReal.toReal_mono hfs hs))
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
  have hd₁ := hasDerivAt_toReal_pathELength_exponentialVariation hab (hV.of_le (by norm_num)) hC
    hspeed
  have hd₁_zero :
      deriv (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal) 0 = 0 := by
    rw [hd₁.deriv, hγ.integral_inner_acceleration_eq_zero (by rw [uIoo_of_le hab]),
      hbdry, sub_self, sub_zero, zero_div]
  have hd₂ := hγ.hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hC hspeed
  have hltR : ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal <
        (Manifold.pathELength I γ a b).toReal := by
    simpa only [exponentialVariation_zero] using TauCeti.eventually_gt_of_deriv_deriv_neg
      (hd₂.deriv.symm ▸ div_neg_of_neg_of_pos hneg hC) hd₁_zero hd₁.continuousAt
  have hfin := eventually_pathELength_exponentialVariation_ne_top
    (by rw [uIcc_of_le hab]; exact hV.of_le (by norm_num))
  have hfin0 : Manifold.pathELength I γ a b ≠ ⊤ := by
    simpa only [exponentialVariation_zero] using hfin.self_of_nhds
  filter_upwards [hltR, nhdsWithin_le_nhds hfin] with s hs hfs
  exact (ENNReal.toReal_lt_toReal hfs hfin0).mp hs

end ExponentialLength

end TauCeti.Manifold

end
