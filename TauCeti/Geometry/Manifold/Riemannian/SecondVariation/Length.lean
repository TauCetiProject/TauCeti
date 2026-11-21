/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric

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
index-form integrand of `V^⊥` is that of `V` minus `⟪D_t V, γ'⟫² / ‖γ'‖²`. For a unit-speed
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
* `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton` and
  `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton`: along a
  geodesic, the index-form integrand of the normal part of a field.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one`: **the second
  variation of length** of a unit-speed geodesic with free endpoints, and its constant-speed
  version `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_acceleration_eq_zero`.
* `IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one`:
  with fixed endpoints, the second variation of length of a unit-speed geodesic is the index form
  of the normal part of the variation field, and it vanishes for tangential variation fields
  (`TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_mem_span`).

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
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  rw [← uIcc_of_le hab] at hF hγ
  obtain ⟨U, V, hUo, hVo, h0U, hV, hfUV⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  -- the squared speed `G (s, t) = ‖∂_t F (s, t)‖ ^ 2`, jointly `C²` on `U ×ˢ V`
  let G : ℝ × ℝ → ℝ := fun z ↦
    ⟪mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z ↦ F z.1 z.2) z (0, 1),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z ↦ F z.1 z.2) z (0, 1)⟫_ℝ
  have hG : ContDiffOn ℝ 2 G (U ×ˢ V) :=
    hfUV.contDiffOn_inner_mfderiv (by norm_num) hUVo (0, 1) (0, 1)
  have hGeq {s t : ℝ} (hs : s ∈ U) (ht : t ∈ V) : G (s, t) = ‖curveVelocity I (F s) t‖ ^ 2 := by
    dsimp only [G]
    rw [← curveVelocity_eq_mfderiv_snd
      ((hfUV.contMDiffAt (hUVo.mem_nhds ⟨hs, ht⟩)).mdifferentiableAt (by norm_num)),
      real_inner_self_eq_norm_sq]
  -- the speed `L = √G` is `C²` on the open set `W` where `G` is positive, which contains
  -- `{0} × [a, b]` because `γ` is regular there
  let W := (U ×ˢ V) ∩ G ⁻¹' Ioi 0
  have hWo : IsOpen W := hG.continuousOn.isOpen_inter_preimage hUVo isOpen_Ioi
  let L : ℝ × ℝ → ℝ := fun z ↦ Real.sqrt (G z)
  have hL : ContDiffOn ℝ 2 L W :=
    (hG.mono inter_subset_left).sqrt fun _ hz ↦ ne_of_gt hz.2
  have hsub : {0} ×ˢ uIcc a b ⊆ W := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    refine ⟨⟨h0U, hV ht⟩, ?_⟩
    rw [mem_preimage, mem_Ioi, hGeq h0U (hV ht)]
    exact pow_pos (norm_pos_iff.2 (hγ t ht)) 2
  have hLeq {s t : ℝ} (hs : s ∈ U) (ht : t ∈ V) : L (s, t) = ‖curveVelocity I (F s) t‖ := by
    dsimp only [L]
    rw [hGeq hs ht, Real.sqrt_sq (norm_nonneg _)]
  have hmain := (TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn hWo hL hsub).2
  -- on `[a, b]`, the second partial derivatives of `L` in `s` are those of the speed
  have hpt : EqOn (fun t ↦ deriv (deriv fun s ↦ L (s, t)) 0)
      (fun t ↦ deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖) 0) (uIcc a b) := fun t ht ↦ by
    have h : (fun s ↦ L (s, t)) =ᶠ[𝓝 0] fun s ↦ ‖curveVelocity I (F s) t‖ :=
      eventually_of_mem (hUo.mem_nhds h0U) fun _ hs ↦ hLeq hs (hV ht)
    exact h.deriv.deriv_eq
  -- near `0`, the length is the integral of `L`
  have hlength : (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) =ᶠ[𝓝 0]
      fun s ↦ ∫ t in a..b, L (s, t) := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    have hγs : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (F s) V :=
      (hfUV.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)).comp
        (contDiff_prodMk_right s).contMDiff.contMDiffOn (fun t ht ↦ ⟨hs, ht⟩)
    have hVs : Icc a b ⊆ V := by simpa only [uIcc_of_le hab] using hV
    rw [hγs.pathELength_eq_ofReal_integral_norm_curveVelocityWithin hVs,
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab (fun _ _ ↦ norm_nonneg _))]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [curveVelocityWithin_of_mem_nhds (hVo.mem_nhds (hV ht)), hLeq hs (hV ht)]
  rw [← intervalIntegral.integral_congr hpt]
  exact hmain.congr_of_eventuallyEq hlength.deriv

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

/-! ### The normal part of a field along a geodesic -/

section NormalPart

variable {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}

/-- The curvature pairing `⟪R(w, v) v, w⟫` does not change when a multiple of `v` is subtracted
from `w`, by the antisymmetry of `R` in its first two arguments and its skew-adjointness. -/
private theorem inner_curvatureTensor_sub_smul {x : M} (w v : TangentSpace I x) (c : ℝ) :
    ⟪(leviCivitaConnection I M).curvatureTensor x (w - c • v) v v, w - c • v⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x w v v, w⟫_ℝ := by
  set R := (leviCivitaConnection I M).curvatureTensor x w v v
  have hskew : ⟪R, v⟫_ℝ = -⟪v, R⟫_ℝ :=
    (isMetricCompatible_leviCivitaConnection (I := I) (M := M)).inner_curvatureTensor_eq_neg
      x w v v v
  have h0 : ⟪R, v⟫_ℝ = 0 := by linarith [real_inner_comm v R]
  simp only [map_sub, map_smul, curvatureTensor_self, smul_zero, sub_zero,
    LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right, inner_smul_right]
  rw [h0, mul_zero, sub_zero]

/-- **The index form sees only the normal part, up to its tangential derivative.** Along a
geodesic on a preconnected parameter set, let `V^⊥ = V - proj_{γ'} V` be the normal part of a
field `V` whose coordinates are differentiable at `t`. Then the index-form integrand of `V^⊥`
against itself is that of `V` minus `‖proj_{γ'} D_t V‖²`, computed with derivatives within the
parameter set. -/
theorem IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton
    (h : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s) (ht : t ∈ s)
    (hV : DifferentiableWithinAt ℝ (sectionCoord ℝ (F := E) γ V (γ t)) s t) :
    indexFormIntegrandWithin I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r))
        (fun r ↦ V r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r)) s t =
      indexFormIntegrandWithin I γ V V s t -
        ‖(ℝ ∙ curveVelocityWithin I γ s t).starProjection
          (alongCurveWithin (leviCivitaConnection I M) γ V s t)‖ ^ 2 := by
  rw [indexFormIntegrandWithin_def, indexFormIntegrandWithin_def,
    h.alongCurveWithin_sub_starProjection_singleton hs ht hV]
  set v := curveVelocityWithin I γ s t
  set D := alongCurveWithin (leviCivitaConnection I M) γ V s t
  -- the projection of `V t` is a multiple of `v`, invisible to the curvature term
  have hproj : (ℝ ∙ v).starProjection (V t) = (⟪v, V t⟫_ℝ / ‖v‖ ^ 2) • v := by
    rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq]
  rw [hproj, inner_curvatureTensor_sub_smul (V t) v]
  -- `D - proj D` is orthogonal to `proj D`
  have horth := Submodule.starProjection_inner_eq_zero (K := ℝ ∙ v) D
    ((ℝ ∙ v).starProjection D) (Submodule.starProjection_apply_mem _ D)
  rw [← real_inner_self_eq_norm_sq ((ℝ ∙ v).starProjection D)]
  rw [inner_sub_left] at horth
  simp only [inner_sub_left, inner_sub_right] at horth ⊢
  rw [real_inner_comm D ((ℝ ∙ v).starProjection D)]
  linarith

/-- The unrestricted form of
`TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton`: along
a geodesic on a preconnected neighbourhood of `t`, the index-form integrand of the normal part
`V - proj_{γ'} V` of a field `V` with differentiable coordinates at `t` is that of `V` minus
`‖proj_{γ'} D_t V‖²`. -/
theorem IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton
    (h : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s) (hst : s ∈ 𝓝 t)
    (hV : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ V (γ t)) t) :
    indexFormIntegrand I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r)) t =
      indexFormIntegrand I γ V V t -
        ‖(ℝ ∙ curveVelocity I γ t).starProjection
          (alongCurve (leviCivitaConnection I M) γ V t)‖ ^ 2 := by
  -- near `t`, derivatives within `s` are unrestricted derivatives
  have hfield : ∀ᶠ r in 𝓝 t,
      HEq (V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
        (V r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r)) := by
    filter_upwards [eventually_mem_nhds_iff.2 hst] with r hr
    rw [curveVelocityWithin_of_mem_nhds hr]
  rw [indexFormIntegrand_congr (δ := γ) EventuallyEq.rfl hfield hfield,
    ← indexFormIntegrandWithin_of_mem_nhds hst, ← indexFormIntegrandWithin_of_mem_nhds hst,
    h.indexFormIntegrandWithin_sub_starProjection_singleton hs (mem_of_mem_nhds hst)
      (hV.differentiableWithinAt), curveVelocityWithin_of_mem_nhds hst,
    alongCurveWithin_of_mem_nhds _ γ V hst]

end NormalPart

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
    rw [uIoo_of_le hab] at ht
    rw [hacc t ht, inner_zero_right]
  -- on `(a, b)` the central curve is a geodesic
  have hgeod : IsGeodesicCurveOn I (F 0) (Ioo a b) := by
    refine ⟨isOpen_Ioo.uniqueDiffOn, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · exact ((hF t (Ioo_subset_Icc_self ht)).comp t (contMDiff_iff_contDiff.mpr
        (contDiff_prodMk_right (n := 3) (0 : ℝ))).contMDiffAt).contMDiffWithinAt.of_le
          (by norm_num)
    · rw [accelerationWithin_of_mem_nhds _ _ (isOpen_Ioo.mem_nhds ht), hacc t ht]
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
      (isOpen_Ioo.mem_nhds ht) hdiff, Submodule.starProjection_singleton,
      RCLike.ofReal_real_eq_id, id_eq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      hγ t (Ioo_subset_Icc_self ht), real_inner_comm]
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
  have hzero : indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b =
      indexForm I (F 0) (fun _ ↦ 0) (fun _ ↦ 0) a b :=
    indexForm_congr (fun _ _ ↦ rfl) (fun t ht ↦ by
        rw [uIoo_of_le hab] at ht
        rw [(Submodule.starProjection_eq_self_iff).2 (hV t ht), sub_self])
      (fun t ht ↦ by
        rw [uIoo_of_le hab] at ht
        rw [(Submodule.starProjection_eq_self_iff).2 (hV t ht), sub_self])
  rw [hzero, indexForm_def]
  simp [indexFormIntegrand_def]

end TauCeti.Manifold

end
