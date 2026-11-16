/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Tangential
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic

/-!
# The second variation of length

Let `F : ℝ → ℝ → M` be a `C³` variation of the curve `γ = F 0` between `a` and `b` in a smooth
Riemannian manifold, with variation field `V = TauCeti.Manifold.variationField I F` and transverse
acceleration `A(t) = D_s ∂_s F (0, t)`.

At a regular parameter `t` (`γ'(t) ≠ 0`), differentiating `s ↦ ‖∂_t F (s, t)‖ = √(‖∂_t F (s, t)‖²)`
twice at `s = 0` gives

`d²/ds² ‖∂_t F (s, t)‖ |₀ =
  (I_γ(V, V)(t) + ⟪D_t A(t), γ'(t)⟫) / ‖γ'(t)‖ - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖³`,

where `I_γ(V, V)(t)` is `TauCeti.Manifold.indexFormIntegrand`. Compared with half the second
derivative of the squared speed, the extra term `-⟪D_t V, γ'⟫² / ‖γ'‖³` removes the tangential
component of `D_t V`.

Along a geodesic `γ` of constant speed `C > 0`, the tangential/normal splitting in
`TauCeti.Geometry.Manifold.Riemannian.IndexForm.Tangential` expresses the normal projection
`V⊥(t) = V(t) - proj_{ℝ ∙ γ'(t)} V(t)` via

`I(V⊥, V⊥) = I(V, V) - (∫_a^b ⟪D_t V(t), γ'(t)⟫² dt) / C²`.

Integrating the pointwise second derivative of speed over `[a, b]` and integrating `⟪D_t A, γ'⟫`
by parts yields **the second variation formula for length** along a constant-speed geodesic, with
free endpoints:

`d²/ds² L(F s) |₀ = (I(V⊥, V⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`.

For a unit-speed geodesic (`C = 1`), `V⊥(t) = V(t) - ⟪V(t), γ'(t)⟫ • γ'(t)` and the factor `1 / C`
disappears. In particular, tangential variations (`V(t) ∈ ℝ ∙ γ'(t)`, corresponding to
first-order reparametrizations of `γ`) contribute `0` to `I(V⊥, V⊥)`, leaving only the endpoint
acceleration pairing — and `0` when the endpoints are fixed.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_norm_curveVelocity` and
  `TauCeti.Manifold.deriv_deriv_norm_curveVelocity`: the pointwise second transverse derivative
  of the speed at a regular parameter.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength` and
  `TauCeti.Manifold.deriv_deriv_toReal_pathELength`: the second variation of length of a
  constant-speed curve, before assuming the geodesic equation.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn`: **the second
  variation of length** along a constant-speed geodesic with free endpoints (together with its
  unit-speed specialization and `deriv_deriv_*` counterparts).
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_inner_eq_zero` and
  `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity`: specializations
  to normal variations and tangential (reparametrization) variations.
* Fixed-endpoint second variation of length
`TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn`
  and local-minimum nonnegativity of the normal-projected index form.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_periodic`: periodic variations of a
  closed constant-speed geodesic, and local-minimum nonnegativity of the normal-projected index
  form.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_exponentialVariation` and
  `TauCeti.Manifold.deriv_deriv_toReal_pathELength_exponentialVariation`: the second variation of
  length of `exp_(γ t) (s • V t)` along a constant-speed geodesic.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (the second variation formula for length and the index form).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2 (the corresponding formula
  for energy).
-/

public noncomputable section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold

/-! ### Pointwise second derivative of the speed -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-- **The second transverse derivative of the speed.** At a parameter `t` where `F` is `C³` and
`γ = F 0` has nonzero velocity, the second derivative at `s = 0` of `s ↦ ‖∂_t F (s, t)‖` is
`(I_γ(V, V)(t) + ⟪D_t A(t), γ'(t)⟫) / ‖γ'(t)‖ - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖³`. -/
theorem hasDerivAt_deriv_norm_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ ‖curveVelocity I (F s) t‖)
      ((indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
          ⟪alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
            curveVelocity I (F 0) t⟫_ℝ) / ‖curveVelocity I (F 0) t‖ -
        ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
          curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 3) 0 := by
  have hd := TauCeti.hasDerivAt_deriv_sqrt (g := fun q ↦ ‖curveVelocity I (F q) t‖ ^ 2) (t := 0)
    (pow_pos (norm_pos_iff.2 hγ) 2)
    (hasDerivAt_norm_sq_curveVelocity (hf.of_le (by norm_num)))
    (hasDerivAt_deriv_norm_sq_curveVelocity hf)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hd
  refine hd.congr_deriv ?_
  field_simp
  ring

/-- Evaluating `hasDerivAt_deriv_norm_curveVelocity` as an iterated `deriv`. -/
theorem deriv_deriv_norm_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : curveVelocity I (F 0) t ≠ 0) :
    deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖) 0 =
      (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
          ⟪alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
            curveVelocity I (F 0) t⟫_ℝ) / ‖curveVelocity I (F 0) t‖ -
        ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
          curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 3 :=
  (hasDerivAt_deriv_norm_curveVelocity hf hγ).deriv

/-! ### Differentiating the length integral twice -/

/-- **The second variation of length of a regular curve.** If `F` is `C³` along `{0} × [a, b]` and
`γ = F 0` has nonzero velocity on `[a, b]`, then `s ↦ d/ds L(F s)` is differentiable at `s = 0`,
with derivative equal to the integral of `hasDerivAt_deriv_norm_curveVelocity`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (∫ t in a..b,
        ((indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
            ⟪alongCurve (leviCivitaConnection I M) (F 0)
              (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
              curveVelocity I (F 0) t⟫_ℝ) / ‖curveVelocity I (F 0) t‖ -
          ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
            curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 3)) 0 := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  rw [← uIcc_of_le hab] at hF hγ
  set W₀ := {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) z}
  have hW₀o : IsOpen W₀ := TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  set G : ℝ × ℝ → ℝ := fun z ↦ ‖curveVelocity I (F z.1) z.2‖ ^ 2
  have hG : ContDiffOn ℝ 2 G W₀ :=
    ContMDiffOn.contDiffOn_norm_sq_curveVelocity (fun _ hz ↦ hz.contMDiffWithinAt) (by norm_num)
      hW₀o
  set W := W₀ ∩ G ⁻¹' Ioi 0
  have hWo : IsOpen W := hG.continuousOn.isOpen_inter_preimage hW₀o isOpen_Ioi
  have h0W : {0} ×ˢ uIcc a b ⊆ W := by
    rintro ⟨_, t⟩ ⟨rfl, ht⟩
    exact ⟨hF t ht, pow_pos (norm_pos_iff.2 (hγ t ht)) 2⟩
  obtain ⟨U, V, hUo, hVo, h0U, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hWo h0W
  have hL : ContDiffOn ℝ 2 (fun z : ℝ × ℝ ↦ ‖curveVelocity I (F z.1) z.2‖) W :=
    ((hG.mono inter_subset_left).sqrt fun _ hz ↦ ne_of_gt hz.2).congr fun _ _ ↦
      (Real.sqrt_sq (norm_nonneg _)).symm
  have hlength : (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) =ᶠ[𝓝 0]
      fun s ↦ ∫ t in a..b, ‖curveVelocity I (F s) t‖ := by
    filter_upwards [hUo.mem_nhds (h0U (mem_singleton 0))] with s hs
    have hγs : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (F s) V := fun t ht ↦
      (((hUV ⟨hs, ht⟩).1.of_le (by norm_num)).comp t
        (contDiff_prodMk_right s).contMDiff.contMDiffAt).contMDiffWithinAt
    rw [hγs.pathELength_eq_ofReal_integral_norm_curveVelocityWithin (uIcc_of_le hab ▸ hV),
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _)]
    exact intervalIntegral.integral_congr fun t ht ↦
      congrArg norm (curveVelocityWithin_of_mem_nhds (hVo.mem_nhds (hV ht)))
  obtain ⟨_, hd⟩ := TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn hWo hL h0W
  exact (hd.congr_of_eventuallyEq hlength.deriv).congr_deriv
    (intervalIntegral.integral_congr fun t ht ↦ deriv_deriv_norm_curveVelocity (hF t ht) (hγ t ht))

/-! ### The second variation of length for constant-speed curves and geodesics -/

/-- **The second variation of length of a constant-speed curve.** Let `F` be `C³` along
`{0} × [a, b]` and suppose `γ = F 0` has constant speed `C > 0` on `[a, b]`. Then `s ↦ d/ds L(F s)`
is differentiable at `s = 0`, with derivative equal to `1 / C` times the difference between the
second energy variation and `(∫_a^b ⟪D_t V(t), γ'(t)⟫² dt) / C²`. -/
theorem hasDerivAt_deriv_toReal_pathELength {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0) (variationField I F) (variationField I F) a b -
          (∫ t in a..b, ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
            curveVelocity I (F 0) t⟫_ℝ ^ 2) / C ^ 2 +
          ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
            curveVelocity I (F 0) b⟫_ℝ -
          ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
            curveVelocity I (F 0) a⟫_ℝ -
          ∫ t in a..b, ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0,
            acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) / C) 0 := by
  have hFu : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    by rwa [uIcc_of_le hab]
  have hγu : ∀ t ∈ uIcc a b, ‖curveVelocity I (F 0) t‖ = C := by rwa [uIcc_of_le hab]
  have hVl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) := fun t ht ↦
    ((hFu t ht).contMDiffAt_variationField (m := 1) (by norm_num)).contMDiffWithinAt
  have hE := (hasDerivAt_deriv_energy_eq_integral hFu).unique (hasDerivAt_deriv_energy hFu)
  have hIAdd := intervalIntegrable_indexFormIntegrand_add_inner_alongCurve_acceleration_fst hFu
  have hDsq : IntervalIntegrable
      (fun t ↦ ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ ^ 2) volume a b := by
    simpa only [sq] using intervalIntegrable_inner_alongCurve_mul hVl hVl
  refine (hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero hab hF fun t ht ↦
    norm_ne_zero_iff.1 (by rw [hγ t ht]; exact hC.ne')).congr_deriv ?_
  rw [intervalIntegral.integral_congr fun t ht ↦ by rw [hγu t ht],
    intervalIntegral.integral_sub (hIAdd.div_const C) (hDsq.div_const (C ^ 3)),
    intervalIntegral.integral_div, intervalIntegral.integral_div, hE]
  have hC' : C ≠ 0 := hC.ne'
  field_simp
  ring

/-- **The second variation of length of a constant-speed curve**, written as an iterated
`deriv`. -/
theorem deriv_deriv_toReal_pathELength {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      (indexForm I (F 0) (variationField I F) (variationField I F) a b -
          (∫ t in a..b, ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
            curveVelocity I (F 0) t⟫_ℝ ^ 2) / C ^ 2 +
          ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
            curveVelocity I (F 0) b⟫_ℝ -
          ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
            curveVelocity I (F 0) a⟫_ℝ -
          ∫ t in a..b, ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0,
            acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) / C :=
  (hasDerivAt_deriv_toReal_pathELength hab hF hC hγ).deriv

/-- **The second variation of length along a constant-speed geodesic.** For a `C³` variation `F`
with possibly moving endpoints of a geodesic `γ = F 0` on `Ioo a b` having constant speed `C > 0`
on `[a, b]`, the second derivative of the length at `s = 0` is
`(I(V⊥, V⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
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
  have hgeou : IsGeodesicCurveOn I (F 0) (uIoo a b) := by rwa [uIoo_of_le hab]
  have hFu : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    by rwa [uIcc_of_le hab]
  have hγu : ∀ t ∈ uIoo a b, ‖curveVelocity I (F 0) t‖ = C := fun t ht ↦
    hγ t (uIcc_of_le hab ▸ uIoo_subset_uIcc_self ht)
  have hVl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) := fun t ht ↦
    ((hFu t ht).contMDiffAt_variationField (m := 1) (by norm_num)).contMDiffWithinAt
  refine (hasDerivAt_deriv_toReal_pathELength hab hF hC hγ).congr_deriv ?_
  rw [← hgeou.indexForm_sub_starProjection_singleton_self hγu hVl,
    hgeou.integral_inner_acceleration_eq_zero, sub_zero]

/-- **The second variation of length along a constant-speed geodesic**, written as an iterated
`deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      (indexForm I (F 0)
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
          (fun t ↦ variationField I F t -
            (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C :=
  (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ hgeo).deriv

/-- **The second variation of length along a unit-speed geodesic.** For a `C³` variation `F` with
possibly moving endpoints of a unit-speed geodesic `γ = F 0` on `[a, b]`,
`d²/ds² L(F s) |₀ = I(V⊥, V⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`, where
`V⊥(t) = V(t) - ⟪V(t), γ'(t)⟫ • γ'(t)`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_norm_curveVelocity_eq_one
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
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
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF zero_lt_one hγ
    hgeo).congr_deriv ?_
  have hproj : ∀ t ∈ uIoo a b, HEq
      (variationField I F t - (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (variationField I F t -
        ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t) := by
    intro t ht
    apply heq_of_eq
    rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq,
      hγ t (uIcc_of_le hab ▸ uIoo_subset_uIcc_self ht), one_pow, div_one, real_inner_comm]
  rw [div_one, indexForm_congr (fun _ _ ↦ rfl) hproj hproj]

/-- **The second variation of length along a unit-speed geodesic**, written as an iterated
`deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_norm_curveVelocity_eq_one
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      indexForm I (F 0)
          (fun t ↦ variationField I F t -
            ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t)
          (fun t ↦ variationField I F t -
            ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ • curveVelocity I (F 0) t) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ :=
  (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn_of_norm_curveVelocity_eq_one
    hab hF hγ hgeo).deriv

/-! ### Normal variations, tangential degeneracy, fixed endpoints, and periodic geodesics -/

/-- **Second variation of length for a normal variation.** When the variation field is orthogonal
to `γ'` on `Ioo a b`, its normal projection is `V` itself and the second variation of length is
`(I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_inner_eq_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (horth : ∀ t ∈ Ioo a b, ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ = 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((indexForm I (F 0) (variationField I F) (variationField I F) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ
    hgeo).congr_deriv ?_
  have hproj : ∀ t ∈ uIoo a b, HEq
      (variationField I F t - (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (variationField I F t) := by
    intro t ht
    apply heq_of_eq
    rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq, real_inner_comm,
      horth t (uIoo_of_le hab ▸ ht), zero_div, zero_smul, sub_zero]
  rw [indexForm_congr (fun _ _ ↦ rfl) hproj hproj]

/-- **Second variation of length for a normal variation**, written as an iterated `deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_inner_eq_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (horth : ∀ t ∈ Ioo a b, ⟪variationField I F t, curveVelocity I (F 0) t⟫_ℝ = 0) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      (indexForm I (F 0) (variationField I F) (variationField I F) a b +
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C :=
  (hasDerivAt_deriv_toReal_pathELength_of_inner_eq_zero hab hF hC hγ hgeo horth).deriv

/-- **Reparametrization degeneracy of the second variation of length.** For a tangential variation
(`V(t) ∈ ℝ ∙ γ'(t)` on `Ioo a b`), the index-form contribution vanishes and only the endpoint
acceleration pairings remain. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (htan : ∀ t ∈ Ioo a b, variationField I F t ∈ ℝ ∙ curveVelocity I (F 0) t) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ
    hgeo).congr_deriv ?_
  rw [indexForm_sub_starProjection_singleton_left_eq_zero_of_mem_span (by rwa [uIoo_of_le hab]),
    zero_add]

/-- **Reparametrization degeneracy of the second variation of length**, written as an iterated
`deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_mem_span_curveVelocity {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (htan : ∀ t ∈ Ioo a b, variationField I F t ∈ ℝ ∙ curveVelocity I (F 0) t) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      (⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0,
          curveVelocity I (F 0) b⟫_ℝ -
        ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0,
          curveVelocity I (F 0) a⟫_ℝ) / C :=
  (hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity hab hF hC hγ hgeo htan).deriv

/-- Shared second-derivative test step deducing `0 ≤ I(V⊥, V⊥)` from
`d²/ds² L(F s) |₀ = I(V⊥, V⊥) / C` and a local minimum of length at `s = 0`. -/
private theorem indexForm_sub_starProjection_singleton_nonneg_of_deriv_deriv_eq
    {a b C : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hd : deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C)
    (hmin : IsLocalMin (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0) :
    0 ≤ indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hdiv := TauCeti.deriv_deriv_nonneg_of_isLocalMin
    (hasDerivAt_toReal_pathELength hab hF hC hγ).continuousAt hmin
  rw [hd, div_nonneg_iff] at hdiv
  exact (hdiv.resolve_right fun h ↦ not_le_of_gt hC h.2).1

namespace IsFixedEndpointVariation

/-- **The second variation of length for a fixed-endpoint variation of a constant-speed geodesic**
is `I(V⊥, V⊥) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C) 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  refine (TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab
    (fun t ht ↦ hF.contMDiffAt t (uIcc_of_le hab ▸ ht)) hC hγ hgeo).congr_deriv ?_
  rw [hF.acceleration_left_eq_zero, hF.acceleration_right_eq_zero, inner_zero_left,
    inner_zero_left, add_zero, sub_zero]

/-- **The second variation of length for a fixed-endpoint variation of a constant-speed geodesic**,
written as an iterated `deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_isGeodesicCurveOn {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C :=
  (hF.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hC hγ hgeo).deriv

/-- For a fixed-endpoint tangential variation of a constant-speed geodesic, the second derivative
of the length at `s = 0` vanishes. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (htan : ∀ t ∈ Ioo a b, variationField I F t ∈ ℝ ∙ curveVelocity I (F 0) t) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 0 := by
  refine (hF.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hC hγ
    hgeo).congr_deriv ?_
  rw [indexForm_sub_starProjection_singleton_left_eq_zero_of_mem_span (by rwa [uIoo_of_le hab]),
    zero_div]

/-- Iterated-`deriv` form of
`IsFixedEndpointVariation.hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity`. -/
theorem deriv_deriv_toReal_pathELength_of_mem_span_curveVelocity {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (htan : ∀ t ∈ Ioo a b, variationField I F t ∈ ℝ ∙ curveVelocity I (F 0) t) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 = 0 :=
  (hF.hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity hab hC hγ hgeo htan).deriv

/-- **Necessary second-order condition at a local minimum of length.** Along a constant-speed
geodesic that locally minimizes length for a `C³` fixed-endpoint variation `F`, the index form of
the normal component `V⊥` is nonnegative. -/
theorem indexForm_sub_starProjection_singleton_nonneg_of_isLocalMin_toReal_pathELength
    {a b : ℝ} (hab : a ≤ b)
    (hF : IsFixedEndpointVariation I 3 F a b)
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hmin : IsLocalMin (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0) :
    0 ≤ indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b :=
  indexForm_sub_starProjection_singleton_nonneg_of_deriv_deriv_eq hab
    (fun t ht ↦ (hF.of_le (by norm_num)).contMDiffAt t (uIcc_of_le hab ▸ ht)) hC hγ
    (hF.deriv_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hC hγ hgeo) hmin

end IsFixedEndpointVariation

/-- **The second variation of length for a periodic variation of a closed geodesic.** When `F s a =
F s b` near `s = 0` and `(F 0 a, γ'(a)) = (F 0 b, γ'(b))`, the endpoint acceleration pairings
cancel and `d²/ds² L(F s) |₀ = I(V⊥, V⊥) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_periodic {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b)) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C) 0 := by
  have hacc := Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M) hper
  have hinner := TauCeti.inner_eq_of_totalSpaceMk_eq (𝕜 := ℝ) hacc hvel
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ
    hgeo).congr_deriv ?_
  rw [hinner, add_sub_cancel_right]

/-- **The second variation of length for a periodic variation of a closed geodesic**, written as
an iterated `deriv`. -/
theorem deriv_deriv_toReal_pathELength_of_periodic {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0 =
      indexForm I (F 0)
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
        (fun t ↦ variationField I F t -
          (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b / C :=
  (hasDerivAt_deriv_toReal_pathELength_of_periodic hab hF hC hγ hgeo hper hvel).deriv

/-- **Nonnegativity of the normal index form at a periodic local minimum of length.** If `F 0` is a
geodesic on `Ioo a b` of constant speed `C > 0` on `[a, b]` with matching endpoint tangent vectors
and `F` is a `C³` periodic variation locally minimizing length at `s = 0`, then the normal-projected
index form `I(V⊥, V⊥)` is nonnegative. -/
theorem indexForm_sub_starProjection_singleton_nonneg_of_isLocalMin_toReal_pathELength_of_periodic
    {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C)
    (hgeo : IsGeodesicCurveOn I (F 0) (Ioo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b))
    (hmin : IsLocalMin (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) 0) :
    0 ≤ indexForm I (F 0)
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t))
      (fun t ↦ variationField I F t -
        (ℝ ∙ curveVelocity I (F 0) t).starProjection (variationField I F t)) a b :=
  indexForm_sub_starProjection_singleton_nonneg_of_deriv_deriv_eq hab
    (fun t ht ↦ (hF t ht).of_le (by norm_num)) hC hγ
    (deriv_deriv_toReal_pathELength_of_periodic hab hF hC hγ hgeo hper hvel) hmin

/-- **The second variation of length of an exponential variation along a constant-speed geodesic.**
Along `exp_(γ t) (s • V t)`, every transverse curve is a geodesic, so all transverse accelerations
vanish and the second derivative of the length at `s = 0` is `I(V⊥, V⊥) / C`, even with moving
endpoints. -/
theorem hasDerivAt_deriv_toReal_pathELength_exponentialVariation [I.Boundaryless]
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b C : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I γ t‖ = C)
    (hgeo : IsGeodesicCurveOn I γ (Ioo a b)) :
    HasDerivAt
      (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      (indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b / C) 0 := by
  have hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht)
  have hγ₀ : ∀ t ∈ Icc a b, ‖curveVelocity I (exponentialVariation I γ V 0) t‖ = C := by
    rwa [exponentialVariation_zero]
  have hgeo₀ : IsGeodesicCurveOn I (exponentialVariation I γ V 0) (Ioo a b) := by
    rwa [exponentialVariation_zero]
  have hd := hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hC hγ₀ hgeo₀
  simp only [acceleration_exponentialVariation_zero, inner_zero_left, add_zero, sub_zero] at hd
  have hcongr : ∀ (γ₀ : ℝ → M) (W : ∀ t, TangentSpace I (γ₀ t)),
      γ₀ = γ → (∀ t, HEq (W t) (V t)) →
      indexForm I γ₀
        (fun t ↦ W t - (ℝ ∙ curveVelocity I γ₀ t).starProjection (W t))
        (fun t ↦ W t - (ℝ ∙ curveVelocity I γ₀ t).starProjection (W t)) a b =
      indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b := by
    rintro _ W rfl hW
    have hWV : W = V := funext fun t ↦ eq_of_heq (hW t)
    subst hWV
    rfl
  exact hd.congr_deriv (congrArg (· / C) (hcongr _ _ (exponentialVariation_zero γ V)
    fun t ↦ heq_of_eq (variationField_exponentialVariation γ V t)))

/-- **The second variation of length of an exponential variation along a constant-speed geodesic**,
written as an iterated `deriv`. -/
theorem deriv_deriv_toReal_pathELength_exponentialVariation [I.Boundaryless]
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b C : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I γ t‖ = C)
    (hgeo : IsGeodesicCurveOn I γ (Ioo a b)) :
    deriv (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal) 0 =
      indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b / C :=
  (hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hC hγ hgeo).deriv

end TauCeti.Manifold
