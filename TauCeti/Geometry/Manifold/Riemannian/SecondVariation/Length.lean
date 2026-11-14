/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
public import TauCeti.Geometry.Manifold.Riemannian.SecondVariation.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric

/-!
# The second variation of length and normal-field reduction

Let `F : ℝ → ℝ → M` be a two-parameter family of curves in a smooth Riemannian manifold, with
central curve `γ = F 0`, variation field `V(t) = ∂_s F (0, t)`, and transverse acceleration
`A(t) = D_s ∂_s F (0, t)` at `s = 0`. At a parameter `t` where `F` is `C³` and `γ'(t) ≠ 0`,
differentiating `s ↦ ‖∂_t F (s, t)‖` twice at `s = 0` yields

`d²/ds² ‖∂_t F (s, t)‖ |₀ =
  (I_t(V, V) - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖² + ⟪D_t A(t), γ'(t)⟫) / ‖γ'(t)‖`.

When `γ` has constant speed `C > 0` on `[a, b]`, differentiating under the integral sign twice and
integrating `⟪D_t A, γ'⟫` by parts gives the second variation of length. When `γ` is moreover a
geodesic on `(a, b)`, covariant differentiation commutes with orthogonal projection onto `ℝ ∙ γ'`
(`TauCeti.Manifold.IsGeodesicCurveOn.alongCurveWithin_sub_starProjection_singleton`), while
`R(P, γ') γ' = 0` and `⟪R(V, γ') γ', P⟫ = 0` for any tangential vector `P ∈ ℝ ∙ γ'`. Hence the
difference `I(V, V) - ∫_a^b ⟪D_t V, γ'⟫² / ‖γ'‖² dt` equals the index form `I(V^⊥, V^⊥)` of the
normal component `V^⊥(t) = V(t) - proj_{ℝ ∙ γ'(t)} V(t)`. In particular:

* for a constant-speed `C > 0` geodesic `γ`,
  `d²/ds² L(F s) |₀ = (I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C`;
* for a unit-speed geodesic `γ`, `V^⊥ = V - ⟪V, γ'⟫ γ'` and
  `d²/ds² L(F s) |₀ = I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`;
* tangential variations (which correspond to reparametrizations of `γ`) are `indexForm`-orthogonal
  to every normal field and have zero second variation of length whenever the endpoint transverse
  accelerations vanish.

Specializing to `TauCeti.Manifold.exponentialVariation` kills the boundary transverse accelerations
even when the endpoints move, and the second-derivative tests give `I(V^⊥, V^⊥) ≥ 0` at a local
minimum of length as well as strict length decrease (`pathELength` in `ℝ≥0∞`) when
`I(V^⊥, V^⊥) < 0` and the first-variation boundary pairings cancel.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_norm_curveVelocity`: pointwise second transverse derivative of
  the speed at a regular parameter.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_curveVelocity_ne_zero`: second variation
  of length of a regular `C³` family.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength`: second variation of length of a
  constant-speed curve, with boundary and longitudinal-acceleration terms.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton` and
  `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_sub_starProjection_singleton`: normal-projection
  formula `I(V^⊥, V^⊥) = I(V, V) - ∫ ⟪D_t V, γ'⟫² / ‖γ'‖²` along a geodesic.
* `TauCeti.Manifold.IsGeodesicCurveOn.indexForm_smul_curveVelocity_eq_zero_of_orthogonal`:
  tangential fields `f • γ'` are `indexForm`-orthogonal to normal fields along a geodesic.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn` and
  `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one`: **the second
  variation of length** of constant-speed and unit-speed geodesics in terms of `I(V^⊥, V^⊥)` and
  boundary transverse accelerations.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity`: tangential
  degeneracy of the second variation of length.
* `TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_exponentialVariation` and its unit-speed
  form `hasDerivAt_deriv_toReal_pathELength_exponentialVariation_of_norm_curveVelocity_eq_one`:
  free-endpoint exponential-variation formulas for length.
* `TauCeti.Manifold.indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength` and
  `TauCeti.Manifold.eventually_pathELength_exponentialVariation_lt_of_indexForm_neg`:
  local-minimum nonnegativity and strict `pathELength` shortening.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10, Theorem 10.4 and Proposition 10.6 (second variation of length and normal variations).
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
  let q : ℝ → ℝ := fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2
  have hvel_cont : ContinuousAt (fun s ↦ ‖curveVelocity I (F s) t‖) 0 :=
    (hasDerivAt_norm_curveVelocity (hf.of_le (by norm_num)) hγ).continuousAt
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) ∧
        ‖curveVelocity I (F s) t‖ ≠ 0 :=
    (((continuous_id.prodMk continuous_const).tendsto 0).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hf.of_le (by norm_num)))).and
      (hvel_cont.eventually_ne (norm_ne_zero_iff.mpr hγ))
  have hd₁ : (deriv fun s ↦ ‖curveVelocity I (F s) t‖) =ᶠ[𝓝 0]
      fun s ↦ deriv q s / (2 * ‖curveVelocity I (F s) t‖) := by
    filter_upwards [hnear] with s ⟨hs, hns⟩
    have hsq : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F (s + z.1) z.2) (0, t) :=
      hs.comp_of_eq
        (((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contMDiff.contMDiffAt) (by simp)
    have hqs : DifferentiableAt ℝ q s := by
      have h := (hasDerivAt_norm_sq_curveVelocity (F := fun r ↦ F (s + r)) hsq).comp_of_eq s
        ((hasDerivAt_id s).sub_const s) (sub_self s).symm
      exact h.differentiableAt.congr_of_eventuallyEq (Eventually.of_forall fun r ↦ by
        dsimp only [q, Function.comp_apply, id_eq]; rw [add_sub_cancel])
    have hsqrt := hqs.hasDerivAt.sqrt (pow_ne_zero 2 hns)
    dsimp only [q] at hsqrt
    simp only [Real.sqrt_sq (norm_nonneg _)] at hsqrt
    exact hsqrt.deriv
  have hnum : HasDerivAt (deriv q)
      (2 * (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        ⟪alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t,
          curveVelocity I (F 0) t⟫_ℝ)) 0 :=
    hasDerivAt_deriv_norm_sq_curveVelocity hf
  have hq0 : deriv q 0 =
      2 * ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ :=
    (hasDerivAt_norm_sq_curveVelocity (hf.of_le (by norm_num))).deriv
  have hden : HasDerivAt (fun s ↦ 2 * ‖curveVelocity I (F s) t‖)
      (2 * (⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ / ‖curveVelocity I (F 0) t‖)) 0 :=
    (hasDerivAt_norm_curveVelocity (hf.of_le (by norm_num)) hγ).const_mul 2
  have hn0 : ‖curveVelocity I (F 0) t‖ ≠ 0 := norm_ne_zero_iff.mpr hγ
  refine ((hnum.div hden (mul_ne_zero two_ne_zero hn0)).congr_of_eventuallyEq hd₁).congr_deriv
    ?_
  rw [hq0]
  field_simp
  ring

/-! ### Second variation of length of regular and constant-speed curves -/

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Around `{0} × uIcc a b` (`a ≤ b`), a regular `C³` family has a jointly `C²` speed
representative `L` on an open product neighbourhood `U₀ ×ˢ V₀` whose integral computes
`(pathELength I (F s) a b).toReal` for all `s ∈ U₀`. -/
private theorem exists_contDiffOn_norm_curveVelocity {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ uIcc a b, curveVelocity I (F 0) t ≠ 0) :
    ∃ (U₀ V₀ : Set ℝ) (L : ℝ × ℝ → ℝ),
      IsOpen U₀ ∧ IsOpen V₀ ∧ 0 ∈ U₀ ∧ uIcc a b ⊆ V₀ ∧
      ContDiffOn ℝ 2 L (U₀ ×ˢ V₀) ∧
      (∀ s ∈ U₀, ∀ t ∈ uIcc a b, L (s, t) = ‖curveVelocity I (F s) t‖) ∧
      ∀ s ∈ U₀, (Manifold.pathELength I (F s) a b).toReal = ∫ t in a..b, L (s, t) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  obtain ⟨U, V, hUo, hVo, h0U, hV, hfUV⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  let G : ℝ × ℝ → ℝ := fun z ↦
    ⟪mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z ↦ F z.1 z.2) z (0, 1),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z ↦ F z.1 z.2) z (0, 1)⟫_ℝ
  have hG : ContDiffOn ℝ 2 G (U ×ˢ V) :=
    hfUV.contDiffOn_inner_mfderiv (by norm_num) hUVo (0, 1) (0, 1)
  have hGeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V → G (s, t) = ‖curveVelocity I (F s) t‖ ^ 2 := by
    intro s t hs ht
    dsimp only [G]
    rw [← curveVelocity_eq_mfderiv_snd
      ((hfUV.contMDiffAt (hUVo.mem_nhds ⟨hs, ht⟩)).mdifferentiableAt (by norm_num)),
      real_inner_self_eq_norm_sq]
  let W := (U ×ˢ V) ∩ G ⁻¹' Ioi 0
  have hWo : IsOpen W := hG.continuousOn.isOpen_inter_preimage hUVo isOpen_Ioi
  let L : ℝ × ℝ → ℝ := fun z ↦ Real.sqrt (G z)
  have hL : ContDiffOn ℝ 2 L W := (hG.mono inter_subset_left).sqrt fun _ hz ↦ ne_of_gt hz.2
  have hsub : {0} ×ˢ uIcc a b ⊆ W := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    refine ⟨⟨h0U, hV ht⟩, ?_⟩
    rw [mem_preimage, mem_Ioi, hGeq h0U (hV ht)]
    exact pow_pos (norm_pos_iff.2 (hγ t ht)) 2
  have hLeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V → L (s, t) = ‖curveVelocity I (F s) t‖ := by
    intro s t hs ht
    dsimp only [L]
    rw [hGeq hs ht, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨U₀, V₀, hU₀o, hV₀o, h0U₀, hV₀, hU₀V₀⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hWo hsub
  refine ⟨U₀, V₀, L, hU₀o, hV₀o, h0U₀ rfl, hV₀, hL.mono hU₀V₀,
    fun s hs t ht ↦ hLeq (hU₀V₀ (mk_mem_prod hs (hV₀ ht))).1.1 (hV ht), fun q hq ↦ ?_⟩
  have hqU : q ∈ U := (hU₀V₀ (mk_mem_prod hq (hV₀ left_mem_uIcc))).1.1
  have hγq : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (F q) V :=
    (hfUV.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)).comp
      (contDiff_prodMk_right q).contMDiff.contMDiffOn fun t ht ↦ ⟨hqU, ht⟩
  have hVs : Icc a b ⊆ V := by simpa only [uIcc_of_le hab] using hV
  rw [hγq.pathELength_eq_ofReal_integral_norm_curveVelocityWithin hVs,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _)]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [curveVelocityWithin_of_mem_nhds (hVo.mem_nhds (hV ht)), hLeq hqU (hV ht)]

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
  rw [← uIcc_of_le hab] at hF hγ
  obtain ⟨U₀, V₀, L, hU₀o, hV₀o, h0U₀, hV₀, hL, hLeq, hlen⟩ :=
    exists_contDiffOn_norm_curveVelocity hab hF hγ
  have hUVo : IsOpen (U₀ ×ˢ V₀) := hU₀o.prod hV₀o
  let L₁ : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ L z (1, 0)
  have hL₁ : ContDiffOn ℝ 1 L₁ (U₀ ×ˢ V₀) :=
    (hL.fderiv_of_isOpen hUVo (by norm_num)).clm_apply contDiffOn_const
  have hdL : (deriv fun s ↦ (Manifold.pathELength I (F s) a b).toReal) =ᶠ[𝓝 0]
      fun s ↦ ∫ t in a..b, L₁ (s, t) := by
    filter_upwards [hU₀o.mem_nhds h0U₀] with s hs
    obtain ⟨_, hLs⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUVo (hL.of_le one_le_two)
      (prod_mono (singleton_subset_iff.mpr hs) hV₀)
    have hlen_near : (fun q ↦ (Manifold.pathELength I (F q) a b).toReal) =ᶠ[𝓝 s]
        fun q ↦ ∫ t in a..b, L (q, t) := by
      filter_upwards [hU₀o.mem_nhds hs] with q hq using hlen q hq
    exact (hLs.congr_of_eventuallyEq hlen_near).deriv
  obtain ⟨_, hDL₁⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUVo hL₁
    (prod_mono (singleton_subset_iff.mpr h0U₀) hV₀)
  refine (hDL₁.congr_of_eventuallyEq hdL).congr_deriv
    (intervalIntegral.integral_congr fun t ht ↦ ?_)
  have hfL₁ : HasFDerivAt L₁ (fderiv ℝ L₁ (0, t)) (0, t) :=
    ((hL₁.differentiableOn one_ne_zero (0, t) ⟨h0U₀, hV₀ ht⟩).differentiableAt
      (hUVo.mem_nhds ⟨h0U₀, hV₀ ht⟩)).hasFDerivAt
  have hdL₁t :=
    hfL₁.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id' (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) t))
  have hL₁eq : (deriv fun s ↦ ‖curveVelocity I (F s) t‖) =ᶠ[𝓝 0] fun s ↦ L₁ (s, t) := by
    filter_upwards [hU₀o.mem_nhds h0U₀] with s hs
    have hfs : HasFDerivAt L (fderiv ℝ L (s, t)) (s, t) :=
      ((hL.differentiableOn (by norm_num) (s, t) ⟨hs, hV₀ ht⟩).differentiableAt
        (hUVo.mem_nhds ⟨hs, hV₀ ht⟩)).hasFDerivAt
    have hdLs := hfs.comp_hasDerivAt s ((hasDerivAt_id' s).prodMk (hasDerivAt_const s t))
    have hnorm : (fun q ↦ ‖curveVelocity I (F q) t‖) =ᶠ[𝓝 s] fun q ↦ L (q, t) := by
      filter_upwards [hU₀o.mem_nhds hs] with q hq using (hLeq q hq t ht).symm
    exact (hdLs.congr_of_eventuallyEq hnorm).deriv
  exact (hdL₁t.congr_of_eventuallyEq hL₁eq).unique
    (hasDerivAt_deriv_norm_curveVelocity (hF t ht) (hγ t ht))

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
  have hintAA : IntervalIntegrable (fun t ↦
      ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0,
        acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_acceleration_fst_acceleration (hF t ht)).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_inner_acceleration_fst_curveVelocity (hF t ht)) (hintDA.add hintAA)
  rw [intervalIntegral.integral_add hintDA hintAA] at hFTC
  rw [intervalIntegral.integral_congr fun t ht ↦ by rw [hγ t ht],
    intervalIntegral.integral_div, intervalIntegral.integral_add (hintI.sub hintT) hintDA,
    intervalIntegral.integral_sub hintI hintT, ← indexForm_def, eq_sub_of_add_eq hFTC]
  ring

/-! ### Normal-field reduction and tangential degeneracy of the index form -/

/-- Squared norm of a vector minus its orthogonal projection onto a line `ℝ ∙ u`. The identity also
holds when `u = 0` via division by zero. -/
private theorem norm_sub_starProjection_singleton_sq {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (u w : X) :
    ‖w - (ℝ ∙ u).starProjection w‖ ^ 2 = ‖w‖ ^ 2 - ⟪w, u⟫_ℝ ^ 2 / ‖u‖ ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq, real_inner_comm u w,
    ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm u w, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- **Pointwise normal-projection identity for the index-form integrand.** Along a geodesic `γ` on
an open preconnected set `s`, at any parameter `t ∈ s` where `V` has differentiable coordinates,
the integrand `I_t(V^⊥, V^⊥)` of the normal component
`V^⊥(r) = V(r) - (ℝ ∙ γ'(r)).starProjection (V(r))` equals
`I_t(V, V) - ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖²`. -/
theorem IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}
    (hγ : IsGeodesicCurveOn I γ s) (hs : IsOpen s) (hconn : IsPreconnected s) (ht : t ∈ s)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t) :
    indexFormIntegrand I γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r))
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r)) t =
      indexFormIntegrand I γ V V t -
        ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ ^ 2 /
          ‖curveVelocity I γ t‖ ^ 2 := by
  set cov := leviCivitaConnection I M
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  -- Rewrite the normal projection locally to use `alongCurveWithin_sub_starProjection_singleton`.
  have hNnear : ∀ᶠ r in 𝓝 t,
      V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r) =
        V r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (V r) := by
    filter_upwards [hs.mem_nhds ht] with r hr
    rw [curveVelocityWithin_of_mem_nhds (hs.mem_nhds hr)]
  have hDN : alongCurve cov γ
        (fun r ↦ V r - (ℝ ∙ curveVelocity I γ r).starProjection (V r)) t =
      alongCurve cov γ V t -
        (ℝ ∙ curveVelocity I γ t).starProjection (alongCurve cov γ V t) := by
    rw [alongCurve_congr cov γ _ hNnear, ← alongCurveWithin_of_mem_nhds cov γ _ (hs.mem_nhds ht),
      hγ.alongCurveWithin_sub_starProjection_singleton hconn ht hV.differentiableWithinAt,
      alongCurveWithin_of_mem_nhds cov γ V (hs.mem_nhds ht),
      curveVelocityWithin_of_mem_nhds (hs.mem_nhds ht)]
  -- The curvature term is unchanged by subtracting a scalar multiple of `γ'(t)`.
  set c := ⟪curveVelocity I γ t, V t⟫_ℝ / ‖curveVelocity I γ t‖ ^ 2
  have hproj : (ℝ ∙ curveVelocity I γ t).starProjection (V t) = c • curveVelocity I γ t := by
    rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq]
  have hcurv : inner ℝ (cov.curvatureTensor (γ t)
        (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (curveVelocity I γ t) (curveVelocity I γ t))
        (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) =
      inner ℝ (cov.curvatureTensor (γ t) (V t) (curveVelocity I γ t) (curveVelocity I γ t))
        (V t) := by
    have hself : inner ℝ (cov.curvatureTensor (γ t) (V t) (curveVelocity I γ t)
        (curveVelocity I γ t)) (curveVelocity I γ t) = 0 := by
      have hskew := hm.inner_curvatureTensor_eq_neg (γ t) (V t) (curveVelocity I γ t)
        (curveVelocity I γ t) (curveVelocity I γ t)
      rw [real_inner_comm _ (curveVelocity I γ t)] at hskew
      linarith
    rw [hproj, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, curvatureTensor_self,
      smul_zero, sub_zero, inner_sub_right, real_inner_smul_right, hself, mul_zero, sub_zero]
  rw [indexFormIntegrand_def, indexFormIntegrand_def, hDN, hcurv, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, norm_sub_starProjection_singleton_sq]
  ring

/-- **Normal-projection formula for the index form along a geodesic.** Let `γ` be a geodesic on
`uIoo a b` and `V` a field along `γ` with a `C¹` lift on `uIcc a b`. Then the index form of the
normal component `V^⊥(t) = V(t) - (ℝ ∙ γ'(t)).starProjection (V(t))` satisfies

`I(V^⊥, V^⊥) = I(V, V) - ∫_a^b ⟪D_t V(t), γ'(t)⟫² / ‖γ'(t)‖² dt`. -/
theorem IsGeodesicCurveOn.indexForm_sub_starProjection_singleton
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (uIoo a b))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (uIcc a b)) :
    indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b =
      indexForm I γ V V a b -
        ∫ t in a..b,
          ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ ^ 2 /
            ‖curveVelocity I γ t‖ ^ 2 := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  -- Integrate the pointwise identity over `uIoo a b`; both right-hand pieces are integrable.
  have hintI : IntervalIntegrable (indexFormIntegrand I γ V V) volume a b :=
    intervalIntegrable_indexFormIntegrand hV hV
  have hintT : IntervalIntegrable (fun t ↦
      ⟪alongCurve (leviCivitaConnection I M) γ V t, curveVelocity I γ t⟫_ℝ ^ 2 /
        ‖curveVelocity I γ t‖ ^ 2) volume a b := by
    -- On `uIoo a b`, the geodesic speed `‖γ'(t)‖` equals a single constant `c`.
    obtain ⟨t₀, ht₀⟩ : (uIoo a b).Nonempty := nonempty_uIoo.mpr hab
    set c := ‖curveVelocityWithin I γ (uIoo a b) t₀‖
    have hγc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (uIcc a b) :=
      (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := 1)).comp_contMDiffOn hV
    have hvel : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
        (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ (uIcc a b) r)) (uIcc a b) := by
      simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ (uIcc a b))] using
        hγc.contMDiffOn_curveVelocityLiftWithin (m := 0) (by simp)
          (uniqueDiffOn_uIcc hab).uniqueMDiffOn
    have hDV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
        (fun r ↦ TotalSpace.mk' E (γ r)
          (alongCurveWithin (leviCivitaConnection I M) γ V (uIcc a b) r)) (uIcc a b) :=
      contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
        (by simp) (by simp) (uniqueDiffOn_uIcc hab) (by simpa using hV)
    have hnum_cont : ContinuousOn (fun r ↦
        ⟪alongCurveWithin (leviCivitaConnection I M) γ V (uIcc a b) r,
          curveVelocityWithin I γ (uIcc a b) r⟫_ℝ ^ 2 / c ^ 2) (uIcc a b) :=
      (((ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
        (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le) hDV hvel).continuousOn).pow 2)
        |>.div_const (c ^ 2)
    refine hnum_cont.intervalIntegrable.congr_uIoo fun t ht ↦ ?_
    have hmemIoo : uIoo a b ∈ 𝓝 t := (isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds ht
    have hmemIcc : uIcc a b ∈ 𝓝 t := mem_of_superset hmemIoo uIoo_subset_uIcc_self
    have hnorm : ‖curveVelocity I γ t‖ = c := by
      rw [← curveVelocityWithin_of_mem_nhds hmemIoo]
      exact hγ.norm_curveVelocityWithin_eq isPreconnected_Ioo ht ht₀
    dsimp only
    rw [alongCurveWithin_of_mem_nhds _ γ V hmemIcc, curveVelocityWithin_of_mem_nhds hmemIcc, hnorm]
  rw [indexForm_def, indexForm_def, ← intervalIntegral.integral_sub hintI hintT]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  have hVt : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t :=
    (hV t (uIoo_subset_uIcc_self ht)).contMDiffAt
      (mem_of_superset ((isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds ht) uIoo_subset_uIcc_self)
  exact hγ.indexFormIntegrand_sub_starProjection_singleton isOpen_Ioo isPreconnected_Ioo ht
    (differentiableAt_sectionCoord γ V (hVt.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))

/-- **Tangential fields are `indexForm`-orthogonal to normal fields along a geodesic.** If `γ` is a
geodesic on `uIoo a b`, `f : ℝ → ℝ` is differentiable on `uIoo a b`, and `W` is differentiable on
`uIoo a b` and orthogonal to `γ'` everywhere on `uIoo a b`, then
`I(f • γ', W) = 0`. -/
theorem IsGeodesicCurveOn.indexForm_smul_curveVelocity_eq_zero_of_orthogonal
    {γ : ℝ → M} {f : ℝ → ℝ} {W : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (uIoo a b))
    (hf : ∀ t ∈ uIoo a b, DifferentiableAt ℝ f t)
    (hW : ∀ t ∈ uIoo a b, DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t)
    (horth : ∀ t ∈ uIoo a b, ⟪W t, curveVelocity I γ t⟫_ℝ = 0) :
    indexForm I γ (fun t ↦ f t • curveVelocity I γ t) W a b = 0 := by
  rw [indexForm_def]
  refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
    intervalIntegral.integral_zero
  set cov := leviCivitaConnection I M
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hmem : uIoo a b ∈ 𝓝 t := (isOpen_Ioo : IsOpen (uIoo a b)).mem_nhds ht
  -- Differentiate `⟪W, γ'⟫ = 0` at `t` to obtain `⟪D_t W, γ'⟫ = 0`.
  have hvel_coord := differentiableWithinAt_sectionCoord_curveVelocityWithin γ hγ.uniqueDiffOn
    hγ.contMDiffOn ht (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hprod := hm.hasDerivWithinAt_inner_alongCurveWithin (hγ.mdifferentiableOn t ht)
    (hW t ht).differentiableWithinAt hvel_coord
  rw [← accelerationWithin_def, hγ.accelerationWithin_eq_zero t ht, inner_zero_right,
    add_zero] at hprod
  have hzero_deriv : HasDerivWithinAt
      (fun r ↦ inner ℝ (W r) (curveVelocityWithin I γ (uIoo a b) r)) 0 (uIoo a b) t :=
    (hasDerivWithinAt_const t (uIoo a b) (0 : ℝ)).congr_of_mem
      (fun r hr ↦ by
        have hrmem : uIoo a b ∈ 𝓝 r := isOpen_Ioo.mem_nhds hr
        rw [curveVelocityWithin_of_mem_nhds hrmem]
        exact horth r hr)
      ht
  have hDW0 : ⟪alongCurve cov γ W t, curveVelocity I γ t⟫_ℝ = 0 := by
    have h := (hγ.uniqueDiffOn t ht).eq_deriv _ hprod hzero_deriv
    rwa [alongCurveWithin_of_mem_nhds cov γ W hmem, curveVelocityWithin_of_mem_nhds hmem] at h
  -- Along the geodesic, `D_t (f • γ') = f'(t) • γ'(t)` and `R(f • γ', γ') = 0`.
  have hnear : ∀ᶠ r in 𝓝[uIoo a b] t,
      f r • curveVelocity I γ r = f r • curveVelocityWithin I γ (uIoo a b) r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrmem : uIoo a b ∈ 𝓝 r := isOpen_Ioo.mem_nhds hr
    rw [curveVelocityWithin_of_mem_nhds hrmem]
  have hDf : alongCurve cov γ (fun r ↦ f r • curveVelocity I γ r) t =
      deriv f t • curveVelocity I γ t := by
    rw [← alongCurveWithin_of_mem_nhds cov γ _ hmem,
      alongCurveWithin_congr cov γ _ hnear (by rw [curveVelocityWithin_of_mem_nhds hmem]),
      hγ.alongCurveWithin_smul_curveVelocityWithin ht (hf t ht).differentiableWithinAt,
      derivWithin_of_mem_nhds hmem, curveVelocityWithin_of_mem_nhds hmem]
  rw [indexFormIntegrand_def, hDf, map_smul, LinearMap.smul_apply, curvatureTensor_self, smul_zero,
    LinearMap.zero_apply, inner_zero_left, sub_zero, real_inner_smul_left,
    real_inner_comm _ (curveVelocity I γ t), hDW0, mul_zero]

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
  refine (hasDerivAt_deriv_toReal_pathELength hab hF hC hspeed).congr_deriv ?_
  have hγu : IsGeodesicCurveOn I (F 0) (uIoo a b) := by rwa [uIoo_of_le hab]
  have hVF : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun r hr ↦ ((hF r hr).contMDiffAt_variationField (by norm_num)).contMDiffWithinAt
  have hnorm_int : ∫ t in a..b,
      ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ ^ 2 / ‖curveVelocity I (F 0) t‖ ^ 2 =
      ∫ t in a..b,
        ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
          curveVelocity I (F 0) t⟫_ℝ ^ 2 / C ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hab] at ht
    rw [hspeed t ht]
  have hbulk : ∫ t in a..b,
      ⟪acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0,
        acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ = 0 := by
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    have hmem : uIoo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    rw [← accelerationWithin_of_mem_nhds _ (F 0) hmem,
      hγu.accelerationWithin_eq_zero t ht, inner_zero_right]
  rw [hγu.indexForm_sub_starProjection_singleton hVF, hnorm_int, hbulk, sub_zero]

/-- **Second variation of length of a unit-speed geodesic.** Let `F` be `C³` along `{0} × [a, b]`
with `a ≤ b`, whose central curve `γ = F 0` is a unit-speed geodesic on `(a, b)`. Then

`d²/ds² L(F s) |₀ = I(V^⊥, V^⊥) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`,

where `V^⊥(t) = V(t) - ⟪V(t), γ'(t)⟫ γ'(t)` is the normal component of `V`. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_norm_curveVelocity_eq_one {a b : ℝ} (hab : a ≤ b)
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
  have hd := hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hγ zero_lt_one hspeed
  refine hd.congr_deriv ?_
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
a `C³` fixed-endpoint variation of a geodesic of constant speed `C > 0`, the second derivative of
length at `s = 0` is `I(V^⊥, V^⊥) / C`. -/
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
  have hFIcc : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    fun t ht ↦ hF.contMDiffAt t (by rwa [uIcc_of_le hab])
  have ha : acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0 = 0 :=
    (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) hF.eventually_apply_left).trans
      (acceleration_const _ _ 0)
  have hb : acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0 = 0 :=
    (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) hF.eventually_apply_right).trans
      (acceleration_const _ _ 0)
  refine (TauCeti.Manifold.hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hFIcc hγ
    hC hspeed).congr_deriv ?_
  rw [ha, hb, inner_zero_left, inner_zero_left]
  ring

/-- **Tangential degeneracy of the second variation of length.** Along a constant-speed `C > 0`
geodesic `γ = F 0`, if the variation field `V` lies in the tangent line `ℝ ∙ γ'(t)` for every
`t ∈ (a, b)` (for instance when `F` reparametrizes `γ`), then `I(V^⊥, V^⊥) = 0` and only the
endpoint transverse-acceleration pairings `(⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫) / C` remain; in
particular the second variation of length vanishes for fixed-endpoint tangential variations. -/
theorem hasDerivAt_deriv_toReal_pathELength_of_mem_span_curveVelocity {a b : ℝ} (hab : a ≤ b)
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
    rw [heq_eq_eq, Submodule.starProjection_eq_self_iff.mpr (htan t ht), sub_self]
    rfl
  rw [indexForm_congr (fun _ _ ↦ rfl) hzero_field hzero_field, indexForm_zero_right, zero_add]

/-! ### Exponential variations and length-minimality consequences -/

section ExponentialLength

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- **First variation of length along an exponential variation.** Let `γ` have constant speed
`C > 0` on `[a, b]` (`a ≤ b`) and let `V` have a `C²` lift on `[a, b]`. Then
`d/ds L(exp_(γ ·) (s • V ·)) |₀ = (⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V, D_t γ'⟫ dt) / C`. -/
theorem hasDerivAt_toReal_pathELength_exponentialVariation {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I γ t‖ = C) :
    HasDerivAt (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      ((⟪V b, curveVelocity I γ b⟫_ℝ - ⟪V a, curveVelocity I γ a⟫_ℝ -
        ∫ t in a..b, ⟪V t, acceleration (leviCivitaConnection I M) γ t⟫_ℝ) / C) 0 := by
  have hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht)
  have hspeed0 : ∀ t ∈ Icc a b, ‖curveVelocity I (exponentialVariation I γ V 0) t‖ = C := by
    rwa [exponentialVariation_zero]
  have hd := hasDerivAt_toReal_pathELength hab hF hC hspeed0
  have heq_inner {x y : M} {u v : TangentSpace I x} {u' v' : TangentSpace I y}
      (hu : TotalSpace.mk' E x u = TotalSpace.mk' E y u')
      (hv : TotalSpace.mk' E x v = TotalSpace.mk' E y v') : ⟪u, v⟫_ℝ = ⟪u', v'⟫_ℝ := by
    cases hu
    cases hv
    rfl
  have hVlift (t : ℝ) :
      TotalSpace.mk' E (exponentialVariation I γ V 0 t)
        (variationField I (exponentialVariation I γ V) t) =
      TotalSpace.mk' E (γ t) (V t) :=
    TotalSpace.ext (congrFun (exponentialVariation_zero γ V) t)
      (heq_of_eq (variationField_exponentialVariation γ V t))
  have hvel (t : ℝ) :
      TotalSpace.mk' E (exponentialVariation I γ V 0 t)
        (curveVelocity I (exponentialVariation I γ V 0) t) =
      TotalSpace.mk' E (γ t) (curveVelocity I γ t) := by
    simpa only [curveVelocityLift_apply] using
      congrArg (fun c ↦ curveVelocityLift I c t) (exponentialVariation_zero γ V)
  have hacc (t : ℝ) :
      TotalSpace.mk' E (exponentialVariation I γ V 0 t)
        (acceleration (leviCivitaConnection I M) (exponentialVariation I γ V 0) t) =
      TotalSpace.mk' E (γ t) (acceleration (leviCivitaConnection I M) γ t) :=
    Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M)
      (Eventually.of_forall (congrFun (exponentialVariation_zero γ V)))
  refine hd.congr_deriv ?_
  rw [heq_inner (hVlift b) (hvel b), heq_inner (hVlift a) (hvel a),
    intervalIntegral.integral_congr fun t _ ↦ heq_inner (hVlift t) (hacc t)]

/-- **Second variation of length along an exponential variation of a constant-speed geodesic.** For
a geodesic `γ` on `(a, b)` of constant speed `C > 0` on `[a, b]` and any `C³` field `V` along `γ`
(even with moving endpoints), `d²/ds² L(exp_(γ ·) (s • V ·)) |₀ = I(V^⊥, V^⊥) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_exponentialVariation {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I γ t‖ = C) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      (indexForm I γ
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b / C) 0 := by
  have hF : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht)
  have hγ0 : IsGeodesicCurveOn I (exponentialVariation I γ V 0) (Ioo a b) := by
    rwa [exponentialVariation_zero]
  have hspeed0 : ∀ t ∈ Icc a b, ‖curveVelocity I (exponentialVariation I γ V 0) t‖ = C := by
    rwa [exponentialVariation_zero]
  refine (hasDerivAt_deriv_toReal_pathELength_of_isGeodesicCurveOn hab hF hγ0 hC
    hspeed0).congr_deriv ?_
  rw [acceleration_exponentialVariation_zero, acceleration_exponentialVariation_zero,
    inner_zero_left, inner_zero_left, add_zero, sub_zero]
  congr 1
  have hfield (t : ℝ) :
      HEq (variationField I (exponentialVariation I γ V) t -
          (ℝ ∙ curveVelocity I (exponentialVariation I γ V 0) t).starProjection
            (variationField I (exponentialVariation I γ V) t))
        (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) := by
    have hVlift : TotalSpace.mk' E (exponentialVariation I γ V 0 t)
        (variationField I (exponentialVariation I γ V) t) = TotalSpace.mk' E (γ t) (V t) :=
      TotalSpace.ext (congrFun (exponentialVariation_zero γ V) t)
        (heq_of_eq (variationField_exponentialVariation γ V t))
    have hvel : TotalSpace.mk' E (exponentialVariation I γ V 0 t)
        (curveVelocity I (exponentialVariation I γ V 0) t) =
        TotalSpace.mk' E (γ t) (curveVelocity I γ t) := by
      simpa only [curveVelocityLift_apply] using
        congrArg (fun c ↦ curveVelocityLift I c t) (exponentialVariation_zero γ V)
    have key {x y : M} {v w : TangentSpace I x} {v' w' : TangentSpace I y}
        (hv : TotalSpace.mk' E x v = TotalSpace.mk' E y v')
        (hw : TotalSpace.mk' E x w = TotalSpace.mk' E y w') :
        HEq (v - (ℝ ∙ w).starProjection v) (v' - (ℝ ∙ w').starProjection v') := by
      cases hv; cases hw; rfl
    exact key hVlift hvel
  exact indexForm_congr (fun t _ ↦ congrFun (exponentialVariation_zero γ V) t)
    (fun t _ ↦ hfield t) (fun t _ ↦ hfield t)

/-- **Second variation of length along an exponential variation of a unit-speed geodesic.** For a
unit-speed geodesic `γ` on `(a, b)` (`a ≤ b`) and any `C³` field `V` along `γ` (with free or fixed
endpoints), `d²/ds² L(exp_(γ ·) (s • V ·)) |₀ = I(V^⊥, V^⊥)` where `V^⊥ = V - ⟪V, γ'⟫ γ'`. -/
theorem hasDerivAt_deriv_toReal_pathELength_exponentialVariation_of_norm_curveVelocity_eq_one
    {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I γ t‖ = 1) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      (indexForm I γ
        (fun t ↦ V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t)
        (fun t ↦ V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t) a b) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hγ zero_lt_one
    hspeed).congr_deriv ?_
  have hproj (t : ℝ) (ht : t ∈ uIoo a b) :
      HEq (V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
        (V t - ⟪V t, curveVelocity I γ t⟫_ℝ • curveVelocity I γ t) := by
    rw [uIoo_of_le hab] at ht
    rw [heq_eq_eq, Submodule.starProjection_unit_singleton ℝ (hspeed t (Ioo_subset_Icc_self ht)),
      real_inner_comm]
  rw [indexForm_congr (fun _ _ ↦ rfl) hproj hproj, div_one]

/-- **Second variation of length along a normal exponential variation.** When `V` is orthogonal to
`γ'` on `(a, b)`, its normal projection is `V` itself, so
`d²/ds² L(exp_(γ ·) (s • V ·)) |₀ = I(V, V) / C`. -/
theorem hasDerivAt_deriv_toReal_pathELength_exponentialVariation_of_orthogonal
    {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I γ t‖ = C)
    (horth : ∀ t ∈ Ioo a b, ⟪V t, curveVelocity I γ t⟫_ℝ = 0) :
    HasDerivAt (deriv fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal)
      (indexForm I γ V V a b / C) 0 := by
  refine (hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hγ hC hspeed).congr_deriv
    ?_
  congr 1
  refine indexForm_congr (fun _ _ ↦ rfl) (fun t ht ↦ ?_) (fun t ht ↦ ?_) <;>
  · rw [uIoo_of_le hab] at ht
    rw [heq_eq_eq, Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq,
      real_inner_comm, horth t ht, zero_div, zero_smul, sub_zero]

/-- For a `C¹` field `V` along `γ` on `[a, b]` (`a ≤ b`), the curves `exp_(γ ·) (s • V ·)` have
finite `pathELength` for all `s` near `0`. -/
private theorem eventually_pathELength_exponentialVariation_ne_top {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t) :
    ∀ᶠ s in 𝓝 (0 : ℝ), Manifold.pathELength I (exponentialVariation I γ V s) a b ≠ ⊤ := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hFu : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 1
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (0, t) := by
    rw [uIcc_of_le hab]
    exact fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht)
  obtain ⟨U, W, hUo, _, h0U, hW, hfUW⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hFu
  filter_upwards [hUo.mem_nhds h0U] with s hs
  have hγs : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (exponentialVariation I γ V s) W :=
    hfUW.comp (contDiff_prodMk_right s).contMDiff.contMDiffOn fun t ht ↦ ⟨hs, ht⟩
  have hWs : Icc a b ⊆ W := by simpa only [uIcc_of_le hab] using hW
  rw [hγs.pathELength_eq_ofReal_integral_norm_curveVelocityWithin hWs]
  exact ENNReal.ofReal_ne_top

/-- **Nonnegativity of `I(V^⊥, V^⊥)` at a local minimum of length.** Let `γ` be a geodesic on
`(a, b)` of constant speed `C > 0` on `[a, b]` (`a ≤ b`), and `V` a `C³` field along `γ` on
`[a, b]`. If `s ↦ pathELength I (exponentialVariation I γ V s) a b` has a local minimum at `s = 0`
(for instance because `γ` minimizes length among curves with `V a = 0` and `V b = 0`, or among
closed curves), then `0 ≤ I(V^⊥, V^⊥)`. -/
theorem indexForm_sub_starProjection_nonneg_of_isLocalMin_pathELength {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I γ t‖ = C)
    (hmin : IsLocalMin (fun s ↦ Manifold.pathELength I (exponentialVariation I γ V s) a b) 0) :
    0 ≤ indexForm I γ
      (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
      (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b := by
  have hfin := eventually_pathELength_exponentialVariation_ne_top hab
    fun t ht ↦ (hV t ht).of_le (by norm_num)
  have hminR : IsLocalMin
      (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal) 0 := by
    filter_upwards [hmin, hfin] with s hs hfs
    exact ENNReal.toReal_mono hfs hs
  have hcont : ContinuousAt
      (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal) 0 :=
    (hasDerivAt_toReal_pathELength_exponentialVariation hab
      (fun t ht ↦ (hV t ht).of_le (by norm_num)) hC hspeed).continuousAt
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hminR
  rw [(hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hγ hC hspeed).deriv] at hnn
  exact (div_nonneg_iff.mp hnn).resolve_right (not_and_of_not_right _ hC.not_ge) |>.1

/-- **Negative normal index form strictly decreases `pathELength`.** Let `γ` be a geodesic on
`(a, b)` of constant speed `C > 0` on `[a, b]` (`a ≤ b`), and `V` a `C³` field along `γ` on `[a, b]`
with `⟪V(b), γ'(b)⟫ = ⟪V(a), γ'(a)⟫`. If `I(V^⊥, V^⊥) < 0`, then for every sufficiently small
`s ≠ 0` the curve `exp_(γ ·) (s • V ·)` has strictly smaller `pathELength` (in `ℝ≥0∞`) than `γ`. -/
theorem eventually_pathELength_exponentialVariation_lt_of_indexForm_neg {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    {C : ℝ} (hC : 0 < C) (hspeed : ∀ t ∈ Icc a b, ‖curveVelocity I γ t‖ = C)
    (hbdry : ⟪V b, curveVelocity I γ b⟫_ℝ = ⟪V a, curveVelocity I γ a⟫_ℝ)
    (hneg : indexForm I γ
      (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t))
      (fun t ↦ V t - (ℝ ∙ curveVelocity I γ t).starProjection (V t)) a b < 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      Manifold.pathELength I (exponentialVariation I γ V s) a b <
        Manifold.pathELength I γ a b := by
  have hd₁ := hasDerivAt_toReal_pathELength_exponentialVariation hab
    (fun t ht ↦ (hV t ht).of_le (by norm_num)) hC hspeed
  have hbulk : ∫ t in a..b, ⟪V t, acceleration (leviCivitaConnection I M) γ t⟫_ℝ = 0 := by
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIoo_of_le hab] at ht
    rw [← accelerationWithin_of_mem_nhds _ γ (isOpen_Ioo.mem_nhds ht),
      hγ.accelerationWithin_eq_zero t ht, inner_zero_right]
  have hd₁_zero :
      deriv (fun s ↦ (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal) 0 = 0 := by
    rw [hd₁.deriv, hbulk, hbdry, sub_self, sub_zero, zero_div]
  have hd₂ := hasDerivAt_deriv_toReal_pathELength_exponentialVariation hab hV hγ hC hspeed
  have hltR : ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      (Manifold.pathELength I (exponentialVariation I γ V s) a b).toReal <
        (Manifold.pathELength I γ a b).toReal := by
    simpa only [exponentialVariation_zero] using
      TauCeti.eventually_gt_of_deriv_deriv_neg
        (hd₂.deriv.symm ▸ div_neg_of_neg_of_pos hneg hC) hd₁_zero hd₁.continuousAt
  have hfin := eventually_pathELength_exponentialVariation_ne_top hab
    fun t ht ↦ (hV t ht).of_le (by norm_num)
  have hfin0 : Manifold.pathELength I γ a b ≠ ⊤ := by
    simpa only [exponentialVariation_zero] using hfin.self_of_nhds
  filter_upwards [hltR, nhdsWithin_le_nhds hfin] with s hs hfs
  exact (ENNReal.toReal_lt_toReal hfs hfin0).mp hs

end ExponentialLength

end TauCeti.Manifold
