/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The first variation of length

Let `F : ℝ → ℝ → M` be a variation of the curve `γ = F 0` in a Riemannian manifold, with
variation field `V = TauCeti.Manifold.variationField I F`. At a parameter where `γ` is regular,
the transverse derivative of the speed is `⟪D_t V, γ'⟫ / ‖γ'‖`. When `γ` is regular on `[a, b]`,
differentiating under the integral sign shows that the derivative at `s = 0` of the length of the
curves `F s` between `a` and `b` is the integral of this transverse derivative. When `γ` moreover
has constant speed `C > 0`, integrating by parts gives

`d/ds L(F s) |₀ = (⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt) / C`.

The endpoints `F s a` and `F s b` are allowed to move, so the boundary terms are kept. Up to the
factor `1 / C`, this is the first variation of energy `TauCeti.Manifold.hasDerivAt_energy`.

## Main results

* `TauCeti.Manifold.hasDerivAt_norm_curveVelocity`: the transverse derivative of the speed at a
  regular parameter.
* `TauCeti.Manifold.hasDerivAt_toReal_pathELength_of_curveVelocity_ne_zero`: the derivative of the
  length of a regular curve is the integral of the transverse derivative of its speed.
* `TauCeti.Manifold.hasDerivAt_toReal_pathELength`: **the first variation formula** for the
  length of a constant-speed curve, with boundary terms.
* `TauCeti.Manifold.hasDerivAt_toReal_pathELength_of_norm_curveVelocity_eq_one`: the same for a
  unit-speed curve.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6, the first
  variation formula for length.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, for the corresponding
  formula for energy.
-/

public noncomputable section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-- **The transverse derivative of the speed.** At a parameter `t` where the family is `C²` and
the central curve `γ = F 0` has nonzero velocity, the function `s ↦ ‖∂_t F (s, t)‖` has
derivative `⟪D_t V(t), γ'(t)⟫ / ‖γ'(t)‖` at `s = 0`, where `V` is the variation field. -/
theorem hasDerivAt_norm_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (fun s ↦ ‖curveVelocity I (F s) t‖)
      (⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ / ‖curveVelocity I (F 0) t‖) 0 := by
  have hd := (hasDerivAt_norm_sq_curveVelocity hf).sqrt (pow_ne_zero 2 (norm_ne_zero_iff.2 hγ))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hd
  convert hd using 1
  field_simp

/-- The transverse derivative of the speed at a parameter where the central curve has unit
speed is `⟪D_t V(t), γ'(t)⟫`. -/
theorem hasDerivAt_norm_curveVelocity_of_norm_eq_one {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ‖curveVelocity I (F 0) t‖ = 1) :
    HasDerivAt (fun s ↦ ‖curveVelocity I (F s) t‖)
      ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ 0 := by
  simpa only [hγ, div_one] using
    hasDerivAt_norm_curveVelocity hf (norm_ne_zero_iff.1 (by rw [hγ]; exact one_ne_zero))

/-- **Continuity of the transverse speed derivative.** At a parameter `t` where the family is
`C²`, the function `r ↦ ⟪D_t V(r), γ'(r)⟫` is continuous, where `V` is the variation field and
`γ = F 0` is the central curve. -/
theorem continuousAt_inner_alongCurve_variationField_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContinuousAt (fun r ↦ ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) r,
      curveVelocity I (F 0) r⟫_ℝ) t := by
  -- the family is `C²` on an open product neighbourhood `U ×ˢ V` of `(0, t)`
  have hWo : IsOpen {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} :=
    TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  obtain ⟨U, V, hUo, hVo, h0U, htV, hUV⟩ := isOpen_prod_iff.mp hWo 0 t hf
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  have hfUV : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) :=
    fun z hz ↦ (hUV hz).contMDiffWithinAt
  -- the squared speed `G (s, r) = ‖∂_r F (s, r)‖ ^ 2`, jointly `C¹` on `U ×ˢ V`
  let G : ℝ × ℝ → ℝ := fun z ↦
    ⟪mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z ↦ F z.1 z.2) z (0, 1),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z ↦ F z.1 z.2) z (0, 1)⟫_ℝ
  have hG : ContDiffOn ℝ 1 G (U ×ˢ V) :=
    hfUV.contDiffOn_inner_mfderiv (by norm_num) hUVo (0, 1) (0, 1)
  have hGcont : ContinuousAt (fun r ↦ fderiv ℝ G (0, r) (1, 0)) t :=
    (((hG.continuousOn_fderiv_of_isOpen hUVo le_rfl).continuousAt
      (hUVo.mem_nhds ⟨h0U, htV⟩)).comp (Continuous.prodMk_right (0 : ℝ)).continuousAt).clm_apply
      continuousAt_const
  -- on `V`, the function is `½ ∂_s G (0, r)`
  refine (hGcont.div_const 2).congr ?_
  filter_upwards [hVo.mem_nhds htV] with r hr
  have hr' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, r) := hUV ⟨h0U, hr⟩
  have hpath : HasDerivAt (fun s : ℝ ↦ (s, r)) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id' (x := (0 : ℝ))).prodMk (hasDerivAt_const (0 : ℝ) r)
  have hGd := ((hG.differentiableOn one_ne_zero (0, r) ⟨h0U, hr⟩).differentiableAt
    (hUVo.mem_nhds ⟨h0U, hr⟩)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hpath
  have heq : (fun s ↦ ‖curveVelocity I (F s) r‖ ^ 2) =ᶠ[𝓝 0] fun s ↦ G (s, r) := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    dsimp only [G]
    rw [← curveVelocity_eq_mfderiv_snd
      ((hUV ⟨hs, hr⟩ : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 _ (s, r)).mdifferentiableAt two_ne_zero),
      real_inner_self_eq_norm_sq]
  have he := (hGd.congr_of_eventuallyEq heq).unique (hasDerivAt_norm_sq_curveVelocity hr')
  simp only [he]
  ring

/-- **The first variation of length of a regular curve.** Let `F` be a two-parameter family which
is `C²` at every point of `{0} × [a, b]`, whose central curve `γ = F 0` has nonzero velocity on
`[a, b]`. Then the length of `F s` between `a` and `b` is differentiable at `s = 0`, with
derivative `∫_a^b ⟪D_t V(t), γ'(t)⟫ / ‖γ'(t)‖ dt`, the integral of the transverse derivative of
the speed `hasDerivAt_norm_curveVelocity`. The endpoints of the curves `F s` are not required to
be fixed. -/
theorem hasDerivAt_toReal_pathELength_of_curveVelocity_ne_zero {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, curveVelocity I (F 0) t ≠ 0) :
    HasDerivAt (fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (∫ t in a..b, ⟪alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t,
        curveVelocity I (F 0) t⟫_ℝ / ‖curveVelocity I (F 0) t‖) 0 := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  rw [← uIcc_of_le hab] at hF hγ
  obtain ⟨U, V, hUo, hVo, h0U, hV, hfUV⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  -- the squared speed `G (s, t) = ‖∂_t F (s, t)‖ ^ 2`, jointly `C¹` on `U ×ˢ V`
  let G : ℝ × ℝ → ℝ := fun z ↦
    ⟪mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z ↦ F z.1 z.2) z (0, 1),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z ↦ F z.1 z.2) z (0, 1)⟫_ℝ
  have hG : ContDiffOn ℝ 1 G (U ×ˢ V) :=
    hfUV.contDiffOn_inner_mfderiv (by norm_num) hUVo (0, 1) (0, 1)
  have hGeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V → G (s, t) = ‖curveVelocity I (F s) t‖ ^ 2 :=
    fun hs ht ↦ by
      dsimp only [G]
      rw [← curveVelocity_eq_mfderiv_snd
        ((hfUV.contMDiffAt (hUVo.mem_nhds ⟨hs, ht⟩)).mdifferentiableAt two_ne_zero),
        real_inner_self_eq_norm_sq]
  -- the speed `L = √G` is `C¹` on the open set `W` where `G` is positive, which contains
  -- `{0} × [a, b]` because `γ` is regular there
  let W := (U ×ˢ V) ∩ G ⁻¹' Ioi 0
  have hWo : IsOpen W := hG.continuousOn.isOpen_inter_preimage hUVo isOpen_Ioi
  let L : ℝ × ℝ → ℝ := fun z ↦ Real.sqrt (G z)
  have hL : ContDiffOn ℝ 1 L W :=
    (hG.mono inter_subset_left).sqrt fun _ hz ↦ ne_of_gt hz.2
  have hsub : {0} ×ˢ uIcc a b ⊆ W := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    refine ⟨⟨h0U, hV ht⟩, ?_⟩
    rw [mem_preimage, mem_Ioi, hGeq h0U (hV ht)]
    exact pow_pos (norm_pos_iff.2 (hγ t ht)) 2
  have hLeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V → L (s, t) = ‖curveVelocity I (F s) t‖ :=
    fun hs ht ↦ by dsimp only [L]; rw [hGeq hs ht, Real.sqrt_sq (norm_nonneg _)]
  -- differentiation under the integral sign
  obtain ⟨_, hDLI⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hWo hL hsub
  have hlength : (fun s ↦ (Manifold.pathELength I (F s) a b).toReal) =ᶠ[𝓝 0]
      fun s ↦ ∫ t in a..b, L (s, t) := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    have hγs : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (F s) V :=
      (hfUV.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).comp
        (contDiff_prodMk_right s).contMDiff.contMDiffOn (fun t ht ↦ ⟨hs, ht⟩)
    have hVs : Icc a b ⊆ V := by simpa only [uIcc_of_le hab] using hV
    rw [hγs.pathELength_eq_ofReal_integral_norm_curveVelocityWithin hVo.uniqueMDiffOn hab hVs,
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab (fun _ _ ↦ norm_nonneg _))]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [curveVelocityWithin_of_mem_nhds (hVo.mem_nhds (hV ht)), hLeq hs (hV ht)]
  refine (hDLI.congr_of_eventuallyEq hlength).congr_deriv
    (intervalIntegral.integral_congr fun t ht ↦ ?_)
  -- pointwise, `∂_s L (0, t)` is the transverse derivative of the speed
  have hpath : HasDerivAt (fun s : ℝ ↦ (s, t)) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id' (x := (0 : ℝ))).prodMk (hasDerivAt_const (0 : ℝ) t)
  have hLd := ((hL.differentiableOn one_ne_zero (0, t) (hsub ⟨rfl, ht⟩)).differentiableAt
    (hWo.mem_nhds (hsub ⟨rfl, ht⟩))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hpath
  have heq : (fun s ↦ ‖curveVelocity I (F s) t‖) =ᶠ[𝓝 0] fun s ↦ L (s, t) := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    exact (hLeq hs (hV ht)).symm
  exact (hLd.congr_of_eventuallyEq heq).unique (hasDerivAt_norm_curveVelocity (hF t ht) (hγ t ht))

/-- **The first variation of length.** Let `F` be a two-parameter family which is `C²` at every
point of `{0} × [a, b]`, whose central curve `γ = F 0` has constant speed `C > 0` on `[a, b]`.
Then the length of `F s` between `a` and `b` is differentiable at `s = 0`, with derivative

`(⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt) / C`,

where `V` is the variation field and `D_t γ'` is the covariant acceleration of `γ` for the
Levi-Civita connection. The endpoints of the curves `F s` are not required to be fixed. -/
theorem hasDerivAt_toReal_pathELength {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    {C : ℝ} (hC : 0 < C) (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = C) :
    HasDerivAt (fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      ((⟪variationField I F b, curveVelocity I (F 0) b⟫_ℝ -
        ⟪variationField I F a, curveVelocity I (F 0) a⟫_ℝ -
        ∫ t in a..b, ⟪variationField I F t,
          acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) / C) 0 := by
  refine (hasDerivAt_toReal_pathELength_of_curveVelocity_ne_zero hab hF fun t ht ↦
    norm_ne_zero_iff.1 (by rw [hγ t ht]; exact hC.ne')).congr_deriv ?_
  rw [← uIcc_of_le hab] at hF hγ
  -- integrate by parts: `⟪D_t V, γ'⟫ = d/dt ⟪V, γ'⟫ - ⟪V, D_t γ'⟫`
  have hint₁ : IntervalIntegrable (fun t ↦ ⟪alongCurve (leviCivitaConnection I M) (F 0)
      (variationField I F) t, curveVelocity I (F 0) t⟫_ℝ) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_alongCurve_variationField_curveVelocity (hF t ht)).continuousWithinAt
  have hint₂ : IntervalIntegrable (fun t ↦ ⟪variationField I F t,
      acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_variationField_acceleration (hF t ht)).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_inner_variationField_curveVelocity (hF t ht)) (hint₁.add hint₂)
  rw [intervalIntegral.integral_add hint₁ hint₂] at hFTC
  rw [intervalIntegral.integral_congr fun t ht ↦ by rw [hγ t ht],
    intervalIntegral.integral_div, eq_sub_of_add_eq hFTC]

/-- **The first variation of length of a unit-speed curve.** For a two-parameter family `F` which
is `C²` at every point of `{0} × [a, b]`, whose central curve `γ = F 0` has unit speed on
`[a, b]`, the derivative at `s = 0` of the length of `F s` between `a` and `b` is
`⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`. -/
theorem hasDerivAt_toReal_pathELength_of_norm_curveVelocity_eq_one {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ Icc a b, ‖curveVelocity I (F 0) t‖ = 1) :
    HasDerivAt (fun s ↦ (Manifold.pathELength I (F s) a b).toReal)
      (⟪variationField I F b, curveVelocity I (F 0) b⟫_ℝ -
        ⟪variationField I F a, curveVelocity I (F 0) a⟫_ℝ -
        ∫ t in a..b, ⟪variationField I F t,
          acceleration (leviCivitaConnection I M) (F 0) t⟫_ℝ) 0 := by
  simpa only [div_one] using hasDerivAt_toReal_pathELength hab hF zero_lt_one hγ

end TauCeti.Manifold
