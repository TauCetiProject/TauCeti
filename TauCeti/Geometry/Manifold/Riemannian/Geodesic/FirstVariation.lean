/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricIntegral
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Energy
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.VariationField

/-!
# The first variation of energy

The *energy* `E(γ) = ½ ∫_a^b ‖γ'(t)‖² dt` of a curve `γ` in a Riemannian manifold between the
parameters `a` and `b` is `TauCeti.Manifold.energy`, defined in
`TauCeti.Geometry.Manifold.Riemannian.Energy`.  A *variation* of `γ` is a two-parameter family
`F` with `F 0 = γ`, with *variation field* `V = TauCeti.Manifold.variationField I F`, the
transverse velocity `V(t) = ∂F/∂s (0, t)`.  This file computes the derivative at `s = 0` of the
energy of the curves `F s`:

`d/ds E(F s) |₀ = ⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`,

where `D_t γ'` is the covariant acceleration of `γ` for the Levi-Civita connection.  When the
variation fixes the endpoints the boundary terms vanish, and along a geodesic the integral
vanishes too: geodesics are critical points of the energy among fixed-endpoint variations.

The formula only asks the family to be `C²` at the points of `{0} × [a, b]`.  The proof
differentiates under the integral sign, which is legitimate because the squared speed of `F s`
is jointly `C¹` in `(s, t)` near the compact segment, then uses the two pointwise derivative
formulas of `TauCeti.Geometry.Manifold.Riemannian.VariationField`: the transverse derivative of
the squared speed is `2 ⟪D_t V, γ'⟫`, and the product rule for `⟪V, γ'⟫` along `γ` integrates by
parts.

## Main definitions and results

* `TauCeti.Manifold.IsGeodesicCurveOn.energy_eq`: the energy of a geodesic segment is
  `(b - a) ‖γ'(a)‖² / 2`.
* `TauCeti.Manifold.hasDerivAt_energy`: **the first variation formula** for the energy, with
  boundary terms.
* `TauCeti.Manifold.hasDerivAt_energy_of_fixed_endpoints`: the first variation formula for a
  variation fixing the endpoints.
* `TauCeti.Manifold.IsGeodesicCurveOn.hasDerivAt_energy_zero`: **geodesics are critical
  points of the energy** among variations with fixed endpoints.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, Proposition 2.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12, the energy
  of a path and its first variation.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6, the first
  variation formula for length, whose proof follows the same scheme.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-! ### The energy of a geodesic segment -/

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The energy of a geodesic segment.** A geodesic has constant speed, so its energy between
`a` and `b` is `(b - a) ‖γ'(a)‖² / 2`. -/
theorem IsGeodesicCurveOn.energy_eq {γ : ℝ → M} {s : Set ℝ} (h : IsGeodesicCurveOn I γ s)
    (hs : IsOpen s) {a b : ℝ} (hsub : uIcc a b ⊆ s) :
    energy I γ a b = (b - a) * ‖curveVelocity I γ a‖ ^ 2 / 2 := by
  -- constant speed is a statement about a preconnected parameter set: pass to the connected
  -- component of `s` containing the segment, which is open and still contains `[a, b]`
  have hs'o : IsOpen (connectedComponentIn s a) := hs.connectedComponentIn
  have hsub' : uIcc a b ⊆ connectedComponentIn s a :=
    isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hsub
  have h' : IsGeodesicCurveOn I γ (connectedComponentIn s a) :=
    h.mono hs'o.uniqueDiffOn (connectedComponentIn_subset s a)
  have ha : a ∈ connectedComponentIn s a := hsub' left_mem_uIcc
  have key : EqOn (fun t ↦ ‖curveVelocity I γ t‖ ^ 2) (fun _ ↦ ‖curveVelocity I γ a‖ ^ 2)
      (uIcc a b) := by
    intro t ht
    have ht' : t ∈ connectedComponentIn s a := hsub' ht
    simp only
    rw [← curveVelocityWithin_of_mem_nhds (hs'o.mem_nhds ht'),
      ← curveVelocityWithin_of_mem_nhds (hs'o.mem_nhds ha),
      h'.norm_curveVelocityWithin_eq isPreconnected_connectedComponentIn ht' ha]
  rw [energy_def, intervalIntegral.integral_congr key, intervalIntegral.integral_const,
    smul_eq_mul]

/-! ### The first variation of energy -/

section FirstVariation

variable {F : ℝ → ℝ → M}

omit [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The squared speed of a curve of the family, written through the differential of the uncurried
family. -/
private theorem inner_mfderiv_snd_self_eq_norm_sq_curveVelocity {s t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t)) :
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) ((0 : ℝ), (1 : ℝ)))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) ((0 : ℝ), (1 : ℝ))) =
      ‖curveVelocity I (F s) t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, curveVelocity_eq_mfderiv_snd hf]

omit [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The pairing of the variation field with the velocity of the central curve, written through
the differential of the uncurried family. -/
private theorem inner_mfderiv_fst_snd_eq_inner_variationField_curveVelocity {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) ((1 : ℝ), (0 : ℝ)))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) ((0 : ℝ), (1 : ℝ))) =
      inner ℝ (variationField I F t) (curveVelocity I (F 0) t) := by
  rw [variationField_eq_mfderiv hf, curveVelocity_eq_mfderiv_snd hf]

/-- **The integrand of the first variation.** At a parameter `t` where the family is `C²`, half
the `s`-derivative at `s = 0` of the squared speed `‖∂_t F (s, t)‖²` is the `t`-derivative of
`⟪∂_s F (0, t), ∂_t F (0, t)⟫ = ⟪V(t), γ'(t)⟫` minus `⟪V(t), D_t γ'(t)⟫`.  This is the pointwise
form of the integration by parts in the first variation formula; the partial velocities are
written through the differential of the uncurried family, so that both sides are functions of
`(s, t)` to which the calculus of `fderiv` and `deriv` applies. -/
private theorem fderiv_inner_mfderiv_fst_eq {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    fderiv ℝ (fun z : ℝ × ℝ ↦
        inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ))))
        (0, t) (1, 0) / 2 =
      deriv (fun r ↦
        inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, r) ((1 : ℝ), (0 : ℝ)))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, r) ((0 : ℝ), (1 : ℝ)))) t -
      inner ℝ (variationField I F t)
        (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t) := by
  -- the family is `C²` on the open set `W` of points where it is `C²`, which contains a product
  -- neighbourhood `U ×ˢ V` of `(0, t)`
  have hWo : IsOpen {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} :=
    TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  have hfW : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2)
      {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} :=
    fun _ hz ↦ hz.contMDiffWithinAt
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hf)
  set G : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
  set K : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((1 : ℝ), (0 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
  have hGz : HasFDerivAt G (fderiv ℝ G (0, t)) (0, t) :=
    (((hfW.contDiffOn_inner_mfderiv (by norm_num) hWo _ _).differentiableOn one_ne_zero _ hf)
      |>.differentiableAt (hWo.mem_nhds hf)).hasFDerivAt
  have hKz : HasFDerivAt K (fderiv ℝ K (0, t)) (0, t) :=
    (((hfW.contDiffOn_inner_mfderiv (by norm_num) hWo _ _).differentiableOn one_ne_zero _ hf)
      |>.differentiableAt (hWo.mem_nhds hf)).hasFDerivAt
  have hpathG : HasDerivAt (fun s : ℝ ↦ (s, t)) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id' (x := (0 : ℝ))).prodMk (hasDerivAt_const (0 : ℝ) t)
  have hpathK : HasDerivAt (fun r : ℝ ↦ ((0 : ℝ), r)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id' (x := t))
  have hGs : HasDerivAt (fun s ↦ G (s, t)) (fderiv ℝ G (0, t) (1, 0)) 0 := by
    exact hGz.comp_hasDerivAt (0 : ℝ) hpathG
  have hKt : HasDerivAt (fun r ↦ K (0, r)) (fderiv ℝ K (0, t) (0, 1)) t := by
    exact hKz.comp_hasDerivAt t hpathK
  -- on `U ×ˢ V`, `G` is the squared speed and `K (0, ·)` is `⟪V, γ'⟫`
  have hGeq : (fun s ↦ G (s, t)) =ᶠ[𝓝 0] fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2 := by
    filter_upwards [hU] with s hs
    exact inner_mfderiv_snd_self_eq_norm_sq_curveVelocity
      ((hUV ⟨hs, mem_of_mem_nhds hV⟩ : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 _ (s, t)).mdifferentiableAt
        two_ne_zero)
  have hKeq : (fun r ↦ K (0, r)) =ᶠ[𝓝 t]
      fun r ↦ inner ℝ (variationField I F r) (curveVelocity I (F 0) r) := by
    filter_upwards [hV] with r hr
    exact inner_mfderiv_fst_snd_eq_inner_variationField_curveVelocity
      ((hUV ⟨mem_of_mem_nhds hU, hr⟩ : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 _ ((0 : ℝ), r))
        |>.mdifferentiableAt two_ne_zero)
  have h1 := hGs.unique ((hasDerivAt_norm_sq_curveVelocity hf).congr_of_eventuallyEq hGeq)
  have h2 := hKt.unique
    ((hasDerivAt_inner_variationField_curveVelocity hf).congr_of_eventuallyEq hKeq)
  rw [h1, hKt.deriv, h2]
  ring

/-- **The first variation of energy.** Let `F` be a two-parameter family which is `C²` at every
point of `{0} × [a, b]`, with central curve `γ = F 0` and variation field `V`.  Then the energy
of `F s` between `a` and `b` is differentiable at `s = 0`, with derivative

`⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`,

where `D_t γ'` is the covariant acceleration of `γ` for the Levi-Civita connection. -/
theorem hasDerivAt_energy {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (fun s ↦ energy I (F s) a b)
      (inner ℝ (variationField I F b) (curveVelocity I (F 0) b) -
        inner ℝ (variationField I F a) (curveVelocity I (F 0) a) -
        ∫ t in a..b, inner ℝ (variationField I F t)
          (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) 0 := by
  obtain ⟨U, V, hUo, hVo, h0U, hV, hfUV⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  have hsurf : ∀ {s t : ℝ}, s ∈ U → t ∈ V →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) :=
    fun hs ht ↦ hfUV.contMDiffAt (hUVo.mem_nhds ⟨hs, ht⟩)
  -- The squared speed `G` and the inner product `K` of the partial velocities, as jointly `C¹`
  -- functions of `(s, t)` on `U ×ˢ V`.
  set G : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
  set K : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((1 : ℝ), (0 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
  have hG : ContDiffOn ℝ 1 G (U ×ˢ V) := hfUV.contDiffOn_inner_mfderiv (by norm_num) hUVo _ _
  have hK0 : ContDiffOn ℝ 1 (fun r ↦ K (0, r)) V :=
    (hfUV.contDiffOn_inner_mfderiv (by norm_num) hUVo _ _).comp
      (contDiff_prodMk_right (0 : ℝ)).contDiffOn fun r hr ↦ ⟨h0U, hr⟩
  have hGeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V → G (s, t) = ‖curveVelocity I (F s) t‖ ^ 2 :=
    fun hs ht ↦ inner_mfderiv_snd_self_eq_norm_sq_curveVelocity
      ((hsurf hs ht).mdifferentiableAt two_ne_zero)
  have hKeq : ∀ t ∈ V, K (0, t) = inner ℝ (variationField I F t) (curveVelocity I (F 0) t) :=
    fun t ht ↦ inner_mfderiv_fst_snd_eq_inner_variationField_curveVelocity
      ((hsurf h0U ht).mdifferentiableAt two_ne_zero)
  -- Differentiation under the integral sign: near `s = 0` the energy is `½ ∫ G (s, t) dt`.
  have henergy : (fun s ↦ energy I (F s) a b) =ᶠ[𝓝 0] fun s ↦ (∫ t in a..b, G (s, t)) / 2 := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    rw [energy_def]
    congr 1
    exact intervalIntegral.integral_congr fun t ht ↦ (hGeq hs (hV ht)).symm
  obtain ⟨hG'int, hGderiv⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUVo hG
    (prod_mono (singleton_subset_iff.mpr h0U) hV)
  have hmain : HasDerivAt (fun s ↦ energy I (F s) a b)
      ((∫ t in a..b, fderiv ℝ G (0, t) (1, 0)) / 2) 0 :=
    (hGderiv.div_const 2).congr_of_eventuallyEq henergy
  -- Pointwise on `V`, the integrand is `d/dt K (0, t) - ⟪V(t), D_t γ'(t)⟫`; both terms are
  -- continuous on `V`, and the fundamental theorem of calculus evaluates the first at the
  -- endpoints.
  have hpt : ∀ t ∈ V, fderiv ℝ G (0, t) (1, 0) / 2 =
      deriv (fun r ↦ K (0, r)) t - inner ℝ (variationField I F t)
        (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t) :=
    fun t ht ↦ fderiv_inner_mfderiv_fst_eq (hsurf h0U ht)
  have hK0cont : ContinuousOn (deriv fun r ↦ K (0, r)) V :=
    hK0.continuousOn_deriv_of_isOpen hVo le_rfl
  have hK'int : IntervalIntegrable (deriv fun r ↦ K (0, r)) volume a b :=
    (hK0cont.mono hV).intervalIntegrable
  have hVAint : IntervalIntegrable (fun t ↦ inner ℝ (variationField I F t)
      (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) volume a b := by
    refine (hK'int.sub (hG'int.div_const 2)).congr fun t ht ↦ ?_
    rw [hpt t (hV (uIoc_subset_uIcc ht))]
    ring
  have hFTC : ∫ t in a..b, deriv (fun r ↦ K (0, r)) t = K (0, b) - K (0, a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ ((hK0.differentiableOn one_ne_zero t (hV ht)).differentiableAt
        (hVo.mem_nhds (hV ht))).hasDerivAt) hK'int
  refine hmain.congr_deriv ?_
  calc (∫ t in a..b, fderiv ℝ G (0, t) (1, 0)) / 2
      = ∫ t in a..b, fderiv ℝ G (0, t) (1, 0) / 2 := (intervalIntegral.integral_div 2 _).symm
    _ = ∫ t in a..b, (deriv (fun r ↦ K (0, r)) t - inner ℝ (variationField I F t)
          (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) :=
        intervalIntegral.integral_congr fun t ht ↦ hpt t (hV ht)
    _ = (∫ t in a..b, deriv (fun r ↦ K (0, r)) t) -
          ∫ t in a..b, inner ℝ (variationField I F t)
            (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t) :=
        intervalIntegral.integral_sub hK'int hVAint
    _ = _ := by rw [hFTC, hKeq b (hV right_mem_uIcc), hKeq a (hV left_mem_uIcc)]

/-- **The first variation of energy for a variation with fixed endpoints.** If moreover every
curve of the family has the same endpoints as `γ = F 0`, the derivative at `s = 0` of the energy
is `-∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`. -/
theorem hasDerivAt_energy_of_fixed_endpoints {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (ha : ∀ s, F s a = F 0 a) (hb : ∀ s, F s b = F 0 b) :
    HasDerivAt (fun s ↦ energy I (F s) a b)
      (-∫ t in a..b, inner ℝ (variationField I F t)
        (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) 0 := by
  refine (hasDerivAt_energy hF).congr_deriv ?_
  rw [variationField_eq_zero ha, variationField_eq_zero hb, inner_zero_left, inner_zero_left]
  ring

/-- **Geodesics are critical points of the energy.** If the central curve `γ = F 0` of a
variation with fixed endpoints is a geodesic on an open set containing `[a, b]`, the derivative
at `s = 0` of the energy of `F s` vanishes. -/
theorem IsGeodesicCurveOn.hasDerivAt_energy_zero {a b : ℝ} {s : Set ℝ}
    (h : IsGeodesicCurveOn I (F 0) s) (hs : IsOpen s) (hsub : uIcc a b ⊆ s)
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (ha : ∀ s, F s a = F 0 a) (hb : ∀ s, F s b = F 0 b) :
    HasDerivAt (fun s ↦ energy I (F s) a b) 0 0 := by
  refine (hasDerivAt_energy_of_fixed_endpoints hF ha hb).congr_deriv ?_
  rw [neg_eq_zero]
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
    intervalIntegral.integral_zero
  simp only [((isGeodesicCurveOn_iff_of_isOpen hs).mp h).2 t (hsub ht), inner_zero_right]

end FirstVariation

end TauCeti.Manifold

end
