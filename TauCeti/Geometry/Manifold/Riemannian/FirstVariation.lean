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
curves near `s = 0` share the endpoints of `γ`, the boundary terms vanish.

The formula holds for a family which is `C²` at the points of `{0} × [a, b]`, for the tangent
bundle of a `C²` manifold carrying a `C¹` Riemannian metric; its integrand is then continuous on
`[a, b]`.  It is the tool for studying the critical points of the energy, the `C²` curves for which
this derivative vanishes for every variation with fixed endpoints.  Those critical points are
exactly the geodesics (`TauCeti.Geometry.Manifold.Riemannian.Geodesic.FirstVariation`).

## Main definitions and results

* `TauCeti.Manifold.hasDerivAt_energy`: **the first variation formula** for the energy, with
  boundary terms.
* `TauCeti.Manifold.hasDerivAt_energy_of_fixed_endpoints`: the first variation formula for a
  variation fixing the endpoints near `s = 0`.
* `TauCeti.Manifold.continuousAt_inner_variationField_alongCurve`: the integrand
  `⟪V(t), D_t γ'(t)⟫` of the first variation formula is continuous where the family is `C²`.
* `TauCeti.Manifold.IsEnergyCritical`: critical points of the energy among variations with fixed
  endpoints, which are `C²` curves by definition; for a `C²` curve, criticality is characterized
  through the first variation formula by
  `TauCeti.Manifold.isEnergyCritical_iff_integral_inner_eq_zero`.

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

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

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
form of the integration by parts in the first variation formula, with the partial velocities
written through the differential of the uncurried family. -/
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

/-- **Continuity of the first-variation integrand.** At a parameter `t` where the family is `C²`,
the integrand `r ↦ ⟪V(r), D_r γ'(r)⟫` of the first variation formula is continuous, where `V` is
the variation field and `D_r γ'` is the covariant acceleration of `γ = F 0`. -/
theorem continuousAt_inner_variationField_alongCurve {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContinuousAt (fun r ↦ inner ℝ (variationField I F r)
      (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) r)) t := by
  -- the family is `C²` on an open product neighbourhood `U ×ˢ V` of `(0, t)`
  have hWo : IsOpen {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} :=
    TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  obtain ⟨U, V, hUo, hVo, h0U, htV, hUV⟩ := isOpen_prod_iff.mp hWo 0 t hf
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  have hfUV : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V) :=
    fun z hz ↦ (hUV hz).contMDiffWithinAt
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
  -- on `V`, the integrand is `d/dr K (0, r) - ½ ∂_s G (0, r)`, which is continuous there
  have hpt : ∀ r ∈ V, fderiv ℝ G (0, r) (1, 0) / 2 =
      deriv (fun r ↦ K (0, r)) r - inner ℝ (variationField I F r)
        (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) r) :=
    fun r hr ↦ fderiv_inner_mfderiv_fst_eq (hUV ⟨h0U, hr⟩)
  have hGcont : ContinuousAt (fun r ↦ fderiv ℝ G (0, r) (1, 0)) t :=
    (((hG.continuousOn_fderiv_of_isOpen hUVo le_rfl).continuousAt
      (hUVo.mem_nhds ⟨h0U, htV⟩)).comp (Continuous.prodMk_right (0 : ℝ)).continuousAt).clm_apply
      continuousAt_const
  refine (((hK0.continuousOn_deriv_of_isOpen hVo le_rfl).continuousAt (hVo.mem_nhds htV)).sub
    (hGcont.div_const 2)).congr ?_
  filter_upwards [hVo.mem_nhds htV] with r hr
  simp only [Pi.sub_apply, hpt r hr]
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
      (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_variationField_alongCurve (hF t ht)).continuousWithinAt
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

/-- **The first variation of energy for a variation with fixed endpoints.** If moreover the
curves of the family near `s = 0` have the same endpoints as `γ = F 0`, the derivative at `s = 0`
of the energy is `-∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`. -/
theorem hasDerivAt_energy_of_fixed_endpoints {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (ha : ∀ᶠ s in 𝓝 0, F s a = F 0 a) (hb : ∀ᶠ s in 𝓝 0, F s b = F 0 b) :
    HasDerivAt (fun s ↦ energy I (F s) a b)
      (-∫ t in a..b, inner ℝ (variationField I F t)
        (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) 0 := by
  refine (hasDerivAt_energy hF).congr_deriv ?_
  rw [variationField_eq_zero ha, variationField_eq_zero hb, inner_zero_left, inner_zero_left]
  ring

end FirstVariation

/-! ### Critical points of the energy -/

section Critical

variable (I) in
/-- A curve `γ` is a **critical point of the energy** between the parameters `a` and `b` when it
is `C²` at every point of `[a, b]` and every variation of `γ` with fixed endpoints leaves the
energy stationary to first order: for every two-parameter family `F` with `F 0 = γ` which is `C²`
at every point of `{0} × [a, b]` and whose curves near `s = 0` share the endpoints of `γ`, the
energy of `F s` between `a` and `b` has derivative `0` at `s = 0`.  The regularity of `γ` is part
of the definition: a curve which is not `C²` on `[a, b]` admits no such variation, and is not
critical.  The criticality of geodesics and its converse are in
`TauCeti.Geometry.Manifold.Riemannian.Geodesic.FirstVariation`. -/
structure IsEnergyCritical (γ : ℝ → M) (a b : ℝ) : Prop where
  /-- A critical point of the energy is `C²` at every point of `[a, b]`. -/
  contMDiffAt : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t
  /-- The energy of a fixed-endpoint variation of a critical point has derivative `0` at
  `s = 0`. -/
  hasDerivAt : ∀ {F : ℝ → ℝ → M}, F 0 = γ →
    (∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) →
    (∀ᶠ s in 𝓝 0, F s a = γ a) → (∀ᶠ s in 𝓝 0, F s b = γ b) →
    HasDerivAt (fun s ↦ energy I (F s) a b) 0 0

variable {γ : ℝ → M} {a b : ℝ}

/-- **Criticality through the first variation formula.** A curve `γ` which is `C²` at every point
of `[a, b]` is a critical point of the energy between `a` and `b` exactly when
`∫_a^b ⟪V(t), D_t γ'(t)⟫ dt = 0` for the variation field `V` of every variation `F` of `γ = F 0`
with fixed endpoints which is `C²` at every point of `{0} × [a, b]`. -/
theorem isEnergyCritical_iff_integral_inner_eq_zero
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t) :
    IsEnergyCritical I γ a b ↔ ∀ F : ℝ → ℝ → M, F 0 = γ →
      (∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) →
      (∀ᶠ s in 𝓝 0, F s a = γ a) → (∀ᶠ s in 𝓝 0, F s b = γ b) →
      ∫ t in a..b, inner ℝ (variationField I F t)
        (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t) = 0 := by
  refine ⟨fun h F hF0 hF ha hb ↦ ?_, fun h ↦ ⟨hγ, fun {F} hF0 hF ha hb ↦ ?_⟩⟩
  · subst hF0
    exact neg_eq_zero.mp ((hasDerivAt_energy_of_fixed_endpoints hF ha hb).unique
      (h.hasDerivAt rfl hF ha hb))
  · subst hF0
    have hvar := hasDerivAt_energy_of_fixed_endpoints hF ha hb
    rwa [h _ rfl hF ha hb, neg_zero] at hvar

end Critical

end TauCeti.Manifold

end
