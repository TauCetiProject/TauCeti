/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Local
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The weak chain rule for measure-preserving Lipschitz changes of variables

Let `Φ : E → E'` be a measure-preserving map between finite-dimensional real normed spaces
carrying additive Haar measures, locally Lipschitz on an open set `U ⊆ E`, with `Φ '' U ⊆ V` for
an open set `V ⊆ E'`. If `u` has weak derivative `D` on `V`, then `u ∘ Φ` has
weak derivative

`x ↦ D (Φ x) ∘L fderiv ℝ Φ x`

on `U`: the classical chain rule survives the passage to weak derivatives. By Rademacher's
theorem `Φ` is differentiable almost everywhere on `U`, which is all the formula needs. No global
bound on the derivative of `Φ` and no integrability of `u` beyond local integrability is needed,
because weak derivatives are detected on relatively compact subdomains.

The typical change of variables of this kind is a shear `(t, y) ↦ (t - φ y, y)` of a product,
which flattens the region above the graph of a Lipschitz function `φ` onto a half-space; it is
measure-preserving by Fubini's theorem.

## The argument

Fix an open `W` whose closure is compact and contained in `U`. The image `K = Φ '' closure W` is
compact in `V`, so some open thickening `O` of `K` still lies in `V`, and `u`, `D` are integrable
on `O`. Mollify the zero extensions of `u` and `D` from `O` by normalized bumps of radius less
than the thickening. The mollified `u` is smooth with compact support, hence Lipschitz, and near
`K` its derivative is the mollified `D`
(`TauCeti.HasWeakFDerivOn.hasFDerivAt_indicator_convolution_normed`). Its composition with `Φ` is
therefore Lipschitz on `W`, with derivative given by the classical chain rule wherever `Φ` is
differentiable, so it is weakly differentiable (`LocallyLipschitzOn.hasWeakFDerivOn`). Since `Φ`
is measure-preserving, the `L¹(W)` distances to `u ∘ Φ` and to the candidate derivative are
bounded by the `L¹` distances of the mollifications to the zero extensions, the latter
multiplied by a Lipschitz constant of `Φ` on `closure W`, and these tend to zero
(`TauCeti.tendsto_eLpNorm_normed_convolution_sub`). Weak derivatives pass to such limits
(`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub`).

## Main declarations

* `TauCeti.HasWeakFDerivOn.comp_measurePreserving`: the weak chain rule.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.3 (smooth approximation).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6.
* W. P. Ziemer, *Weakly Differentiable Functions*, §2.2 (bi-Lipschitz changes of variables).
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal Topology Convolution

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} {ν : Measure E'}

variable [BorelSpace E] [μ.IsAddHaarMeasure] [BorelSpace E'] [ν.IsAddHaarMeasure]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [BorelSpace E'] [ν.IsAddHaarMeasure] in
/-- Precomposition with a measure-preserving map does not increase the lower integral of an
a.e.-measurable function over a set. -/
private theorem setLIntegral_comp_le {Φ : E → E'} (hΦ : MeasurePreserving Φ μ ν) (W : Set E)
    {g : E' → ℝ≥0∞} (hg : AEMeasurable g ν) :
    ∫⁻ x in W, g (Φ x) ∂μ ≤ ∫⁻ y, g y ∂ν := by
  refine (setLIntegral_le_lintegral _ _).trans_eq ?_
  rw [← hΦ.map_eq] at hg ⊢
  exact (lintegral_map' hg hΦ.measurable.aemeasurable).symm

omit [μ.IsAddHaarMeasure] [BorelSpace E'] [ν.IsAddHaarMeasure] in
/-- **Passing the chain rule to the limit.** Let `Φ` be measure-preserving, with
`‖fderiv ℝ Φ‖ ≤ M` on `W`. If each `f k ∘ Φ` has weak derivative `x ↦ G k (Φ x) ∘L fderiv ℝ Φ x`
on `W`, and `f k → g`, `G k → H` in `L¹` (through a.e.-strongly measurable differences), with
`g ∘ Φ` and `H ∘ Φ` integrable on `W`, then `g ∘ Φ` has weak derivative
`x ↦ H (Φ x) ∘L fderiv ℝ Φ x` on `W`. -/
private theorem hasWeakFDerivOn_comp_of_tendsto {W : Opens E} {Φ : E → E'}
    (hΦ : MeasurePreserving Φ μ ν) {M : ℝ}
    (hM : ∀ x ∈ (W : Set E), ‖fderiv ℝ Φ x‖ ≤ M)
    {f : ℕ → E' → F} {G : ℕ → E' → E' →L[ℝ] F} {g : E' → F} {H : E' → E' →L[ℝ] F}
    (hweak : ∀ k, HasWeakFDerivOn μ W (f k ∘ Φ) fun x => (G k (Φ x)).comp (fderiv ℝ Φ x))
    (hg : IntegrableOn (g ∘ Φ) W μ) (hH : IntegrableOn (H ∘ Φ) W μ)
    (hfm : ∀ k, AEStronglyMeasurable (fun y => f k y - g y) ν)
    (hGm : ∀ k, AEStronglyMeasurable (fun y => G k y - H y) ν)
    (hf : Tendsto (fun k => ∫⁻ y, ‖f k y - g y‖ₑ ∂ν) atTop (𝓝 0))
    (hG : Tendsto (fun k => ∫⁻ y, ‖G k y - H y‖ₑ ∂ν) atTop (𝓝 0)) :
    HasWeakFDerivOn μ W (g ∘ Φ) fun x => (H (Φ x)).comp (fderiv ℝ Φ x) := by
  have hW := W.isOpen.measurableSet
  have hcomp : ∀ x ∈ (W : Set E), ∀ A : E' →L[ℝ] F,
      ‖A.comp (fderiv ℝ Φ x)‖ ≤ ‖A‖ * M := fun x hx A =>
    (A.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hM x hx) (norm_nonneg _))
  have hcand : IntegrableOn (fun x => (H (Φ x)).comp (fderiv ℝ Φ x)) W μ :=
    Integrable.mono' (hH.norm.mul_const M)
      ((ContinuousLinearMap.compL ℝ E E' F).aestronglyMeasurable_comp₂ hH.1
        (measurable_fderiv ℝ Φ).aestronglyMeasurable)
      ((ae_restrict_iff' hW).2 (Eventually.of_forall fun x hx => hcomp x hx _))
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop) hg.locallyIntegrableOn
    (fun v => IntegrableOn.locallyIntegrableOn
      ((ContinuousLinearMap.apply ℝ F v).integrable_comp hcand))
    hweak ?_ ?_
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
      (fun _ => bot_le) fun k => setLIntegral_comp_le hΦ W (hfm k).enorm
  · have hGM := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal M) hG
      (Or.inr ENNReal.ofReal_ne_top)
    rw [zero_mul] at hGM
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGM
      (fun _ => bot_le) fun k => ?_
    calc ∫⁻ x in W, ‖(G k (Φ x)).comp (fderiv ℝ Φ x) - (H (Φ x)).comp (fderiv ℝ Φ x)‖ₑ ∂μ
        ≤ ∫⁻ x in W, ‖G k (Φ x) - H (Φ x)‖ₑ * ENNReal.ofReal M ∂μ := by
          refine setLIntegral_mono' hW fun x hx => ?_
          rw [← ContinuousLinearMap.sub_comp, ← ofReal_norm, ← ofReal_norm,
            ← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hcomp x hx _)
      _ = (∫⁻ x in W, ‖G k (Φ x) - H (Φ x)‖ₑ ∂μ) * ENNReal.ofReal M :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul_left (setLIntegral_comp_le hΦ W (hGm k).enorm) _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] [BorelSpace E'] [ν.IsAddHaarMeasure] in
/-- Mollification by normalized bumps of shrinking radius converges in `L¹`, stated for the
convolution order `g ⋆ ρ` of the interior mollification lemmas. -/
private theorem tendsto_lintegral_convolution_normed_sub [BorelSpace E'] [ν.IsAddHaarMeasure]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {g : E' → G}
    (hg : MemLp g 1 ν) {φ : ℕ → ContDiffBump (0 : E')}
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ y,
      ‖(g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, ν] (φ k).normed ν) y - g y‖ₑ ∂ν) atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hφ hg) (fun _ => bot_le)
    fun k => ?_
  rw [convolution_flip]
  exact lintegral_enorm_le_eLpNorm_one

/-- **The weak chain rule.** If `u` has weak derivative `D` on the open set `V`, and `Φ` is a
measure-preserving map, locally Lipschitz on the open set `U` and mapping `U` into `V`, then
`u ∘ Φ` has weak derivative `x ↦ D (Φ x) ∘L fderiv ℝ Φ x` on `U`. -/
theorem HasWeakFDerivOn.comp_measurePreserving {U : Opens E} {V : Opens E'} {u : E' → F}
    {D : E' → E' →L[ℝ] F} {Φ : E → E'} (h : HasWeakFDerivOn ν V u D)
    (hΦ : MeasurePreserving Φ μ ν) (hΦl : LocallyLipschitzOn U Φ)
    (hUV : MapsTo Φ U V) :
    HasWeakFDerivOn μ U (u ∘ Φ) fun x => (D (Φ x)).comp (fderiv ℝ Φ x) := by
  have : CompleteSpace F := h.completeSpace
  rw [hasWeakFDerivOn_iff_forall_isCompact_closure]
  intro W hWc hWU
  have hWU' : (W : Set E) ⊆ U := subset_closure.trans hWU
  -- `Φ` is Lipschitz on the compact `closure W`, so its derivative is bounded on `W`.
  obtain ⟨C, hC⟩ := (hΦl.mono hWU).exists_lipschitzOnWith_of_compact hWc
  have hCW : LipschitzOnWith C Φ W := hC.mono subset_closure
  -- The compact image `K` of `closure W` has an open thickening `O` with closure inside `V`.
  set K := Φ '' closure (W : Set E)
  have hK : IsCompact K := hWc.image_of_continuousOn hC.continuousOn
  have hKV : K ⊆ V := image_subset_iff.2 fun x hx => hUV (hWU hx)
  have hWK : ∀ x ∈ (W : Set E), Φ x ∈ K := fun x hx => mem_image_of_mem Φ (subset_closure hx)
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open V.isOpen hKV
  obtain ⟨O, hO⟩ : ∃ O : Opens E', (O : Set E') = thickening δ K := ⟨⟨_, isOpen_thickening⟩, rfl⟩
  have hOV : (O : Set E') ⊆ cthickening δ K := hO ▸ thickening_subset_cthickening δ K
  have hKO : K ⊆ O := hO ▸ self_subset_thickening hδ K
  have hu : MemLp u 1 (ν.restrict O) := memLp_one_iff_integrable.2 <|
    (h.locallyIntegrableOn.integrableOn_compact_subset hδV hK.cthickening).mono_set hOV
  have hD : MemLp D 1 (ν.restrict O) := memLp_one_iff_integrable.2 <|
    (h.locallyIntegrableOn_deriv.integrableOn_compact_subset hδV hK.cthickening).mono_set hOV
  have hu' : MemLp ((O : Set E').indicator u) 1 ν :=
    (memLp_indicator_iff_restrict (f := u) O.isOpen.measurableSet.nullMeasurableSet).2 hu
  have hD' : MemLp ((O : Set E').indicator D) 1 ν :=
    (memLp_indicator_iff_restrict (f := D) O.isOpen.measurableSet.nullMeasurableSet).2 hD
  have hOc : HasCompactSupport ((O : Set E').indicator u) :=
    HasCompactSupport.intro' hK.cthickening isClosed_cthickening fun y hy =>
      indicator_of_notMem (fun hyO => hy (hOV hyO)) u
  -- Mollify the zero extensions from `O` by bumps whose radii stay below `δ`.
  let φ : ℕ → ContDiffBump (0 : E') := fun k =>
    ⟨δ / (k + 2) / 2, δ / (k + 2), by positivity, half_lt_self (by positivity)⟩
  have hφδ : ∀ k, (φ k).rOut < δ := fun k =>
    div_lt_self hδ (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  let f : ℕ → E' → F := fun k =>
    ((O : Set E').indicator u) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, ν] (φ k).normed ν
  let G : ℕ → E' → E' →L[ℝ] F := fun k =>
    ((O : Set E').indicator D) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, ν] (φ k).normed ν
  -- The mollified `u` is smooth with compact support, hence Lipschitz.
  have hfl : ∀ k, ∃ L, LipschitzWith L (f k) := fun k =>
    ((φ k).hasCompactSupport_normed.contDiff_convolution_right _
      (hu'.locallyIntegrable le_rfl) ((φ k).contDiff_normed (n := 1))
      ).lipschitzWith_of_hasCompactSupport
      (hOc.convolution _ (φ k).hasCompactSupport_normed) one_ne_zero
  -- Near `K` the mollified `u` has the mollified `D` as derivative; compose with `Φ` on `W`
  -- wherever `Φ` is differentiable, which is almost everywhere by Rademacher's theorem.
  have hfd : ∀ k, ∀ᵐ x ∂μ, x ∈ (W : Set E) →
      HasFDerivAt (f k ∘ Φ) ((G k (Φ x)).comp (fderiv ℝ Φ x)) x := fun k => by
    filter_upwards [(hΦl.mono hWU').ae_differentiableAt_of_mem (μ := μ) W.isOpen] with x hdx hx
    exact ((h.mono (hOV.trans hδV)).hasFDerivAt_indicator_convolution_normed hu hD le_rfl le_rfl
      (φ k) (Φ x) ((closedBall_subset_ball (hφδ k)).trans
        (hO ▸ ball_subset_thickening (hWK x hx) δ))).comp x (hdx hx).hasFDerivAt
  have hweak : ∀ k, HasWeakFDerivOn μ W (f k ∘ Φ)
      fun x => (G k (Φ x)).comp (fderiv ℝ Φ x) := fun k => by
    obtain ⟨L, hL⟩ := hfl k
    have hl : LocallyLipschitzOn W (f k ∘ Φ) := fun _ _ =>
      ⟨_, _, self_mem_nhdsWithin, hL.comp_lipschitzOnWith hCW⟩
    exact hl.hasWeakFDerivOn (hfd k)
  have hfc : ∀ k, Continuous (f k) := fun k => (hfl k).elim fun _ hL => hL.continuous
  have hGc : ∀ k, Continuous (G k) := fun k =>
    (φ k).hasCompactSupport_normed.continuous_convolution_right _
      (hD'.locallyIntegrable le_rfl) (φ k).continuous_normed
  -- On `W`, the zero extensions from `O` agree with `u` and `D` after composing with `Φ`.
  have hindu : (O : Set E').indicator u ∘ Φ =ᵐ[μ.restrict W] u ∘ Φ :=
    (ae_restrict_iff' W.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx =>
      indicator_of_mem (hKO (hWK x hx)) u
  have hindD : (O : Set E').indicator D ∘ Φ =ᵐ[μ.restrict W] D ∘ Φ :=
    (ae_restrict_iff' W.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx =>
      indicator_of_mem (hKO (hWK x hx)) D
  refine (hasWeakFDerivOn_comp_of_tendsto hΦ
    (fun x hx => norm_fderiv_le_of_lipschitzOn ℝ (W.isOpen.mem_nhds hx) hCW) hweak
    (hΦ.integrable_comp_of_integrable (memLp_one_iff_integrable.1 hu')).integrableOn
    (hΦ.integrable_comp_of_integrable (memLp_one_iff_integrable.1 hD')).integrableOn
    (fun k => (hfc k).aestronglyMeasurable.sub hu'.aestronglyMeasurable)
    (fun k => (hGc k).aestronglyMeasurable.sub hD'.aestronglyMeasurable)
    (tendsto_lintegral_convolution_normed_sub hu' hφ)
    (tendsto_lintegral_convolution_normed_sub hD' hφ)).congr_ae hindu |>.congr_ae_deriv ?_
  filter_upwards [hindD] with x hx
  simp only [Function.comp_apply] at hx
  rw [hx]

end TauCeti
