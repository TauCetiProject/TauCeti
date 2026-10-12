/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Local
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The weak chain rule for measure-preserving `C¹` changes of variables

Let `Φ : E → E` be a measure-preserving measurable embedding of a finite-dimensional real normed
space, of class `C¹` on an open set `U`, with `Φ '' U ⊆ V` for an open set `V`. If `u` has weak
derivative `D` on `V`, then `u ∘ Φ` has weak derivative

`x ↦ D (Φ x) ∘L fderiv ℝ Φ x`

on `U`: the classical chain rule survives the passage to weak derivatives. No bound on the
derivative of `Φ` and no integrability of `u` beyond local integrability is needed, because weak
derivatives are detected on relatively compact subdomains.

The typical change of variables of this kind is a shear `(t, y) ↦ (t + φ y, y)` of a product,
which flattens the region above the graph of a `C¹` function `φ` onto a half-space; it is
measure-preserving by Fubini's theorem.

## The argument

Fix an open `W` whose closure is compact and contained in `U`. The image `K = Φ '' closure W` is
compact in `V`, so some open thickening `O` of `K` still lies in `V`, and `u`, `D` are integrable
on `O`. Mollify the zero extensions of `u` and `D` from `O` by normalized bumps of radius less
than the thickening. Near `K` the derivative of the mollified `u` is the mollified `D`
(`TauCeti.HasWeakFDerivOn.hasFDerivAt_indicator_convolution_normed`), so the classical chain rule
gives the derivative of the mollified `u` composed with `Φ` on `W`. Since `Φ` is
measure-preserving, the `L¹(W)` distances to `u ∘ Φ` and to the candidate derivative are bounded
by the `L¹` distances of the mollifications to the zero extensions, the latter multiplied by a
bound for `fderiv ℝ Φ` on `closure W`, and these tend to zero
(`TauCeti.tendsto_eLpNorm_normed_convolution_sub`). Weak derivatives pass to such limits
(`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub`).

## Main declarations

* `TauCeti.HasWeakFDerivOn.locallyIntegrableOn_deriv`: in finite dimension, a weak derivative is
  locally integrable as an operator-valued function.
* `TauCeti.HasWeakFDerivOn.comp_measurePreserving`: the weak chain rule.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.3 (smooth approximation).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal Topology Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}

/-- In finite dimension, a weak derivative `U` of `u` on `Ω` is locally integrable on `Ω` as an
operator-valued function: it is a finite sum of its values on a basis, each locally integrable by
definition. -/
theorem HasWeakFDerivOn.locallyIntegrableOn_deriv {Ω : Opens E} {u : E → F}
    {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) : LocallyIntegrableOn U Ω μ := by
  obtain ⟨n, b, -⟩ : ∃ n, ∃ b : Module.Basis (Fin n) ℝ E, True :=
    ⟨_, Module.finBasis ℝ E, trivial⟩
  -- The `i`-th term `x ↦ (b.coord i).smulRight (U x (b i))` of the expansion of `U` in `b`.
  let g : Fin n → E → E →L[ℝ] F := fun i x =>
    ContinuousLinearMap.smulRightL ℝ E F (LinearMap.toContinuousLinearMap (b.coord i)) (U x (b i))
  have hU : U = fun x => ∑ i, g i x := by
    funext x
    ext v
    calc U x v = U x (∑ i, b.repr v i • b i) := by rw [b.sum_repr]
      _ = _ := by rw [map_sum]; simp [g]
  have hg : ∀ i, LocallyIntegrableOn (g i) Ω μ := fun i =>
    (ContinuousLinearMap.smulRightL ℝ E F _).locallyIntegrableOn_comp
      (h.hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv
  have hsum : LocallyIntegrableOn (fun x => ∑ i, g i x) Ω μ :=
    (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 fun k hk hkc =>
      integrable_finsetSum (f := g) _ fun i _ => (hg i).integrableOn_compact_subset hk hkc
  rwa [hU]

variable [BorelSpace E] [μ.IsAddHaarMeasure]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- Precomposition with a measure-preserving measurable embedding does not increase the lower
integral over a set. -/
private theorem setLIntegral_comp_le {Φ : E → E} (hΦ : MeasurePreserving Φ μ μ)
    (hΦe : MeasurableEmbedding Φ) (W : Set E) (g : E → ℝ≥0∞) :
    ∫⁻ x in W, g (Φ x) ∂μ ≤ ∫⁻ y, g y ∂μ :=
  (setLIntegral_le_lintegral _ _).trans_eq (hΦ.lintegral_comp_emb hΦe g)

omit [μ.IsAddHaarMeasure] in
/-- **Passing the chain rule to the limit.** Let `Φ` be measure-preserving, with
`‖fderiv ℝ Φ‖ ≤ M` on `W`. If each `f k ∘ Φ` has weak derivative `x ↦ G k (Φ x) ∘L fderiv ℝ Φ x`
on `W`, and `f k → g`, `G k → H` in `L¹`, with `g ∘ Φ` and `H ∘ Φ` integrable on `W`, then
`g ∘ Φ` has weak derivative `x ↦ H (Φ x) ∘L fderiv ℝ Φ x` on `W`. -/
private theorem hasWeakFDerivOn_comp_of_tendsto {W : Opens E} {Φ : E → E}
    (hΦ : MeasurePreserving Φ μ μ) (hΦe : MeasurableEmbedding Φ) {M : ℝ}
    (hM : ∀ x ∈ (W : Set E), ‖fderiv ℝ Φ x‖ ≤ M) (hΦc : ContinuousOn (fderiv ℝ Φ) W)
    {f : ℕ → E → F} {G : ℕ → E → E →L[ℝ] F} {g : E → F} {H : E → E →L[ℝ] F}
    (hweak : ∀ k, HasWeakFDerivOn μ W (f k ∘ Φ) fun x => (G k (Φ x)).comp (fderiv ℝ Φ x))
    (hg : IntegrableOn (g ∘ Φ) W μ) (hH : IntegrableOn (H ∘ Φ) W μ)
    (hf : Tendsto (fun k => ∫⁻ y, ‖f k y - g y‖ₑ ∂μ) atTop (𝓝 0))
    (hG : Tendsto (fun k => ∫⁻ y, ‖G k y - H y‖ₑ ∂μ) atTop (𝓝 0)) :
    HasWeakFDerivOn μ W (g ∘ Φ) fun x => (H (Φ x)).comp (fderiv ℝ Φ x) := by
  have hW := W.isOpen.measurableSet
  have hcomp : ∀ x ∈ (W : Set E), ∀ A : E →L[ℝ] F,
      ‖A.comp (fderiv ℝ Φ x)‖ ≤ ‖A‖ * M := fun x hx A =>
    (A.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hM x hx) (norm_nonneg _))
  have hcand : IntegrableOn (fun x => (H (Φ x)).comp (fderiv ℝ Φ x)) W μ :=
    Integrable.mono' (hH.norm.mul_const M)
      ((ContinuousLinearMap.compL ℝ E E F).aestronglyMeasurable_comp₂ hH.1
        (hΦc.aestronglyMeasurable hW))
      ((ae_restrict_iff' hW).2 (Eventually.of_forall fun x hx => hcomp x hx _))
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop) hg.locallyIntegrableOn
    (fun v => IntegrableOn.locallyIntegrableOn
      ((ContinuousLinearMap.apply ℝ F v).integrable_comp hcand))
    hweak ?_ ?_
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
      (fun _ => bot_le) fun k => setLIntegral_comp_le hΦ hΦe W fun y => ‖f k y - g y‖ₑ
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
      _ ≤ _ := mul_le_mul_left (setLIntegral_comp_le hΦ hΦe W fun y => ‖G k y - H y‖ₑ) _

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Mollification by normalized bumps of shrinking radius converges in `L¹`, stated for the
convolution order `g ⋆ ρ` of the interior mollification lemmas. -/
private theorem tendsto_lintegral_convolution_normed_sub [BorelSpace E] [μ.IsAddHaarMeasure]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {g : E → G}
    (hg : MemLp g 1 μ) {φ : ℕ → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ y,
      ‖(g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] (φ k).normed μ) y - g y‖ₑ ∂μ) atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hφ hg) (fun _ => bot_le)
    fun k => ?_
  rw [convolution_flip]
  exact lintegral_enorm_le_eLpNorm_one

/-- **The weak chain rule.** If `u` has weak derivative `D` on the open set `V`, and `Φ` is a
measure-preserving measurable embedding, of class `C¹` on the open set `U` and mapping `U` into
`V`, then `u ∘ Φ` has weak derivative `x ↦ D (Φ x) ∘L fderiv ℝ Φ x` on `U`. -/
theorem HasWeakFDerivOn.comp_measurePreserving {U V : Opens E} {u : E → F}
    {D : E → E →L[ℝ] F} {Φ : E → E} (h : HasWeakFDerivOn μ V u D)
    (hΦ : MeasurePreserving Φ μ μ) (hΦe : MeasurableEmbedding Φ) (hΦd : ContDiffOn ℝ 1 Φ U)
    (hUV : MapsTo Φ U V) :
    HasWeakFDerivOn μ U (u ∘ Φ) fun x => (D (Φ x)).comp (fderiv ℝ Φ x) := by
  have : CompleteSpace F := h.completeSpace
  have hΦc : ContinuousOn (fderiv ℝ Φ) U := hΦd.continuousOn_fderiv_of_isOpen U.isOpen le_rfl
  rw [hasWeakFDerivOn_iff_forall_isCompact_closure]
  intro W hWc hWU
  have hWU' : (W : Set E) ⊆ U := subset_closure.trans hWU
  -- The compact image `K` of `closure W` has an open thickening `O` with closure inside `V`.
  set K := Φ '' closure (W : Set E)
  have hK : IsCompact K := hWc.image_of_continuousOn (hΦd.continuousOn.mono hWU)
  have hKV : K ⊆ V := image_subset_iff.2 fun x hx => hUV (hWU hx)
  have hWK : ∀ x ∈ (W : Set E), Φ x ∈ K := fun x hx => mem_image_of_mem Φ (subset_closure hx)
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open V.isOpen hKV
  obtain ⟨O, hO⟩ : ∃ O : Opens E, (O : Set E) = thickening δ K := ⟨⟨_, isOpen_thickening⟩, rfl⟩
  have hOV : (O : Set E) ⊆ cthickening δ K := hO ▸ thickening_subset_cthickening δ K
  have hKO : K ⊆ O := hO ▸ self_subset_thickening hδ K
  have hu : MemLp u 1 (μ.restrict O) := memLp_one_iff_integrable.2 <|
    (h.locallyIntegrableOn.integrableOn_compact_subset hδV hK.cthickening).mono_set hOV
  have hD : MemLp D 1 (μ.restrict O) := memLp_one_iff_integrable.2 <|
    (h.locallyIntegrableOn_deriv.integrableOn_compact_subset hδV hK.cthickening).mono_set hOV
  have hu' : MemLp ((O : Set E).indicator u) 1 μ :=
    (memLp_indicator_iff_restrict (f := u) O.isOpen.measurableSet.nullMeasurableSet).2 hu
  have hD' : MemLp ((O : Set E).indicator D) 1 μ :=
    (memLp_indicator_iff_restrict (f := D) O.isOpen.measurableSet.nullMeasurableSet).2 hD
  -- Mollify the zero extensions from `O` by bumps whose radii stay below `δ`.
  let φ : ℕ → ContDiffBump (0 : E) := fun k =>
    ⟨δ / (k + 2) / 2, δ / (k + 2), by positivity, half_lt_self (by positivity)⟩
  have hφδ : ∀ k, (φ k).rOut < δ := fun k =>
    div_lt_self hδ (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  let f : ℕ → E → F := fun k =>
    ((O : Set E).indicator u) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] (φ k).normed μ
  let G : ℕ → E → E →L[ℝ] F := fun k =>
    ((O : Set E).indicator D) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, μ] (φ k).normed μ
  -- Near `K` the mollified `u` has the mollified `D` as derivative; compose with `Φ` on `W`.
  have hΦx : ∀ x ∈ (W : Set E), HasFDerivAt Φ (fderiv ℝ Φ x) x := fun x hx =>
    ((hΦd.differentiableOn one_ne_zero x (hWU' hx)).differentiableAt
      (U.isOpen.mem_nhds (hWU' hx))).hasFDerivAt
  have hfd : ∀ k, ∀ x ∈ (W : Set E),
      HasFDerivAt (f k ∘ Φ) ((G k (Φ x)).comp (fderiv ℝ Φ x)) x := fun k x hx =>
    ((h.mono (hOV.trans hδV)).hasFDerivAt_indicator_convolution_normed hu hD le_rfl le_rfl (φ k)
      (Φ x) ((closedBall_subset_ball (hφδ k)).trans
        (hO ▸ ball_subset_thickening (hWK x hx) δ))).comp x (hΦx x hx)
  have hΦW : ContinuousOn Φ W := hΦd.continuousOn.mono hWU'
  have hweak : ∀ k, HasWeakFDerivOn μ W (f k ∘ Φ)
      fun x => (G k (Φ x)).comp (fderiv ℝ Φ x) := fun k => hasWeakFDerivOn_iff.2 fun v =>
    hasWeakLineDerivOn_of_hasLineDerivAt
      ((((φ k).hasCompactSupport_normed.continuous_convolution_right _
        (hu'.locallyIntegrable le_rfl) (φ k).continuous_normed).comp_continuousOn hΦW
        ).locallyIntegrableOn W.isOpen.measurableSet)
      (((((φ k).hasCompactSupport_normed.continuous_convolution_right _
        (hD'.locallyIntegrable le_rfl) (φ k).continuous_normed).comp_continuousOn hΦW).clm_comp
        (hΦc.mono hWU')).clm_apply continuousOn_const
        |>.locallyIntegrableOn W.isOpen.measurableSet)
      fun x hx => (hfd k x hx).hasLineDerivAt v
  -- On `W`, the zero extensions from `O` agree with `u` and `D` after composing with `Φ`.
  have hindu : (O : Set E).indicator u ∘ Φ =ᵐ[μ.restrict W] u ∘ Φ :=
    (ae_restrict_iff' W.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx =>
      indicator_of_mem (hKO (hWK x hx)) u
  have hindD : (O : Set E).indicator D ∘ Φ =ᵐ[μ.restrict W] D ∘ Φ :=
    (ae_restrict_iff' W.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx =>
      indicator_of_mem (hKO (hWK x hx)) D
  have hpre : (W : Set E) ⊆ Φ ⁻¹' O := fun x hx => hKO (hWK x hx)
  obtain ⟨M, hM⟩ := hWc.exists_bound_of_continuousOn (hΦc.mono hWU)
  refine (hasWeakFDerivOn_comp_of_tendsto hΦ hΦe (fun x hx => hM x (subset_closure hx))
    (hΦc.mono hWU') hweak
    (((hΦ.integrableOn_comp_preimage hΦe).2
      (memLp_one_iff_integrable.1 hu').integrableOn).mono_set hpre)
    (((hΦ.integrableOn_comp_preimage hΦe).2
      (memLp_one_iff_integrable.1 hD').integrableOn).mono_set hpre)
    (tendsto_lintegral_convolution_normed_sub hu' hφ)
    (tendsto_lintegral_convolution_normed_sub hD' hφ)).congr_ae hindu |>.congr_ae_deriv ?_
  filter_upwards [hindD] with x hx
  simp only [Function.comp_apply] at hx
  rw [hx]

end TauCeti
