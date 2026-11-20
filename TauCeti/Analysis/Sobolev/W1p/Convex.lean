/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
public import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Convex.Topology
import TauCeti.Topology.MetricSpace.Holder

/-!
# Sharp Lipschitz representatives on convex domains

The precise representative of a real `W^{1,∞}` function on an open set is Lipschitz on
each convex subset, with constant at most the essential supremum of its weak gradient.
In particular the whole-space representative has this bound. Neither boundedness of the
domain nor boundary regularity is needed.

Local continuity comes from the interior Morrey theorem. Mollification on a neighborhood of
each segment gives the sharp constant, without assuming that smooth functions are dense in
the `W^{1,∞}` norm.

A `W^{1,p}` function of any exponent whose value is essentially bounded on an open convex subset
`V` of its domain, with weak gradient essentially bounded by `M` there, restricts to a `W^{1,∞}`
class on `V`, so its precise representative is `M`-Lipschitz on `V`
(`TauCeti.W1p.lipschitzOnWith_preciseRepresentative_of_ae_norm_gradient_le`). This is how a weak
solution of an elliptic equation whose gradient is known to be locally bounded, for instance
Hölder continuous, is shown to be locally Lipschitz. If the precise representatives of the value
and of the gradient are bounded on the `ρ`-thickening of a set `S`, the precise representative of
the value is therefore Hölder on the `ρ / 2`-thickening with every exponent at most one
(`TauCeti.W1p.exists_holderOnWith_preciseRepresentative_of_forall_norm_le`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Metric Filter TauCeti.MeasureTheory
open scoped Topology Convolution ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

private theorem W1p.memLp_indicator_preciseRepresentative (u : W1p μ Ω ∞) :
    MemLp ((Ω : Set E).indicator (preciseRepresentative μ (W1p.value u))) ∞ μ := by
  apply (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2
  exact (Lp.memLp (W1p.value u)).ae_eq (W1p.ae_eq_preciseRepresentative u)

private theorem W1p.norm_fderiv_convolution_indicator_le (u : W1p μ Ω ∞)
    (ρ : ContDiffBump (0 : E)) {z : E}
    (hz : ∀ y ∈ tsupport (ρ.normed μ), z - y ∈ Ω) :
    ‖fderiv ℝ (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
      ((Ω : Set E).indicator (preciseRepresentative μ (W1p.value u)))) z‖ ≤
        ‖W1p.gradient u‖ := by
  let f := (Ω : Set E).indicator (preciseRepresentative μ (W1p.value u))
  let G := (Ω : Set E).indicator (fun x ↦ innerSL ℝ (W1p.gradient u x))
  have hf := W1p.memLp_indicator_preciseRepresentative u
  have hG₀ : MemLp (fun x ↦ innerSL ℝ (W1p.gradient u x)) ∞ (μ.restrict Ω) :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp_memLp' (Lp.memLp (W1p.gradient u))
  have hG : MemLp G ∞ μ := by
    exact (memLp_indicator_iff_restrict (f := fun x ↦ innerSL ℝ (W1p.gradient u x))
      Ω.isOpen.measurableSet.nullMeasurableSet).2 hG₀
  have hweak : HasWeakFDerivOn μ Ω f G := by
    exact ((W1p.hasWeakFDerivOn u).congr_ae (W1p.ae_eq_preciseRepresentative u)).indicator
  have hbound : ∀ᵐ x ∂μ, ‖G x‖ ≤ ‖W1p.gradient u‖ := by
    have h := (ae_restrict_iff' Ω.isOpen.measurableSet).1
      (Lp.ae_norm_le_norm_top (W1p.gradient u))
    filter_upwards [h] with x hx
    by_cases hxΩ : x ∈ Ω
    · simpa [G, hxΩ] using hx hxΩ
    · simp [G, hxΩ]
  rw [← convolution_flip, hweak.fderiv_convolution_right (hf.locallyIntegrable le_top)
    (hG.locallyIntegrable le_top) _ ρ.contDiff_normed ρ.hasCompactSupport_normed z hz,
    convolution_flip, convolution_def]
  calc
    ‖∫ y, ContinuousLinearMap.lsmul ℝ ℝ (ρ.normed μ y) (G (z - y)) ∂μ‖ ≤
        ∫ y, ρ.normed μ y * ‖W1p.gradient u‖ ∂μ := by
      apply norm_integral_le_of_norm_le (ρ.integrable_normed.mul_const _)
      filter_upwards [((μ.measurePreserving_sub_left z).quasiMeasurePreserving.ae hbound)]
        with y hy
      simpa only [ContinuousLinearMap.lsmul_apply, norm_smul,
        Real.norm_of_nonneg (ρ.nonneg_normed y)] using
          mul_le_mul_of_nonneg_left hy (ρ.nonneg_normed y)
    _ = ‖W1p.gradient u‖ := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-- On any convex subset of its open domain the precise representative of a `W^{1,∞}`
class is Lipschitz, with the sharp bound given by the essential supremum of its weak gradient. -/
theorem W1p.lipschitzOnWith_preciseRepresentative_of_convex (u : W1p μ Ω ∞)
    {s : Set E} (hs : Convex ℝ s) (hsΩ : s ⊆ Ω) :
    LipschitzOnWith ‖W1p.gradient u‖₊ (preciseRepresentative μ (W1p.value u)) s := by
  let f := (Ω : Set E).indicator (preciseRepresentative μ (W1p.value u))
  have hf := W1p.memLp_indicator_preciseRepresentative u
  have hc := W1p.continuousOn_preciseRepresentative (ENNReal.natCast_lt_top _) u
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_segment ℝ x y).exists_cthickening_subset_open Ω.isOpen
    ((hs.segment_subset hx hy).trans hsΩ)
  let ρ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking hδ
  have hsupp (n : ℕ) (z : E) (hz : z ∈ segment ℝ x y)
      (w : E) (hw : w ∈ tsupport ((ρ n).normed μ)) : z - w ∈ Ω := by
    apply hδΩ
    apply mem_cthickening_of_dist_le _ z δ _ hz
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    rw [(ρ n).tsupport_normed_eq, mem_closedBall, dist_zero_right] at hw
    simp only [ρ, ContDiffBump.rOut_shrinking] at hw
    exact hw.trans (div_le_self hδ.le (by simp))
  have hlim (z : E) (hz : z ∈ Ω) :
      Tendsto (fun n ↦ ((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) z)
        atTop (𝓝 (preciseRepresentative μ (W1p.value u) z)) := by
    have hcont : ContinuousAt f z := by
      exact (hc.continuousAt (Ω.isOpen.mem_nhds hz)).congr
        (Filter.EventuallyEq.symm (Ω.isOpen.eventually_mem hz |>.mono fun t ht ↦
          indicator_of_mem ht _))
    simpa only [f, indicator_of_mem hz] using
      ContDiffBump.convolution_tendsto_right (ContDiffBump.tendsto_rOut_shrinking hδ)
        (Eventually.of_forall fun _ ↦ hf.aestronglyMeasurable)
        (hcont.tendsto.comp tendsto_snd) (tendsto_const_nhds (x := z))
  have hle (n : ℕ) :
      dist (((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x)
        (((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) y) ≤
          ‖W1p.gradient u‖ * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    apply (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intro z _
      exact ((ρ n).hasCompactSupport_normed.contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n).contDiff_normed
        (hf.locallyIntegrable le_top) (n := ⊤)).differentiable (by simp) z
    · intro z hz
      exact W1p.norm_fderiv_convolution_indicator_le u (ρ n) (hsupp n z hz)
    · exact right_mem_segment ℝ x y
    · exact left_mem_segment ℝ x y
  exact le_of_tendsto ((hlim x (hsΩ hx)).dist (hlim y (hsΩ hy)))
    (Eventually.of_forall hle)

/-- On the whole space the precise representative of a `W^{1,∞}` class is globally
Lipschitz with constant at most the essential supremum of its weak gradient. -/
theorem W1p.lipschitzWith_preciseRepresentative (u : W1p μ ⊤ ∞) :
    LipschitzWith ‖W1p.gradient u‖₊ (preciseRepresentative μ (W1p.value u)) := by
  rw [← lipschitzOnWith_univ]
  exact W1p.lipschitzOnWith_preciseRepresentative_of_convex u convex_univ subset_rfl

/-- A Sobolev function whose value is essentially bounded on an open convex subset `V` of its
domain, and whose weak gradient is essentially bounded by `M` there, has a precise representative
that is `M`-Lipschitz on `V`. The exponent `p` of the Sobolev space is arbitrary. -/
theorem W1p.lipschitzOnWith_preciseRepresentative_of_ae_norm_gradient_le {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1p μ Ω p) {V : Opens E} (hV : V ≤ Ω) (hVc : Convex ℝ (V : Set E))
    (hval : MemLp (W1p.value u) ∞ (μ.restrict V)) {M : NNReal}
    (hM : ∀ᵐ x ∂μ.restrict V, ‖W1p.gradient u x‖ ≤ M) :
    LipschitzOnWith M (preciseRepresentative μ (W1p.value u)) V := by
  -- The restriction of `u` to `V` is a `W^{1,∞}(V)` class.
  have hv : MemLp (W1p.value (W1p.restrictL hV u)) ∞ (μ.restrict V) :=
    hval.ae_eq (W1p.value_restrictL_ae hV u).symm
  have hgM : ∀ᵐ x ∂μ.restrict V, ‖W1p.gradient (W1p.restrictL hV u) x‖ ≤ M := by
    filter_upwards [W1p.gradient_restrictL_ae hV u, hM] with x hx hxM
    rwa [hx]
  have hg : MemLp (W1p.gradient (W1p.restrictL hV u)) ∞ (μ.restrict V) :=
    memLp_top_of_bound (Lp.aestronglyMeasurable _) M hgM
  let w : W1p μ V ∞ := W1p.mk (hv.toLp _) (hg.toLp _)
    (((W1p.hasWeakFDerivOn (W1p.restrictL hV u)).congr_ae hv.coeFn_toLp.symm).congr_ae_deriv
      (hg.coeFn_toLp.symm.mono fun x hx => congrArg (fun v => innerSL ℝ v) hx))
  have hw : ‖W1p.gradient w‖₊ ≤ M := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, W1p.gradient_mk, Lp.norm_toLp,
      eLpNorm_exponent_top]
    · exact ENNReal.toReal_le_of_le_ofReal M.coe_nonneg (eLpNormEssSup_le_of_ae_bound hgM)
    · exact Lp.aestronglyMeasurable _
  -- On `V` the precise representatives of `w` and `u` agree.
  have heq : ∀ x ∈ (V : Set E), preciseRepresentative μ (W1p.value w) x =
      preciseRepresentative μ (W1p.value u) x := fun x hx => by
    refine preciseRepresentative_congr_ae_nhds (V.isOpen.mem_nhds hx) ?_
    rw [W1p.value_mk]
    exact hv.coeFn_toLp.trans (W1p.value_restrictL_ae hV u)
  have hL := (W1p.lipschitzOnWith_preciseRepresentative_of_convex w hVc le_rfl).weaken hw
  intro x hx y hy
  rw [← heq x hx, ← heq y hy]
  exact hL hx hy

/-- A Sobolev function whose precise representative and the precise representative of whose
gradient are bounded on the `ρ`-thickening of a set `S` inside its domain has a precise
representative that is Lipschitz on the balls of radius `ρ / 2` about the points of the
`ρ / 2`-thickening, hence Hölder on the `ρ / 2`-thickening with every exponent at most one. -/
theorem W1p.exists_holderOnWith_preciseRepresentative_of_forall_norm_le {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1p μ Ω p) {S : Set E} {ρ : ℝ} (hρ : 0 < ρ)
    (hρS : thickening ρ S ⊆ Ω) {M₁ M₂ : ℝ}
    (hv : ∀ x ∈ thickening ρ S, ‖preciseRepresentative μ (W1p.value u) x‖ ≤ M₁)
    (hg : ∀ x ∈ thickening ρ S, ‖preciseRepresentative μ (W1p.gradient u) x‖ ≤ M₂)
    {γ : NNReal} (hγ : γ ≤ 1) :
    ∃ C : NNReal,
      HolderOnWith C γ (preciseRepresentative μ (W1p.value u)) (thickening (ρ / 2) S) := by
  have hval : (W1p.value u : E → ℝ) =ᵐ[μ.restrict Ω] preciseRepresentative μ (W1p.value u) :=
    W1p.ae_eq_preciseRepresentative u
  have hgrad : (W1p.gradient u : E → E) =ᵐ[μ.restrict Ω]
      preciseRepresentative μ (W1p.gradient u) :=
    ae_eq_restrict_preciseRepresentative Ω.isOpen
      (W1p.hasWeakFDerivOn u).locallyIntegrableOn_gradient
  have hball : ∀ x ∈ thickening (ρ / 2) S, ball x (ρ / 2) ⊆ thickening ρ S := fun x hx =>
    (ball_subset_thickening hx _).trans
      ((thickening_thickening_subset _ _ _).trans (by rw [add_halves]))
  -- On each such ball, the value and the gradient of `u` are essentially bounded.
  have hlip : ∀ x ∈ thickening (ρ / 2) S,
      LipschitzOnWith M₂.toNNReal (preciseRepresentative μ (W1p.value u)) (ball x (ρ / 2)) := by
    intro x hx
    let V : Opens E := ⟨ball x (ρ / 2), isOpen_ball⟩
    have hVU : (V : Set E) ⊆ thickening ρ S := hball x hx
    have hV : V ≤ Ω := hVU.trans hρS
    have hae : ae (μ.restrict (V : Set E)) ≤ ae (μ.restrict Ω) :=
      ae_mono (Measure.restrict_mono hV le_rfl)
    refine W1p.lipschitzOnWith_preciseRepresentative_of_ae_norm_gradient_le u hV
      (convex_ball x _) ?_ ?_
    · refine memLp_top_of_bound ((Lp.aestronglyMeasurable _).mono_measure
        (Measure.restrict_mono hV le_rfl)) M₁ ?_
      filter_upwards [ae_restrict_mem V.isOpen.measurableSet, hval.filter_mono hae] with y hy hy'
      rw [hy']
      exact hv y (hVU hy)
    · filter_upwards [ae_restrict_mem V.isOpen.measurableSet, hgrad.filter_mono hae] with y hy hy'
      rw [hy']
      exact (hg y (hVU hy)).trans (Real.le_coe_toNNReal _)
  have hρ2 : ((ρ / 2).toNNReal : ℝ) = ρ / 2 := Real.coe_toNNReal _ (by positivity)
  refine ⟨_, HolderOnWith.of_le_of_dist_le (K := M₂.toNNReal) (D := (2 * M₁).toNNReal)
    (δ := (ρ / 2).toNNReal) (β := 1) (fun x hx y _ hxy => ?_) (fun x hx y hy => ?_) hγ
    (by rw [← NNReal.coe_pos, hρ2]; positivity)⟩
  · rw [hρ2] at hxy
    rw [NNReal.coe_one, Real.rpow_one]
    exact (hlip x hx).dist_le_mul x (mem_ball_self (by positivity)) y
      (mem_ball_comm.1 (mem_ball.2 hxy))
  · have hsub : thickening (ρ / 2) S ⊆ thickening ρ S := thickening_mono (by linarith) S
    calc dist (preciseRepresentative μ (W1p.value u) x)
          (preciseRepresentative μ (W1p.value u) y)
        ≤ ‖preciseRepresentative μ (W1p.value u) x‖ +
          ‖preciseRepresentative μ (W1p.value u) y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M₁ := by linarith [hv x (hsub hx), hv y (hsub hy)]
      _ ≤ (2 * M₁).toNNReal := Real.le_coe_toNNReal _

end TauCeti
