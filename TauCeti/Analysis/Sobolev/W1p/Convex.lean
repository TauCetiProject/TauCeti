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
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Convex.Measure
import TauCeti.Data.ENNReal.Inv
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Lipschitz and Hölder representatives on convex domains

The precise representative of a real `W^{1,∞}` function on an open set is Lipschitz on
each convex subset, with constant at most the essential supremum of its weak gradient.
In particular the whole-space representative has this bound. Neither boundedness of the
domain nor boundary regularity is needed. On an arbitrary open domain the representative is
therefore locally Lipschitz, and by Rademacher's theorem its classical directional derivatives,
which exist almost everywhere, are the components of the weak gradient.

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

For `p` above the dimension `n`, **Morrey's inequality holds up to the boundary of a bounded
convex domain** `Ω`: the precise representative of `u ∈ W^{1,p}(Ω)` is Hölder continuous
on all of `Ω` with exponent `1 - n / p` and constant `C ‖∇u‖_{Lᵖ(Ω)}`, where `C` depends on `n`,
`p`, the Haar measure and `Ω`, and it extends to a Hölder function on `closure Ω`. For `p = ∞`
the Lipschitz bound above has the sharp constant. The proof is Campanato's. A convex set
containing a ball `B(z, ρ)` fills a fixed fraction of every ball `B(x, r)` centred in it with
`r ≤ 2 diam Ω` (`Convex.ofReal_div_pow_mul_addHaar_closedBall_le_addHaar_closedBall_inter`), and
`B(x, r) ∩ Ω` is convex, so the Poincaré–Wirtinger inequality
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex` together with Hölder's inequality bounds
the mean oscillation of `u` there by a multiple of `r ^ (1 - n / p)`. Campanato's theorem on sets
with the measure density property,
`TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le`,
then gives the Hölder bound.

## Main declarations

* `TauCeti.W1p.lipschitzOnWith_preciseRepresentative_of_convex`: the sharp Lipschitz bound for
  `W^{1,∞}` on convex subsets of the domain.
* `TauCeti.W1p.locallyLipschitzOn_preciseRepresentative`,
  `TauCeti.W1p.lineDeriv_preciseRepresentative_ae_eq`: on any open domain the `W^{1,∞}`
  representative is locally Lipschitz, with classical directional derivatives a.e. equal to the
  components of the weak gradient.
* `TauCeti.W1p.lipschitzOnWith_preciseRepresentative_of_ae_norm_gradient_le`: the Lipschitz
  bound for `W^{1,p}` functions with essentially bounded value and gradient on a convex subset.
* `TauCeti.W1p.exists_holderOnWith_preciseRepresentative_of_forall_norm_le`: Hölder bounds
  on thickenings from pointwise bounds on the value and the gradient.
* `TauCeti.W1p.exists_holderOnWith_preciseRepresentative_of_convex`: Morrey's inequality on a
  bounded convex domain, for the precise representative.
* `TauCeti.W1p.exists_holderOnWith_closure_ae_eq_of_convex`: a representative Hölder continuous
  on the closure of a bounded convex domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17 and Lemma 7.16.
* S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup.
  Pisa (3) 17 (1963), 175–188.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Metric Filter TauCeti.MeasureTheory
open scoped Topology Convolution ENNReal NNReal InnerProductSpace

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

/-- The precise representative of a `W^{1,∞}` class is locally Lipschitz on its open domain: it
is Lipschitz on every ball contained in the domain. -/
theorem W1p.locallyLipschitzOn_preciseRepresentative (u : W1p μ Ω ∞) :
    LocallyLipschitzOn (Ω : Set E) (preciseRepresentative μ (W1p.value u)) := fun x hx ↦ by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  exact ⟨_, ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),
    W1p.lipschitzOnWith_preciseRepresentative_of_convex u (convex_ball x r) hrΩ⟩

/-- Almost everywhere on its domain, the classical directional derivative of the precise
representative of a `W^{1,∞}` class is the corresponding component of the weak gradient. -/
theorem W1p.lineDeriv_preciseRepresentative_ae_eq (u : W1p μ Ω ∞) (v : E) :
    (fun x ↦ lineDeriv ℝ (preciseRepresentative μ (W1p.value u)) x v) =ᵐ[μ.restrict Ω]
      fun x ↦ ⟪W1p.gradient u x, v⟫_ℝ := by
  have hll := W1p.locallyLipschitzOn_preciseRepresentative u
  -- Both functions are weak derivatives of the precise representative.
  have h₁ : HasWeakLineDerivOn μ Ω (preciseRepresentative μ (W1p.value u))
      (fun x ↦ lineDeriv ℝ (preciseRepresentative μ (W1p.value u)) x v) v :=
    hll.hasWeakLineDerivOn ((hll.ae_differentiableAt_of_mem Ω.isOpen).mono fun _ hx hxΩ ↦
      (hx hxΩ).lineDifferentiableAt.hasLineDerivAt)
  have h₂ := ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn v).congr_ae
    (W1p.ae_eq_preciseRepresentative u)
  filter_upwards [h₁.ae_eq h₂] with x hx
  rw [hx, innerSL_apply_apply]

/-! ### Morrey's inequality on bounded convex domains -/

section Morrey

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Mean oscillation on balls about the points of a convex domain.** If `Ω` is convex and fills
at least the fraction `c > 0` of `closedBall x r`, then the mean oscillation of `u ∈ W^{1,p}(Ω)`
on `closedBall x r ∩ Ω` is at most `C ‖∇u‖_{Lᵖ(Ω)} r ^ (1 - n / p)`, where `n` is the dimension
and `C = 2 ^ (n + 1) ω (c ω) ^ (-(1 + 1 / p))` with `ω` the measure of the unit ball. -/
private theorem W1p.setAverage_closedBall_norm_sub_le_of_convex
    (hconv : Convex ℝ (Ω : Set E)) (u : W1p μ Ω p) {x : E} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hdens : ENNReal.ofReal c * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω)) :
    ⨍ y in closedBall x r,
        ‖W1p.value u y - ⨍ z in closedBall x r, W1p.value u z ∂μ.restrict Ω‖ ∂μ.restrict Ω ≤
      2 ^ (Module.finrank ℝ E + 1) * μ.real (ball (0 : E) 1) *
        (c * μ.real (ball (0 : E) 1)) ^ (-(1 + 1 / p.toReal)) * ‖W1p.gradient u‖ *
          r ^ (1 - Module.finrank ℝ E / p.toReal) := by
  set e : ℝ := -(1 + 1 / p.toReal)
  let W : Opens E := ⟨ball x r ∩ Ω, isOpen_ball.inter Ω.isOpen⟩
  have hWΩ : W ≤ Ω := SetLike.coe_subset_coe.mp inter_subset_right
  have hWb : Bornology.IsBounded (W : Set E) := isBounded_ball.subset inter_subset_left
  have hω : 0 < μ.real (ball (0 : E) 1) := Metric.measureReal_ball_pos μ 0 one_pos
  -- Averages over `closedBall x r` for `μ.restrict Ω` are averages over `W = ball x r ∩ Ω`.
  have hWae : (closedBall x r ∩ Ω : Set E) =ᵐ[μ] (W : Set E) :=
    ae_eq_set_inter (Measure.addHaar_closedBall_ae_eq_ball_of_ne_zero μ x r hr.ne')
      (Filter.EventuallyEqSet.rfl : (Ω : Set E) =ᵐ[μ] Ω)
  -- The measure of `W` is at least `c ω rⁿ`, where `ω` is the measure of the unit ball.
  have hpos : 0 < c * μ.real (ball (0 : E) 1) * r ^ Module.finrank ℝ E := by positivity
  have hm : c * μ.real (ball (0 : E) 1) * r ^ Module.finrank ℝ E ≤ μ.real W := by
    have hμW : μ.restrict Ω (closedBall x r) = μ W := by
      rw [Measure.restrict_apply measurableSet_closedBall, measure_congr hWae]
    have hω₁ := measureReal_congr (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero 0 1 one_ne_zero)
    have h := Measure.ofReal_mul_rpow_mul_le_addHaar_restrict_closedBall μ x (c := c.toNNReal) hr
      (by rwa [ENNReal.ofNNReal_toNNReal])
    rw [hμW, ← ofReal_measureReal hWb.measure_lt_top.ne,
      ENNReal.ofReal_le_ofReal_iff measureReal_nonneg] at h
    refine Eq.trans_le ?_ h
    rw [Real.coe_toNNReal _ hc.le, Real.rpow_natCast, hω₁]
    ring
  have hW0 : μ W ≠ 0 := fun h ↦
    (hpos.trans_le hm).ne' ((measureReal_eq_zero_iff hWb.measure_lt_top.ne).2 h)
  -- Pass to the restriction of `u` to `W`.
  have hval := W1p.value_restrictL_ae hWΩ u
  have hosc : ⨍ y in W, ‖W1p.value u y - ⨍ z in W, W1p.value u z ∂μ‖ ∂μ =
      ⨍ y in W, ‖W1p.value (W1p.restrictL hWΩ u) y -
        ⨍ z in W, W1p.value (W1p.restrictL hWΩ u) z ∂μ‖ ∂μ := by
    rw [average_congr hval]
    exact average_congr (hval.mono fun y hy ↦ by simp only [hy])
  have hexp : r ^ (1 - Module.finrank ℝ E / p.toReal) =
      r ^ (Module.finrank ℝ E + 1) * r ^ ((Module.finrank ℝ E : ℝ) * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    push_cast [e]
    ring_nf
  rw [Measure.restrict_restrict measurableSet_closedBall, Measure.restrict_congr_set hWae, hosc]
  refine (W1p.setAverage_norm_sub_setAverage_le_of_convex ((convex_ball x r).inter hconv)
    hWb hW0 _).trans ?_
  calc μ.real (ball (0 : E) 1) * diam (W : Set E) ^ (Module.finrank ℝ E + 1) * μ.real W ^ e *
        ‖W1p.gradient (W1p.restrictL hWΩ u)‖
      ≤ μ.real (ball (0 : E) 1) * (2 * r) ^ (Module.finrank ℝ E + 1) *
          (c * μ.real (ball (0 : E) 1) * r ^ Module.finrank ℝ E) ^ e * ‖W1p.gradient u‖ := by
        gcongr _ * ?_ ^ _ * ?_ * ?_
        · exact (diam_mono inter_subset_left isBounded_ball).trans (diam_ball hr.le)
        · exact Real.rpow_le_rpow_of_nonpos hpos hm (neg_nonpos.2 (by positivity))
        · exact W1p.norm_gradient_restrictL_le hWΩ u
    _ = 2 ^ (Module.finrank ℝ E + 1) * μ.real (ball (0 : E) 1) *
          (c * μ.real (ball (0 : E) 1)) ^ e * ‖W1p.gradient u‖ *
            r ^ (1 - Module.finrank ℝ E / p.toReal) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul hr.le,
          mul_pow, hexp]
        ring

/-- **Morrey's inequality on a bounded convex domain.** Let `Ω` be a bounded convex open subset
of a finite-dimensional real inner product space of dimension `n`, and let `n < p ≤ ∞`. There is
a constant `C > 0`, depending on `n`, `p`, the Haar measure `μ` and `Ω`, such that the precise
representative of every `u ∈ W^{1,p}(Ω)`, which agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`), is Hölder continuous on all of `Ω` with exponent
`1 - n / p` and constant `C ‖∇u‖_{Lᵖ(Ω)}`.

Unlike the interior estimate `TauCeti.W1p.exists_holderOnWith_preciseRepresentative`, the bound
holds up to the boundary. The proof is Campanato's: convexity gives the measure density property
(`Convex.ofReal_div_pow_mul_addHaar_closedBall_le_addHaar_closedBall_inter`), and the
Poincaré–Wirtinger inequality on the convex sets `ball x r ∩ Ω` bounds the mean oscillation of
`u` there by a multiple of `r ^ (1 - n / p)`. For `p = ∞` the exponent is `1`, and
`TauCeti.W1p.lipschitzOnWith_preciseRepresentative_of_convex` gives the sharp constant. -/
theorem W1p.exists_holderOnWith_preciseRepresentative_of_convex
    (hp : (Module.finrank ℝ E : ℝ≥0∞) < p) (hconv : Convex ℝ (Ω : Set E))
    (hb : Bornology.IsBounded (Ω : Set E)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : W1p μ Ω p,
      HolderOnWith (C * ‖W1p.gradient u‖).toNNReal
        ((1 : ℝ≥0∞) - Module.finrank ℝ E / p).toNNReal
        (preciseRepresentative μ (W1p.value u)) Ω := by
  set n := Module.finrank ℝ E
  set α : ℝ≥0 := ((1 : ℝ≥0∞) - n / p).toNNReal
  have hα : 0 < α := ENNReal.toNNReal_one_sub_div_pos hp
  have hαp : (α : ℝ) = 1 - n / p.toReal := by
    rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_one_sub_div hp.le, ENNReal.toReal_natCast]
  rcases (Ω : Set E).eq_empty_or_nonempty with hΩ | ⟨z, hz⟩
  · exact ⟨1, one_pos, fun u x hx ↦ by rw [hΩ] at hx; exact hx.elim⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen z hz
  set ω := μ.real (ball (0 : E) 1)
  set R := 2 * diam (Ω : Set E) + ρ
  set c : ℝ := (ρ / R) ^ n
  have hω : 0 < ω := Metric.measureReal_ball_pos μ 0 one_pos
  have hc : 0 < c := by positivity
  -- Convexity gives the measure density property, at every radius up to `2 diam Ω`.
  have hdens : ∀ x ∈ (Ω : Set E), ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ 2 * ediam (Ω : Set E) →
      ENNReal.ofReal c * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω) := by
    intro x hx r hr hrd
    have hrd' : r ≤ 2 * diam (Ω : Set E) := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hb.ediam_ne_top) hrd
      rwa [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h
    exact hconv.ofReal_div_pow_mul_addHaar_closedBall_le_addHaar_closedBall_inter hρ hball
      (subset_closure hx) hr (by linarith) (by linarith [dist_le_diam_of_mem hb hx hz])
  -- The mean oscillation is at most `K ‖∇u‖ r^α`.
  set K := 2 ^ (n + 1) * ω * (c * ω) ^ (-(1 + 1 / p.toReal))
  have hK : 0 < K := by positivity
  set K₀ : ℝ := 2 * 2 ^ (α : ℝ) * (2 ^ n / (c.toNNReal * (1 - 2 ^ (-(α : ℝ)))))
  have hK₀ : 0 < K₀ := by
    have : (2 : ℝ) ^ (-(α : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 (NNReal.coe_pos.2 hα))
    have : 0 < 1 - (2 : ℝ) ^ (-(α : ℝ)) := by linarith
    have : (0 : ℝ) < c.toNNReal := by simpa using hc
    positivity
  refine ⟨K₀ * K, mul_pos hK₀ hK, fun u ↦ ?_⟩
  have hholder := holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le
    (M := (K * ‖W1p.gradient u‖).toNNReal) hα (Real.toNNReal_pos.2 hc)
    ((Lp.memLp (W1p.value u)).locallyIntegrable Fact.out)
    (fun x hx r hr hrd ↦ by rw [ENNReal.ofNNReal_toNNReal]; exact hdens x hx r hr hrd)
    fun x hx r hr hrd ↦ by
      rw [Real.coe_toNNReal _ (by positivity), hαp]
      exact W1p.setAverage_closedBall_norm_sub_le_of_convex hconv u hr hc
        (hdens x hx r hr hrd)
  have hC : (K₀ * K * ‖W1p.gradient u‖).toNNReal =
      K₀.toNNReal * (K * ‖W1p.gradient u‖).toNNReal := by
    rw [mul_assoc, Real.toNNReal_mul hK₀.le]
  intro x hx y hy
  rw [hC, ← preciseRepresentative_restrict_of_mem_nhds (Ω.isOpen.mem_nhds hx),
    ← preciseRepresentative_restrict_of_mem_nhds (Ω.isOpen.mem_nhds hy)]
  exact hholder x hx y hy

/-- **Morrey's embedding on a bounded convex domain, up to the boundary.** Let `Ω` be a bounded
convex open subset of a finite-dimensional real inner product space of dimension `n`, and let
`n < p ≤ ∞`. There is a constant `C > 0`, depending on `n`, `p`, the Haar measure `μ` and `Ω`,
such that every `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function which is Hölder
continuous on `closure Ω` with exponent `1 - n / p` and constant `C ‖∇u‖_{Lᵖ(Ω)}`. -/
theorem W1p.exists_holderOnWith_closure_ae_eq_of_convex
    (hp : (Module.finrank ℝ E : ℝ≥0∞) < p) (hconv : Convex ℝ (Ω : Set E))
    (hb : Bornology.IsBounded (Ω : Set E)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : W1p μ Ω p, ∃ g : E → ℝ,
      HolderOnWith (C * ‖W1p.gradient u‖).toNNReal
        ((1 : ℝ≥0∞) - Module.finrank ℝ E / p).toNNReal g (closure Ω) ∧
      W1p.value u =ᵐ[μ.restrict Ω] g := by
  classical
  obtain ⟨C, hC, hhol⟩ :=
    W1p.exists_holderOnWith_preciseRepresentative_of_convex (μ := μ) hp hconv hb
  refine ⟨C, hC, fun u ↦ ?_⟩
  set f := preciseRepresentative μ (W1p.value u)
  -- Extend `f` from the dense subset `Ω` of `closure Ω`.
  have hdense : Dense (Subtype.val ⁻¹' (Ω : Set E) : Set (closure (Ω : Set E))) :=
    Subtype.dense_iff.2 (by rw [Subtype.image_preimage_coe, inter_eq_right.2 subset_closure])
  obtain ⟨g, hg, hfg⟩ := HolderOnWith.extend_of_dense
    (f := fun x : closure (Ω : Set E) ↦ f x)
    (fun x hx y hy ↦ by simpa only [Subtype.edist_eq] using hhol u x hx y hy) hdense
  refine ⟨fun x ↦ if hx : x ∈ closure (Ω : Set E) then g ⟨x, hx⟩ else 0, fun x hx y hy ↦ ?_, ?_⟩
  · simpa only [dite_eq_left hx, dite_eq_left hy, Subtype.edist_mk_mk] using hg ⟨x, hx⟩ ⟨y, hy⟩
  · refine (W1p.ae_eq_preciseRepresentative u).trans ?_
    filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet] with x hx
    rw [dite_eq_left (subset_closure hx)]
    exact hfg (x := ⟨x, subset_closure hx⟩) hx

end Morrey

end TauCeti
