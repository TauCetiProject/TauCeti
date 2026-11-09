/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Weak derivatives pass to `L¹` limits

The weak-derivative relation of `TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean` is a family of
integral identities against test functions, so it survives any limit that is strong enough to
pass under those integrals.  Convergence in `L¹(Ω)` is enough: a test function and its
directional derivatives are bounded and supported inside `Ω`, so

`∫ (∂_v φ) • uᵢ → ∫ (∂_v φ) • u` and `∫ φ • uᵢ' → ∫ φ • u'`

as soon as `‖uᵢ - u‖_{L¹(Ω)} → 0` and `‖uᵢ' - u'‖_{L¹(Ω)} → 0`.  Local integrability of the two
limits is not automatic from the convergence and is therefore a hypothesis.

This is the step that transports a derivative computation from smooth functions to a general
Sobolev function: the smooth approximations have classical derivatives, and the limit inherits
them weakly.  It is stated for an arbitrary filter of approximations, and with the `L¹` distance
written as a lower Lebesgue integral so that no integrability of the differences is needed.

Only the integrals against test functions need to converge, so weak derivatives also pass to
distributional limits, and in particular to weak limits in `L²`.  This is the closure step of
the direct method of the calculus of variations, where a minimizing sequence is only known to
converge weakly.

## Main declarations

* `TauCeti.hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub`: the directional statement.
* `TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub`: the Fréchet statement.
* `TauCeti.hasWeakLineDerivOn_of_tendsto_integral_smul`: the statement for distributional limits.
* `TauCeti.hasWeakLineDerivOn_of_tendsto_toWeakSpace`: the statement for weak limits in `L²`.
-/

public section

namespace TauCeti

open Filter _root_.MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] {μ : Measure E}
  {Ω : Opens E} {v : E} {ι : Type*} {l : Filter ι}

/-- **Weak directional derivatives pass to `L¹(Ω)` limits.**  If each `uᵢ` has `uᵢ'` as a weak
derivative in the direction `v` on `Ω`, and both families converge in `L¹(Ω)` to locally
integrable limits, then the limit of the derivatives is a weak derivative of the limit. -/
theorem hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub [OpensMeasurableSpace E] [l.NeBot]
    {u u' : ι → E → F} {w w' : E → F}
    (hw : LocallyIntegrableOn w Ω μ) (hw' : LocallyIntegrableOn w' Ω μ)
    (h : ∀ i, HasWeakLineDerivOn μ Ω (u i) (u' i) v)
    (hu : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖u i x - w x‖ₑ ∂μ) l (𝓝 0))
    (hu' : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖u' i x - w' x‖ₑ ∂μ) l (𝓝 0)) :
    HasWeakLineDerivOn μ Ω w w' v := by
  have : Nonempty ι := nonempty_of_neBot l
  have hcomplete : CompleteSpace F := (h (Classical.arbitrary ι)).completeSpace
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨hcomplete, hw, hw', fun φ => ?_⟩
  obtain ⟨K, hK⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨K', hK'⟩ :=
    (TestFunction.lineDerivCLM ℝ v φ).continuous.bounded_above_of_compact_support
      (TestFunction.lineDerivCLM ℝ v φ).hasCompactSupport
  have hdφ : ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) : E → ℝ) =
      fun x => lineDeriv ℝ (φ : E → ℝ) x v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  rw [hdφ] at hK'
  have h1 : Tendsto (fun i => ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u i x ∂μ) l
      (𝓝 (∫ x, lineDeriv ℝ (φ : E → ℝ) x v • w x ∂μ)) :=
    MeasureTheory.tendsto_integral_smul_of_tendsto_lintegral_enorm_sub (ae_of_all _ hK')
      (ae_of_all _ fun x hx =>
        lineDeriv_of_notMem_tsupport (fun hm => hx (φ.tsupport_subset hm)) v)
      (Eventually.of_forall fun i =>
        integrable_lineDeriv_smul_of_locallyIntegrableOn (h i).locallyIntegrableOn φ v)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hw φ v).aestronglyMeasurable hu
  have h2 : Tendsto (fun i => ∫ x, (φ : E → ℝ) x • u' i x ∂μ) l
      (𝓝 (∫ x, (φ : E → ℝ) x • w' x ∂μ)) :=
    MeasureTheory.tendsto_integral_smul_of_tendsto_lintegral_enorm_sub (ae_of_all _ hK)
      (ae_of_all _ fun x hx =>
        image_eq_zero_of_notMem_tsupport fun hm => hx (φ.tsupport_subset hm))
      (Eventually.of_forall fun i =>
        φ.integrable_smul (h i).locallyIntegrableOn_deriv)
      (φ.integrable_smul hw').aestronglyMeasurable hu'
  refine tendsto_nhds_unique ?_ h2.neg
  simpa only [(h _).integral_lineDeriv_smul_eq_neg_integral_smul φ] using h1

/-- **Weak Fréchet derivatives pass to `L¹(Ω)` limits.**  The Fréchet form of
`TauCeti.hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub`, with the derivatives converging in
the operator norm. -/
theorem hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub [OpensMeasurableSpace E] [l.NeBot]
    {u : ι → E → F} {U : ι → E → E →L[ℝ] F} {w : E → F} {W : E → E →L[ℝ] F}
    (hw : LocallyIntegrableOn w Ω μ) (hW : ∀ v : E, LocallyIntegrableOn (fun x => W x v) Ω μ)
    (h : ∀ i, HasWeakFDerivOn μ Ω (u i) (U i))
    (hu : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖u i x - w x‖ₑ ∂μ) l (𝓝 0))
    (hU : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖U i x - W x‖ₑ ∂μ) l (𝓝 0)) :
    HasWeakFDerivOn μ Ω w W := by
  rw [hasWeakFDerivOn_iff]
  intro v
  refine hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub hw (hW v)
    (fun i => (h i).hasWeakLineDerivOn v) hu ?_
  have hbound : ∀ i, ∫⁻ x in (Ω : Set E), ‖U i x v - W x v‖ₑ ∂μ ≤
      ‖v‖ₑ * ∫⁻ x in (Ω : Set E), ‖U i x - W x‖ₑ ∂μ := by
    intro i
    rw [← lintegral_const_mul' _ _ enorm_ne_top]
    refine lintegral_mono fun x => ?_
    have hle : ‖U i x v - W x v‖ ≤ ‖U i x - W x‖ * ‖v‖ := by
      simpa using (U i x - W x).le_opNorm v
    calc ‖U i x v - W x v‖ₑ ≤ ENNReal.ofReal (‖U i x - W x‖ * ‖v‖) := by
          simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hle
      _ = ‖v‖ₑ * ‖U i x - W x‖ₑ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm,
            mul_comm]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => zero_le) hbound
  simpa using ENNReal.Tendsto.const_mul (a := ‖v‖ₑ) hU (Or.inr enorm_ne_top)

/-- **Weak directional derivatives pass to distributional limits.**  If each `uᵢ` has `uᵢ'` as a
weak derivative in the direction `v` on `Ω`, and the integrals of both families against every test
function on `Ω` converge to those of locally integrable limits, then the limit of the derivatives
is a weak derivative of the limit. -/
theorem hasWeakLineDerivOn_of_tendsto_integral_smul [l.NeBot] {u u' : ι → E → F} {w w' : E → F}
    (hw : LocallyIntegrableOn w Ω μ) (hw' : LocallyIntegrableOn w' Ω μ)
    (h : ∀ i, HasWeakLineDerivOn μ Ω (u i) (u' i) v)
    (hu : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ x, (φ : E → ℝ) x • u i x ∂μ) l (𝓝 (∫ x, (φ : E → ℝ) x • w x ∂μ)))
    (hu' : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ x, (φ : E → ℝ) x • u' i x ∂μ) l (𝓝 (∫ x, (φ : E → ℝ) x • w' x ∂μ))) :
    HasWeakLineDerivOn μ Ω w w' v := by
  have : Nonempty ι := nonempty_of_neBot l
  have hcomplete : CompleteSpace F := (h (Classical.arbitrary ι)).completeSpace
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨hcomplete, hw, hw', fun φ => ?_⟩
  have hdφ : ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) : E → ℝ) =
      fun x => lineDeriv ℝ (φ : E → ℝ) x v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  have h1 := hu (TestFunction.lineDerivCLM ℝ v φ)
  rw [hdφ] at h1
  refine tendsto_nhds_unique ?_ (hu' φ).neg
  simpa only [(h _).integral_lineDeriv_smul_eq_neg_integral_smul φ] using h1

/-- **Weak directional derivatives pass to weak limits in `L²`.**  If each `uᵢ` has `uᵢ'` as a
weak derivative in the direction `v` on `Ω`, and both families converge weakly in `L²(μ)`, then
the weak limit of the derivatives is a weak derivative of the weak limit of the functions. -/
theorem hasWeakLineDerivOn_of_tendsto_toWeakSpace [OpensMeasurableSpace E]
    [IsLocallyFiniteMeasure μ] [l.NeBot] {u u' : ι → Lp ℝ 2 μ} {w w' : Lp ℝ 2 μ}
    (h : ∀ i, HasWeakLineDerivOn μ Ω (u i) (u' i) v)
    (hu : Tendsto (fun i => toWeakSpace ℝ _ (u i)) l (𝓝 (toWeakSpace ℝ _ w)))
    (hu' : Tendsto (fun i => toWeakSpace ℝ _ (u' i)) l (𝓝 (toWeakSpace ℝ _ w'))) :
    HasWeakLineDerivOn μ Ω w w' v := by
  have hli (f : Lp ℝ 2 μ) : LocallyIntegrableOn f Ω μ :=
    ((Lp.memLp f).locallyIntegrable one_le_two).locallyIntegrableOn _
  -- Integrals against a test function are `L²` inner products, which converge weakly.
  have hlim {f : ι → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
      (hf : Tendsto (fun i => toWeakSpace ℝ _ (f i)) l (𝓝 (toWeakSpace ℝ _ g)))
      (φ : 𝓓(Ω, ℝ)) :
      Tendsto (fun i => ∫ x, (φ : E → ℝ) x • f i x ∂μ) l (𝓝 (∫ x, (φ : E → ℝ) x • g x ∂μ)) := by
    have hφ : MemLp (φ : E → ℝ) 2 μ := φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
    have h := tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hf (innerSL ℝ (hφ.toLp _))
    simpa only [innerSL_apply_apply, L2.inner_toLp_left, real_inner_eq_re_inner, RCLike.inner_apply,
      conj_trivial, RCLike.re_to_real, smul_eq_mul, mul_comm] using h
  exact hasWeakLineDerivOn_of_tendsto_integral_smul (hli w) (hli w') h (hlim hu) (hlim hu')

end TauCeti
