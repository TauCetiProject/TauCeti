/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.Restriction
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Weak bilinear product rules at Hölder exponents

The product of two weakly differentiable Banach-valued functions satisfies the Leibniz rule
under the usual Hölder integrability hypotheses. Both factors may be rough. The proof mollifies
both factors, applies the classical rule, and passes to the limit on relatively compact open
subdomains. This follows the local mollification proof of the symmetric energy identity in
`TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Basic`, using the existing general approximation
and weak-limit APIs. No boundary regularity or boundedness of the original domain is required.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.3 (weak product rules)
  and §5.3.1 (local approximation by mollification).
-/

public section

open MeasureTheory Filter Set TopologicalSpace Metric
open scoped Convolution ContDiff ENNReal Topology

namespace TauCeti

private theorem tendsto_setLIntegral_enorm_sub_of_tendsto_Lp
    {E H : Type*} [MeasurableSpace E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {μ : Measure E} {r : ℝ≥0∞} [Fact (1 ≤ r)] {W : Set E} (hW : μ W < ⊤)
    {A : ℕ → Lp H r μ} {A₀ : Lp H r μ} (hA : Tendsto A atTop (𝓝 A₀))
    {a : ℕ → E → H} {a₀ : E → H} (ha : ∀ n, A n =ᵐ[μ] a n)
    (ha₀ : A₀ =ᵐ[μ.restrict W] a₀) :
    Tendsto (fun n => ∫⁻ x in W, ‖a n x - a₀ x‖ₑ ∂μ) atTop (𝓝 0) := by
  let R := W.LpToL1RestrictCLM (𝕜 := ℝ) (F := H) (p := r) hW
  have h := (R.continuous.tendsto A₀).comp hA
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h
  refine h.congr fun n => ?_
  rw [eLpNorm_one_eq_lintegral_enorm ((Lp.aestronglyMeasurable _).sub
    (Lp.aestronglyMeasurable _))]
  apply lintegral_congr_ae
  filter_upwards [W.LpToL1RestrictCLM_coeFn (𝕜 := ℝ) hW (A n),
    W.LpToL1RestrictCLM_coeFn (𝕜 := ℝ) hW A₀, ae_restrict_of_ae (ha n), ha₀]
    with x h₁ h₂ h₃ h₄
  -- Expose function composition after rewriting the Lp metric as an integral.
  change ‖R (A n) x - R A₀ x‖ₑ = _
  exact congrArg (fun z => ‖z‖ₑ) (congrArg₂ (· - ·) (h₁.trans h₃) (h₂.trans h₄))

variable {E F G H : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {Ω : Opens E} {v : E}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
  [CompleteSpace F] [CompleteSpace G] [CompleteSpace H] in
private theorem hasLineDerivAt_bilin (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} {f' : F} {g' : G} {x v : E}
    (hf : HasLineDerivAt ℝ f f' x v) (hg : HasLineDerivAt ℝ g g' x v) :
    HasLineDerivAt ℝ (fun y => B (f y) (g y)) (B f' (g x) + B (f x) g') x v := by
  -- A directional derivative is a one-variable derivative along the affine line.
  change HasDerivAt _ _ 0
  simpa only [Function.comp_apply, zero_smul, add_zero] using
    (B.hasFDerivAt.comp_hasDerivAt 0 hf).clm_apply hg

omit [CompleteSpace F] [CompleteSpace G] in
private theorem hasWeakLineDerivOn_bilin_convolution (B : F →L[ℝ] G →L[ℝ] H)
    {U U' : E → F} {V V' : E → G}
    (hf : HasWeakLineDerivOn μ Ω U U' v) (hg : HasWeakLineDerivOn μ Ω V V' v)
    (hU : LocallyIntegrable U μ) (hU' : LocallyIntegrable U' μ)
    (hV : LocallyIntegrable V μ) (hV' : LocallyIntegrable V' μ)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) {W : Opens E}
    (hsupp : ∀ x ∈ (W : Set E), ∀ y ∈ tsupport ρ, x - y ∈ Ω) :
    HasWeakLineDerivOn μ W
      (fun x => B ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) x)
        ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V) x))
      (fun x => B ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U') x)
        ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V) x) +
        B ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U) x)
          ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V') x)) v := by
  let u := ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U
  let u' := ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U'
  let w := ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V
  let w' := ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V'
  have huc : Continuous u := hρc.continuous_convolution_left
    _ hρ.continuous hU
  have hu'c : Continuous u' := hρc.continuous_convolution_left
    _ hρ.continuous hU'
  have hwc : Continuous w := hρc.continuous_convolution_left
    _ hρ.continuous hV
  have hw'c : Continuous w' := hρc.continuous_convolution_left
    _ hρ.continuous hV'
  refine hasWeakLineDerivOn_of_hasLineDerivAt
    ((B.continuous₂.comp (huc.prodMk hwc)).locallyIntegrable.locallyIntegrableOn _)
    (((B.continuous₂.comp (hu'c.prodMk hwc)).add
      (B.continuous₂.comp (huc.prodMk hw'c))).locallyIntegrable.locallyIntegrableOn _) ?_
  intro x hx
  have hud := hf.hasLineDerivAt_convolution_right hU
    _ hρ hρc x (hsupp x hx)
  have hwd := hg.hasLineDerivAt_convolution_right hV
    _ hρ hρc x (hsupp x hx)
  rw [convolution_flip, convolution_flip] at hud hwd
  exact hasLineDerivAt_bilin B hud hwd

/-- The bilinear weak Leibniz rule at finite Hölder exponents. Neither factor is assumed
classically differentiable. The exponent conditions include the integrable target `r = 1`. -/
theorem HasWeakLineDerivOn.bilin_of_memLp (B : F →L[ℝ] G →L[ℝ] H)
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    {f f' : E → F} {g g' : E → G}
    (hf : HasWeakLineDerivOn μ Ω f f' v) (hg : HasWeakLineDerivOn μ Ω g g' v)
    (hfp : MemLp f p (μ.restrict Ω)) (hf'p : MemLp f' p (μ.restrict Ω))
    (hgq : MemLp g q (μ.restrict Ω)) (hg'q : MemLp g' q (μ.restrict Ω)) :
    HasWeakLineDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B (f' x) (g x) + B (f x) (g' x)) v := by
  -- Zero extensions provide global Lp inputs for the native approximate identity.
  have hΩm := Ω.isOpen.measurableSet.nullMeasurableSet (μ := μ)
  let U := (Ω : Set E).indicator f
  let U' := (Ω : Set E).indicator f'
  let V := (Ω : Set E).indicator g
  let V' := (Ω : Set E).indicator g'
  have hU : MemLp U p μ := (memLp_indicator_iff_restrict hΩm).2 hfp
  have hU' : MemLp U' p μ := (memLp_indicator_iff_restrict hΩm).2 hf'p
  have hV : MemLp V q μ := (memLp_indicator_iff_restrict hΩm).2 hgq
  have hV' : MemLp V' q μ := (memLp_indicator_iff_restrict hΩm).2 hg'q
  have hUloc := hU.locallyIntegrable (Fact.out : 1 ≤ p)
  have hU'loc := hU'.locallyIntegrable (Fact.out : 1 ≤ p)
  have hVloc := hV.locallyIntegrable (Fact.out : 1 ≤ q)
  have hV'loc := hV'.locallyIntegrable (Fact.out : 1 ≤ q)
  -- Work locally, where the kernels stay inside the domain and the measure is finite.
  rw [hasWeakLineDerivOn_iff_forall_isCompact_closure]
  intro W hWc hWΩ
  have hWΩ' : (W : Set E) ⊆ Ω := subset_closure.trans hWΩ
  have hWμ : μ (W : Set E) < ⊤ := lt_of_le_of_lt (measure_mono subset_closure)
    hWc.measure_lt_top
  let _ : IsFiniteMeasure (μ.restrict (W : Set E)) := isFiniteMeasure_restrict.2 hWμ.ne
  have hlim := ((B.memLp_of_bilin r hfp hgq).mono_measure
    (Measure.restrict_mono hWΩ' le_rfl)).integrable (Fact.out : 1 ≤ r)
  have hlim' := (((B.memLp_of_bilin r hf'p hgq).add (B.memLp_of_bilin r hfp hg'q)).mono_measure
    (Measure.restrict_mono hWΩ' le_rfl)).integrable (Fact.out : 1 ≤ r)
  obtain ⟨δ, hδ, hδΩ⟩ := hWc.exists_cthickening_subset_open Ω.isOpen hWΩ
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    { rIn := δ / (n + 2), rOut := δ / (n + 1), rIn_pos := by positivity,
      rIn_lt_rOut := div_lt_div_of_pos_left hδ (by positivity) (by linarith) }
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hsupp (n : ℕ) (x : E) (hx : x ∈ (W : Set E)) :
      ∀ y ∈ tsupport ((φ n).normed μ), x - y ∈ Ω := by
    intro y hy
    rw [(φ n).tsupport_normed_eq, mem_closedBall, dist_zero_right] at hy
    refine hδΩ (mem_cthickening_of_dist_le _ x δ _ (subset_closure hx) ?_)
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact hy.trans (div_le_self hδ.le (by simp))
  let u := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U
  let u' := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U'
  let w := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V
  let w' := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V'
  have hweak (n : ℕ) : HasWeakLineDerivOn μ W (fun x => B (u n x) (w n x))
      (fun x => B (u' n x) (w n x) + B (u n x) (w' n x)) v :=
    hasWeakLineDerivOn_bilin_convolution B hf.indicator hg.indicator
      hUloc hU'loc hVloc hV'loc (φ n).contDiff_normed (φ n).hasCompactSupport_normed (hsupp n)
  -- Approximate identities converge in the input spaces. Hölder makes both Leibniz
  -- terms converge in the target space; restriction turns this into L1 convergence.
  let A := fun n => normedBumpLp hp (φ n) μ (hU.toLp U)
  let A' := fun n => normedBumpLp hp (φ n) μ (hU'.toLp U')
  let C := fun n => normedBumpLp hq (φ n) μ (hV.toLp V)
  let C' := fun n => normedBumpLp hq (φ n) μ (hV'.toLp V')
  have hA := tendsto_normedBumpLp (mu := μ) hp hφ (hU.toLp U)
  have hA' := tendsto_normedBumpLp (mu := μ) hp hφ (hU'.toLp U')
  have hC := tendsto_normedBumpLp (mu := μ) hq hφ (hV.toLp V)
  have hC' := tendsto_normedBumpLp (mu := μ) hq hφ (hV'.toLp V')
  let T := B.holderL μ p q r
  have hprod {a : ℕ → Lp F p μ} {a₀ : Lp F p μ} {c : ℕ → Lp G q μ} {c₀ : Lp G q μ}
      (ha : Tendsto a atTop (𝓝 a₀)) (hc : Tendsto c atTop (𝓝 c₀)) :
      Tendsto (fun n => T (a n) (c n)) atTop (𝓝 (T a₀ c₀)) :=
    (isBoundedBilinearMap_apply.continuous.tendsto _).comp
      (((T.continuous.tendsto a₀).comp ha).prodMk_nhds hc)
  have hAae (n : ℕ) : A n =ᵐ[μ] u n := normedBumpLp_ae_eq_convolution hp (φ n) hU
  have hA'ae (n : ℕ) : A' n =ᵐ[μ] u' n := normedBumpLp_ae_eq_convolution hp (φ n) hU'
  have hCae (n : ℕ) : C n =ᵐ[μ] w n := normedBumpLp_ae_eq_convolution hq (φ n) hV
  have hC'ae (n : ℕ) : C' n =ᵐ[μ] w' n := normedBumpLp_ae_eq_convolution hq (φ n) hV'
  have hWae : ∀ᵐ x ∂μ.restrict W, x ∈ (Ω : Set E) :=
    (ae_restrict_mem W.isOpen.measurableSet).mono fun x hx => hWΩ' hx
  have hUae : hU.toLp U =ᵐ[μ.restrict W] f := by
    filter_upwards [ae_restrict_of_ae hU.coeFn_toLp, hWae] with x h₁ h₂
    simp only [h₁, U, indicator_of_mem h₂]
  have hU'ae : hU'.toLp U' =ᵐ[μ.restrict W] f' := by
    filter_upwards [ae_restrict_of_ae hU'.coeFn_toLp, hWae] with x h₁ h₂
    simp only [h₁, U', indicator_of_mem h₂]
  have hVae : hV.toLp V =ᵐ[μ.restrict W] g := by
    filter_upwards [ae_restrict_of_ae hV.coeFn_toLp, hWae] with x h₁ h₂
    simp only [h₁, V, indicator_of_mem h₂]
  have hV'ae : hV'.toLp V' =ᵐ[μ.restrict W] g' := by
    filter_upwards [ae_restrict_of_ae hV'.coeFn_toLp, hWae] with x h₁ h₂
    simp only [h₁, V', indicator_of_mem h₂]
  refine hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub (IntegrableOn.locallyIntegrableOn hlim)
    (IntegrableOn.locallyIntegrableOn hlim') hweak
    (tendsto_setLIntegral_enorm_sub_of_tendsto_Lp hWμ (hprod hA hC) ?_ ?_)
    (tendsto_setLIntegral_enorm_sub_of_tendsto_Lp hWμ
      ((hprod hA' hC).add (hprod hA hC')) ?_ ?_)
  · intro n
    filter_upwards [B.coeFn_holder (r := r) (A n) (C n), hAae n, hCae n] with x h₁ h₂ h₃
    exact h₁.trans (congrArg₂ (fun a c => B a c) h₂ h₃)
  · filter_upwards [ae_restrict_of_ae (B.coeFn_holder (r := r) (hU.toLp U) (hV.toLp V)),
      hUae, hVae] with x h₁ h₂ h₃
    exact h₁.trans (congrArg₂ (fun a c => B a c) h₂ h₃)
  · intro n
    filter_upwards [Lp.coeFn_add (T (A' n) (C n)) (T (A n) (C' n)),
      B.coeFn_holder (r := r) (A' n) (C n), B.coeFn_holder (r := r) (A n) (C' n),
      hA'ae n, hCae n, hAae n, hC'ae n] with x h₀ h₁ h₂ h₃ h₄ h₅ h₆
    exact h₀.trans (congrArg₂ (· + ·)
      (h₁.trans (congrArg₂ (fun a c => B a c) h₃ h₄))
      (h₂.trans (congrArg₂ (fun a c => B a c) h₅ h₆)))
  · filter_upwards [ae_restrict_of_ae (Lp.coeFn_add
        (T (hU'.toLp U') (hV.toLp V)) (T (hU.toLp U) (hV'.toLp V'))),
      ae_restrict_of_ae (B.coeFn_holder (r := r) (hU'.toLp U') (hV.toLp V)),
      ae_restrict_of_ae (B.coeFn_holder (r := r) (hU.toLp U) (hV'.toLp V')),
      hU'ae, hVae, hUae, hV'ae] with x h₀ h₁ h₂ h₃ h₄ h₅ h₆
    exact h₀.trans (congrArg₂ (· + ·)
      (h₁.trans (congrArg₂ (fun a c => B a c) h₃ h₄))
      (h₂.trans (congrArg₂ (fun a c => B a c) h₅ h₆)))

/-- The Fréchet form of the bilinear weak Leibniz rule. The derivative field is expressed using
native continuous bilinear precomposition maps, so its `Lʳ` membership follows from Hölder. -/
theorem HasWeakFDerivOn.bilin_of_memLp (B : F →L[ℝ] G →L[ℝ] H)
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    {f : E → F} {Df : E → E →L[ℝ] F} {g : E → G} {Dg : E → E →L[ℝ] G}
    (hf : HasWeakFDerivOn μ Ω f Df) (hg : HasWeakFDerivOn μ Ω g Dg)
    (hfp : MemLp f p (μ.restrict Ω)) (hDfp : MemLp Df p (μ.restrict Ω))
    (hgq : MemLp g q (μ.restrict Ω)) (hDgq : MemLp Dg q (μ.restrict Ω)) :
    HasWeakFDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B.precompL E (Df x) (g x) + B.precompR E (f x) (Dg x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  simpa only [add_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply] using
    (hf.hasWeakLineDerivOn v).bilin_of_memLp (r := r) B hp hq (hg.hasWeakLineDerivOn v)
      hfp (hDfp.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ F v))
      hgq (hDgq.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ G v))

end TauCeti
