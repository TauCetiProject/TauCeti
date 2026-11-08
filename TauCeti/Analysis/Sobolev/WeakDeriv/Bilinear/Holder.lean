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
import TauCeti.MeasureTheory.Function.Lp.Holder
import TauCeti.Analysis.Calculus.LineDeriv.Bilinear
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Weak bilinear product rules at Hölder exponents

The product of two weakly differentiable Banach-valued functions satisfies the Leibniz rule
under Hölder integrability hypotheses on every compact subset of the domain. Both factors may be
rough, and their weak derivatives supply completeness of their coefficient spaces. The proof
mollifies
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

variable {E F G H : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {Ω : Opens E} {v : E}

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
  exact hud.clm_bilin B hwd

/-- The bilinear weak Leibniz rule at finite Hölder exponents. Neither factor is assumed
classically differentiable. The exponent conditions include the integrable target `r = 1`. -/
private theorem hasWeakLineDerivOn_bilin_of_memLp (B : F →L[ℝ] G →L[ℝ] H)
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    {f f' : E → F} {g g' : E → G}
    (hf : HasWeakLineDerivOn μ Ω f f' v) (hg : HasWeakLineDerivOn μ Ω g g' v)
    (hfp : MemLp f p (μ.restrict Ω)) (hf'p : MemLp f' p (μ.restrict Ω))
    (hgq : MemLp g q (μ.restrict Ω)) (hg'q : MemLp g' q (μ.restrict Ω)) :
    HasWeakLineDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B (f' x) (g x) + B (f x) (g' x)) v := by
  let _ : CompleteSpace F := hf.completeSpace
  let _ : CompleteSpace G := hg.completeSpace
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
  obtain ⟨φ, hφ, hsupp⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := μ) hWc hWΩ
  let u := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U
  let u' := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] U'
  let w := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V
  let w' := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] V'
  have hweak (n : ℕ) : HasWeakLineDerivOn μ W (fun x => B (u n x) (w n x))
      (fun x => B (u' n x) (w n x) + B (u n x) (w' n x)) v :=
    hasWeakLineDerivOn_bilin_convolution B hf.indicator hg.indicator
      hUloc hU'loc hVloc hV'loc (φ n).contDiff_normed (φ n).hasCompactSupport_normed (hsupp n)
  have hUae := hU.coeFn_toLp_indicator_restrict W.isOpen.measurableSet hWΩ'
  have hU'ae := hU'.coeFn_toLp_indicator_restrict W.isOpen.measurableSet hWΩ'
  have hVae := hV.coeFn_toLp_indicator_restrict W.isOpen.measurableSet hWΩ'
  have hV'ae := hV'.coeFn_toLp_indicator_restrict W.isOpen.measurableSet hWΩ'
  -- Hölder makes both Leibniz terms converge in the target space; restriction turns this into
  -- L1 convergence.
  exact hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub (IntegrableOn.locallyIntegrableOn hlim)
    (IntegrableOn.locallyIntegrableOn hlim') hweak
    (tendsto_setLIntegral_enorm_bilin_normedBump_sub (r := r) B hp hq hU hV hφ hWμ hUae hVae)
    (tendsto_setLIntegral_enorm_bilin_leibniz_normedBump_sub (r := r) B hp hq hU hU' hV hV' hφ
      hWμ hUae hU'ae hVae hV'ae)


/-- The local bilinear weak Leibniz rule at finite Hölder exponents. Values and derivatives
need only belong to their input `Lp` spaces on compact subsets of the open domain. -/
theorem HasWeakLineDerivOn.bilin_of_memLp (B : F →L[ℝ] G →L[ℝ] H)
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    {f f' : E → F} {g g' : E → G}
    (hf : HasWeakLineDerivOn μ Ω f f' v) (hg : HasWeakLineDerivOn μ Ω g g' v)
    (hfp : ∀ K, IsCompact K → K ⊆ Ω → MemLp f p (μ.restrict K))
    (hf'p : ∀ K, IsCompact K → K ⊆ Ω → MemLp f' p (μ.restrict K))
    (hgq : ∀ K, IsCompact K → K ⊆ Ω → MemLp g q (μ.restrict K))
    (hg'q : ∀ K, IsCompact K → K ⊆ Ω → MemLp g' q (μ.restrict K)) :
    HasWeakLineDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B (f' x) (g x) + B (f x) (g' x)) v := by
  rw [hasWeakLineDerivOn_iff_forall_isCompact_closure]
  intro W hWc hWΩ
  have hWΩ' : (W : Set E) ⊆ Ω := subset_closure.trans hWΩ
  have hμ : μ.restrict (W : Set E) ≤ μ.restrict (closure (W : Set E)) :=
    Measure.restrict_mono_set μ subset_closure
  exact hasWeakLineDerivOn_bilin_of_memLp (r := r) B hp hq (hf.mono hWΩ') (hg.mono hWΩ')
    ((hfp _ hWc hWΩ).mono_measure hμ) ((hf'p _ hWc hWΩ).mono_measure hμ)
    ((hgq _ hWc hWΩ).mono_measure hμ) ((hg'q _ hWc hWΩ).mono_measure hμ)

/-- The Fréchet form of the bilinear weak Leibniz rule. The derivative field is expressed using
native continuous bilinear precomposition maps, so its local `Lʳ` membership follows from Hölder. -/
theorem HasWeakFDerivOn.bilin_of_memLp (B : F →L[ℝ] G →L[ℝ] H)
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    {f : E → F} {Df : E → E →L[ℝ] F} {g : E → G} {Dg : E → E →L[ℝ] G}
    (hf : HasWeakFDerivOn μ Ω f Df) (hg : HasWeakFDerivOn μ Ω g Dg)
    (hfp : ∀ K, IsCompact K → K ⊆ Ω → MemLp f p (μ.restrict K))
    (hDfp : ∀ K, IsCompact K → K ⊆ Ω → MemLp Df p (μ.restrict K))
    (hgq : ∀ K, IsCompact K → K ⊆ Ω → MemLp g q (μ.restrict K))
    (hDgq : ∀ K, IsCompact K → K ⊆ Ω → MemLp Dg q (μ.restrict K)) :
    HasWeakFDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B.precompL E (Df x) (g x) + B.precompR E (f x) (Dg x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  simpa only [add_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply] using
    (hf.hasWeakLineDerivOn v).bilin_of_memLp (r := r) B hp hq (hg.hasWeakLineDerivOn v)
      hfp (fun K hK hKΩ => (hDfp K hK hKΩ).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ F v))
      hgq (fun K hK hKΩ => (hDgq K hK hKΩ).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ G v))

end TauCeti
