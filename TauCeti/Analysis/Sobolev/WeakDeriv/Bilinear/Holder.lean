/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.Holder
import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.Analysis.Calculus.LineDeriv.Bilinear
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Normed
import TauCeti.Analysis.Distribution.TestFunction.Integral.Convergence
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Topology.Sets.Opens

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

For a continuous left factor with a continuous directional derivative on `Ω`,
`TauCeti.HasWeakLineDerivOn.bilin_of_hasLineDerivAt_left` proves the weak Leibniz rule for any
weakly differentiable right factor `g` by mollifying `g`. At the endpoint where the left factor is
continuous on `Ω` with `f' ∈ Lᵖ_loc(Ω)` and `g ∈ L^q_loc(Ω)` with `p⁻¹ + q⁻¹ ≤ 1` (allowing
`p = ∞` or `q = ∞`, and without assuming `g' ∈ L^q_loc(Ω)`),
`TauCeti.HasWeakLineDerivOn.bilin_of_continuousOn` obtains the same weak Leibniz rule by mollifying
`f` and reducing to the classically differentiable case.

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
classically differentiable. Each factor and its derivative may carry their own exponents; only
the three products in the identity need Hölder triples. The targets include `1`. -/
private theorem hasWeakLineDerivOn_bilin_of_memLp (B : F →L[ℝ] G →L[ℝ] H)
    {p p' q q' r r₁ r₂ : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)] [Fact (1 ≤ q')]
    [Fact (1 ≤ r)] [Fact (1 ≤ r₁)] [Fact (1 ≤ r₂)]
    [ENNReal.HolderTriple p q r] [ENNReal.HolderTriple p' q r₁] [ENNReal.HolderTriple p q' r₂]
    (hp : p ≠ ⊤) (hp' : p' ≠ ⊤) (hq : q ≠ ⊤) (hq' : q' ≠ ⊤)
    {f f' : E → F} {g g' : E → G}
    (hf : HasWeakLineDerivOn μ Ω f f' v) (hg : HasWeakLineDerivOn μ Ω g g' v)
    (hfp : MemLp f p (μ.restrict Ω)) (hf'p : MemLp f' p' (μ.restrict Ω))
    (hgq : MemLp g q (μ.restrict Ω)) (hg'q : MemLp g' q' (μ.restrict Ω)) :
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
  have hU' : MemLp U' p' μ := (memLp_indicator_iff_restrict hΩm).2 hf'p
  have hV : MemLp V q μ := (memLp_indicator_iff_restrict hΩm).2 hgq
  have hV' : MemLp V' q' μ := (memLp_indicator_iff_restrict hΩm).2 hg'q
  have hUloc := hU.locallyIntegrable (Fact.out : 1 ≤ p)
  have hU'loc := hU'.locallyIntegrable (Fact.out : 1 ≤ p')
  have hVloc := hV.locallyIntegrable (Fact.out : 1 ≤ q)
  have hV'loc := hV'.locallyIntegrable (Fact.out : 1 ≤ q')
  -- Work locally, where the kernels stay inside the domain and the measure is finite.
  rw [hasWeakLineDerivOn_iff_forall_isCompact_closure]
  intro W hWc hWΩ
  have hWΩ' : (W : Set E) ⊆ Ω := subset_closure.trans hWΩ
  have hWμ : μ (W : Set E) < ⊤ := lt_of_le_of_lt (measure_mono subset_closure)
    hWc.measure_lt_top
  let _ : IsFiniteMeasure (μ.restrict (W : Set E)) := isFiniteMeasure_restrict.2 hWμ.ne
  have hle : μ.restrict (W : Set E) ≤ μ.restrict (Ω : Set E) := Measure.restrict_mono hWΩ' le_rfl
  have hlim := ((B.memLp_of_bilin r hfp hgq).mono_measure hle).integrable (Fact.out : 1 ≤ r)
  have hlim₁ := ((B.memLp_of_bilin r₁ hf'p hgq).mono_measure hle).integrable (Fact.out : 1 ≤ r₁)
  have hlim₂ := ((B.memLp_of_bilin r₂ hfp hg'q).mono_measure hle).integrable (Fact.out : 1 ≤ r₂)
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
  have h₁ := B.tendsto_setLIntegral_enorm_bilin_normedBump_sub (r := r₁) hp' hq hU' hV hφ hWμ
    hU'ae hVae
  have h₂ := B.tendsto_setLIntegral_enorm_bilin_normedBump_sub (r := r₂) hp hq' hU hV' hφ hWμ
    hUae hV'ae
  -- The derivative error is bounded by the sum of the two product errors.
  have hm₁ (n : ℕ) : AEStronglyMeasurable (fun x => B (u' n x) (w n x) - B (f' x) (g x))
      (μ.restrict (W : Set E)) :=
    (B.continuous₂.comp_aestronglyMeasurable₂
      ((Lp.aestronglyMeasurable _).congr (normedBumpLp_ae_eq_convolution hp' (φ n) hU')).restrict
      ((Lp.aestronglyMeasurable _).congr (normedBumpLp_ae_eq_convolution hq (φ n) hV)).restrict).sub
        hlim₁.aestronglyMeasurable
  exact hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub (IntegrableOn.locallyIntegrableOn hlim)
    (IntegrableOn.locallyIntegrableOn (hlim₁.add hlim₂)) hweak
    (B.tendsto_setLIntegral_enorm_bilin_normedBump_sub (r := r) hp hq hU hV hφ hWμ hUae hVae)
    (tendsto_setLIntegral_enorm_add_sub hm₁ h₁ h₂)

/-- The local bilinear weak Leibniz rule with separate finite exponents for each factor and its
derivative. Only the three products in the identity must be locally integrable by Hölder; this
covers a rough factor whose derivative is integrable against the other factor but not against its
derivative. -/
theorem HasWeakLineDerivOn.bilin_of_memLp (B : F →L[ℝ] G →L[ℝ] H)
    {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)] [Fact (1 ≤ q')]
    (hp : p ≠ ⊤) (hp' : p' ≠ ⊤) (hq : q ≠ ⊤) (hq' : q' ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp'q : p'⁻¹ + q⁻¹ ≤ 1) (hpq' : p⁻¹ + q'⁻¹ ≤ 1)
    {f f' : E → F} {g g' : E → G}
    (hf : HasWeakLineDerivOn μ Ω f f' v) (hg : HasWeakLineDerivOn μ Ω g g' v)
    (hfp : ∀ K, IsCompact K → K ⊆ Ω → MemLp f p (μ.restrict K))
    (hf'p : ∀ K, IsCompact K → K ⊆ Ω → MemLp f' p' (μ.restrict K))
    (hgq : ∀ K, IsCompact K → K ⊆ Ω → MemLp g q (μ.restrict K))
    (hg'q : ∀ K, IsCompact K → K ⊆ Ω → MemLp g' q' (μ.restrict K)) :
    HasWeakLineDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B (f' x) (g x) + B (f x) (g' x)) v := by
  let _ := ENNReal.HolderTriple.of p q
  let _ := ENNReal.HolderTriple.of p' q
  let _ := ENNReal.HolderTriple.of p q'
  let _ : Fact (1 ≤ (p⁻¹ + q⁻¹)⁻¹) := ⟨ENNReal.one_le_inv.2 hpq⟩
  let _ : Fact (1 ≤ (p'⁻¹ + q⁻¹)⁻¹) := ⟨ENNReal.one_le_inv.2 hp'q⟩
  let _ : Fact (1 ≤ (p⁻¹ + q'⁻¹)⁻¹) := ⟨ENNReal.one_le_inv.2 hpq'⟩
  rw [hasWeakLineDerivOn_iff_forall_isCompact_closure]
  intro W hWc hWΩ
  have hWΩ' : (W : Set E) ⊆ Ω := subset_closure.trans hWΩ
  have hμ : μ.restrict (W : Set E) ≤ μ.restrict (closure (W : Set E)) :=
    Measure.restrict_mono_set μ subset_closure
  exact hasWeakLineDerivOn_bilin_of_memLp (r := (p⁻¹ + q⁻¹)⁻¹) (r₁ := (p'⁻¹ + q⁻¹)⁻¹)
    (r₂ := (p⁻¹ + q'⁻¹)⁻¹) B hp hp' hq hq' (hf.mono hWΩ') (hg.mono hWΩ')
    ((hfp _ hWc hWΩ).mono_measure hμ) ((hf'p _ hWc hWΩ).mono_measure hμ)
    ((hgq _ hWc hWΩ).mono_measure hμ) ((hg'q _ hWc hWΩ).mono_measure hμ)

/-- The Fréchet form of the bilinear weak Leibniz rule with separate finite exponents for each
factor and its derivative, as in `TauCeti.HasWeakLineDerivOn.bilin_of_memLp`. -/
theorem HasWeakFDerivOn.bilin_of_memLp (B : F →L[ℝ] G →L[ℝ] H)
    {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)] [Fact (1 ≤ q')]
    (hp : p ≠ ⊤) (hp' : p' ≠ ⊤) (hq : q ≠ ⊤) (hq' : q' ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp'q : p'⁻¹ + q⁻¹ ≤ 1) (hpq' : p⁻¹ + q'⁻¹ ≤ 1)
    {f : E → F} {Df : E → E →L[ℝ] F} {g : E → G} {Dg : E → E →L[ℝ] G}
    (hf : HasWeakFDerivOn μ Ω f Df) (hg : HasWeakFDerivOn μ Ω g Dg)
    (hfp : ∀ K, IsCompact K → K ⊆ Ω → MemLp f p (μ.restrict K))
    (hDfp : ∀ K, IsCompact K → K ⊆ Ω → MemLp Df p' (μ.restrict K))
    (hgq : ∀ K, IsCompact K → K ⊆ Ω → MemLp g q (μ.restrict K))
    (hDgq : ∀ K, IsCompact K → K ⊆ Ω → MemLp Dg q' (μ.restrict K)) :
    HasWeakFDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B.precompL E (Df x) (g x) + B.precompR E (f x) (Dg x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  simpa only [add_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply] using
    (hf.hasWeakLineDerivOn v).bilin_of_memLp B hp hp' hq hq' hpq hp'q hpq'
      (hg.hasWeakLineDerivOn v)
      hfp (fun K hK hKΩ => (hDfp K hK hKΩ).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ F v))
      hgq (fun K hK hKΩ => (hDgq K hK hKΩ).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ G v))

section Endpoint

open scoped Distributions LineDeriv

/-- Local smooth mollification of a weakly differentiable function on nested relatively compact
opens `W₀ ⋐ W ⋐ Ω`. -/
private theorem exists_seq_normed_convolution_indicator {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {W₀ W : Opens E} (hW₀c : IsCompact (closure (W₀ : Set E)))
    (hW₀W : closure (W₀ : Set E) ⊆ W) (hWc : IsCompact (closure (W : Set E)))
    (hWΩ : closure (W : Set E) ⊆ Ω) {u u' : E → M} (hu : HasWeakLineDerivOn μ Ω u u' v) :
    ∃ ρ : ℕ → ContDiffBump (0 : E),
      Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) ∧
      Integrable ((W : Set E).indicator u) μ ∧
      Integrable ((W : Set E).indicator u') μ ∧
      (∀ n, Continuous
        ((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (W : Set E).indicator u)) ∧
      (∀ n, Continuous
        ((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (W : Set E).indicator u')) ∧
      (∀ n, ∀ x ∈ (W₀ : Set E), HasLineDerivAt ℝ
        ((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (W : Set E).indicator u)
        (((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (W : Set E).indicator u') x)
        x v) := by
  obtain ⟨ρ, hρ0, hball⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := μ) hW₀c hW₀W
  have hWm : NullMeasurableSet (W : Set E) μ := W.isOpen.measurableSet.nullMeasurableSet
  have hu_int := hu.locallyIntegrableOn.integrable_indicator_of_isCompact_closure hWm hWc hWΩ
  have hu'_int :=
    hu.locallyIntegrableOn_deriv.integrable_indicator_of_isCompact_closure hWm hWc hWΩ
  exact ⟨ρ, hρ0, hu_int, hu'_int,
    fun n => ((ρ n).contDiff_normed_convolution hu_int.locallyIntegrable (n := 1)).continuous,
    fun n => ((ρ n).contDiff_normed_convolution hu'_int.locallyIntegrable (n := 1)).continuous,
    fun n x hx => (hu.mono (subset_closure.trans hWΩ)).hasLineDerivAt_normed_convolution_indicator
      hu_int.locallyIntegrable (ρ n) (hball n x hx)⟩

/-- **Endpoint directional weak Leibniz rule for a classically differentiable left factor.** If `f₀`
is continuous on `Ω` and has continuous directional derivative `f'₀` along `v` at every point of
`Ω`, and `g` has weak directional derivative `g'` along `v` on `Ω`, then `B(f₀, g)` has weak
directional derivative `B(f'₀, g) + B(f₀, g')` along `v` on `Ω`. Neither `g` nor `g'` needs any
integrability beyond the local integrability inherent in `HasWeakLineDerivOn`. -/
theorem HasWeakLineDerivOn.bilin_of_hasLineDerivAt_left (B : F →L[ℝ] G →L[ℝ] H)
    {f₀ f'₀ : E → F} (hf₀c : ContinuousOn f₀ Ω) (hf'₀c : ContinuousOn f'₀ Ω)
    (hfd : ∀ x ∈ (Ω : Set E), HasLineDerivAt ℝ f₀ (f'₀ x) x v)
    {g g' : E → G} (hg : HasWeakLineDerivOn μ Ω g g' v) :
    HasWeakLineDerivOn μ Ω (fun x => B (f₀ x) (g x))
      (fun x => B (f'₀ x) (g x) + B (f₀ x) (g' x)) v := by
  have : CompleteSpace G := hg.completeSpace
  rw [hasWeakLineDerivOn_iff_forall_isCompact_closure]
  intro W₀ hW₀c hW₀Ω
  obtain ⟨W, hW₀W, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hW₀c hW₀Ω
  obtain ⟨ρ, hρ0, hg_int, hg'_int, hgm_cont, hg'm_cont, hgm_deriv⟩ :=
    exists_seq_normed_convolution_indicator hW₀c hW₀W hWc hWΩ hg
  let g_m (m : ℕ) :=
    (ρ m).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (W : Set E).indicator g
  let g'_m (m : ℕ) :=
    (ρ m).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (W : Set E).indicator g'
  have hW₀W' : (W₀ : Set E) ⊆ W := subset_closure.trans hW₀W
  have hW₀Ω' : (W₀ : Set E) ⊆ Ω := subset_closure.trans hW₀Ω
  have hf₀W₀ : ContinuousOn f₀ W₀ := hf₀c.mono hW₀Ω'
  have hf'₀W₀ : ContinuousOn f'₀ W₀ := hf'₀c.mono hW₀Ω'
  -- Classical Leibniz rule for `(f₀, g_m)` on `W₀`.
  have hweak_m (m : ℕ) : HasWeakLineDerivOn μ W₀ (fun x => B (f₀ x) (g_m m x))
      (fun x => B (f'₀ x) (g_m m x) + B (f₀ x) (g'_m m x)) v := by
    refine hasWeakLineDerivOn_of_hasLineDerivAt
      ((B.continuous₂.comp_continuousOn (hf₀W₀.prodMk (hgm_cont m).continuousOn)
        ).locallyIntegrableOn W₀.isOpen.measurableSet)
      (((B.continuous₂.comp_continuousOn (hf'₀W₀.prodMk (hgm_cont m).continuousOn)).add
        (B.continuous₂.comp_continuousOn (hf₀W₀.prodMk (hg'm_cont m).continuousOn))
        ).locallyIntegrableOn W₀.isOpen.measurableSet)
      fun x hx => (hfd x (hW₀Ω' hx)).clm_bilin B (hgm_deriv m x hx)
  -- Local integrability of the limit functions and `L¹(W₀)` convergence of `B(f₀, g_m)` and
  -- `B(f'₀, g_m) + B(f₀, g'_m)`.
  have hloc₀ := W₀.isOpen.isLocallyClosed
  have hBf_g := (hg.locallyIntegrableOn.mono_set hW₀Ω').continuousOn_clm_apply
    hloc₀ (B.continuous.comp_continuousOn hf₀W₀)
  have hBf'_g := (hg.locallyIntegrableOn.mono_set hW₀Ω').continuousOn_clm_apply
    hloc₀ (B.continuous.comp_continuousOn hf'₀W₀)
  have hBf_g' := (hg.locallyIntegrableOn_deriv.mono_set hW₀Ω').continuousOn_clm_apply
    hloc₀ (B.continuous.comp_continuousOn hf₀W₀)
  obtain ⟨C₁, hC₁⟩ := hW₀c.exists_bound_of_continuousOn (hf₀c.mono hW₀Ω)
  obtain ⟨C₂, hC₂⟩ := hW₀c.exists_bound_of_continuousOn (hf'₀c.mono hW₀Ω)
  have hC₁' : ∀ x ∈ (W₀ : Set E), ‖f₀ x‖ ≤ C₁ := fun x hx => hC₁ x (subset_closure hx)
  have hC₂' : ∀ x ∈ (W₀ : Set E), ‖f'₀ x‖ ≤ C₂ := fun x hx => hC₂ x (subset_closure hx)
  have hgm_lim := tendsto_setLIntegral_enorm_normed_convolution_indicator_sub hρ0
    W₀.isOpen.measurableSet.nullMeasurableSet hW₀W' hg_int
  have hg'm_lim := tendsto_setLIntegral_enorm_normed_convolution_indicator_sub hρ0
    W₀.isOpen.measurableSet.nullMeasurableSet hW₀W' hg'_int
  have hL₁ := B.tendsto_setLIntegral_enorm_bilin_sub_of_norm_le W₀.isOpen.measurableSet hC₁' hgm_lim
  have hL₂ : Tendsto (fun m => ∫⁻ x in (W₀ : Set E),
      ‖(B (f'₀ x) (g_m m x) + B (f₀ x) (g'_m m x)) -
        (B (f'₀ x) (g x) + B (f₀ x) (g' x))‖ₑ ∂μ) atTop (𝓝 0) :=
    tendsto_setLIntegral_enorm_add_sub
      (a := fun m x => B (f'₀ x) (g_m m x)) (b := fun m x => B (f₀ x) (g'_m m x))
      (fun m => ((B.continuous₂.comp_continuousOn
        (hf'₀W₀.prodMk (hgm_cont m).continuousOn)).aestronglyMeasurable
        W₀.isOpen.measurableSet).sub hBf'_g.aestronglyMeasurable)
      (B.tendsto_setLIntegral_enorm_bilin_sub_of_norm_le W₀.isOpen.measurableSet hC₂' hgm_lim)
      (B.tendsto_setLIntegral_enorm_bilin_sub_of_norm_le W₀.isOpen.measurableSet hC₁' hg'm_lim)
  exact hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub
    hBf_g (hBf'_g.add hBf_g') hweak_m hL₁ hL₂

/-- **Endpoint directional weak Leibniz rule for a continuous left factor.** If `f` is continuous
on `Ω` with weak directional derivative `f'` along `v` that is locally `Lᵖ` on `Ω`, and `g` is
locally `L^q` on `Ω` with weak directional derivative `g'` along `v` (without assuming `g'` is
locally `L^q`), where `p⁻¹ + q⁻¹ ≤ 1` (allowing `p = ∞` or `q = ∞`), then `B(f, g)` has weak
directional derivative `B(f', g) + B(f, g')` along `v`. -/
theorem HasWeakLineDerivOn.bilin_of_continuousOn (B : F →L[ℝ] G →L[ℝ] H)
    {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ ≤ 1) {f f' : E → F} {g g' : E → G}
    (hf : HasWeakLineDerivOn μ Ω f f' v) (hfc : ContinuousOn f Ω)
    (hf'p : ∀ K, IsCompact K → K ⊆ Ω → MemLp f' p (μ.restrict K))
    (hg : HasWeakLineDerivOn μ Ω g g' v)
    (hgq : ∀ K, IsCompact K → K ⊆ Ω → MemLp g q (μ.restrict K)) :
    HasWeakLineDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B (f' x) (g x) + B (f x) (g' x)) v := by
  have : CompleteSpace F := hf.completeSpace
  have : CompleteSpace G := hg.completeSpace
  have hloc := Ω.isOpen.isLocallyClosed
  have hBf : ContinuousOn (fun x => B (f x)) Ω := B.continuous.comp_continuousOn hfc
  have hBfg : LocallyIntegrableOn (fun x => B (f x) (g x)) Ω μ :=
    hg.locallyIntegrableOn.continuousOn_clm_apply hloc hBf
  have hBf'g : LocallyIntegrableOn (fun x => B (f' x) (g x)) Ω μ := by
    let _ := ENNReal.HolderTriple.of p q
    have h1 : 1 ≤ (p⁻¹ + q⁻¹)⁻¹ := ENNReal.one_le_inv.2 hpq
    rw [locallyIntegrableOn_iff hloc]
    intro K hKΩ hK
    have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact (B.memLp_of_bilin (p⁻¹ + q⁻¹)⁻¹ (hf'p K hK hKΩ) (hgq K hK hKΩ)).integrable h1
  have hBfg' : LocallyIntegrableOn (fun x => B (f x) (g' x)) Ω μ :=
    hg.locallyIntegrableOn_deriv.continuousOn_clm_apply hloc hBf
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hBfg, hBf'g.add hBfg', fun φ => ?_⟩
  -- Two-stage mollify-and-pass-to-limit on nested relatively compact neighborhoods `W₀ ⋐ W ⋐ Ω`
  -- around `tsupport φ`.
  obtain ⟨W, hφW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨W₀, hφW₀, hW₀W, hW₀c⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport hφW
  obtain ⟨ρ, hρ0, -, -, hfn_cont, hf'n_cont, hfn_deriv⟩ :=
    exists_seq_normed_convolution_indicator hW₀c hW₀W hWc hWΩ hf
  have hWm : NullMeasurableSet (W : Set E) μ := W.isOpen.measurableSet.nullMeasurableSet
  have hf'W : MemLp f' p (μ.restrict W) :=
    (hf'p _ hWc hWΩ).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have hgW : MemLp g q (μ.restrict W) :=
    (hgq _ hWc hWΩ).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  let f_n (n : ℕ) :=
    (ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (W : Set E).indicator f
  let f'_n (n : ℕ) :=
    (ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (W : Set E).indicator f'
  have hW₀Ω : (W₀ : Set E) ⊆ Ω := subset_closure.trans (hW₀W.trans (subset_closure.trans hWΩ))
  -- Stage 1: mollify `g` and pass `m → ∞` in `L¹(W₀)` to get the weak Leibniz rule for `(f_n, g)`.
  have hweak_n (n : ℕ) : HasWeakLineDerivOn μ W₀ (fun x => B (f_n n x) (g x))
      (fun x => B (f'_n n x) (g x) + B (f_n n x) (g' x)) v :=
    (hg.mono hW₀Ω).bilin_of_hasLineDerivAt_left B (hfn_cont n).continuousOn
      (hf'n_cont n).continuousOn (hfn_deriv n)
  -- Stage 2: test against `φ` and pass `n → ∞` using `f_n → f` uniformly on `tsupport φ` (`ht1`,
  -- `ht3`) and `f'_n → f'` weakly in `Lᵖ(W)` against `φ • g ∈ L^{p'}` (`ht2`).
  let φ₀ : 𝓓(W₀, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφW₀⟩
  have hid (n : ℕ) : (∫ x, fderiv ℝ (φ : E → ℝ) x v • B (f_n n x) (g x) ∂μ) =
      -((∫ x, (φ : E → ℝ) x • B (f'_n n x) (g x) ∂μ) +
        ∫ x, (φ : E → ℝ) x • B (f_n n x) (g' x) ∂μ) := by
    have h := (hweak_n n).integral_lineDeriv_smul_eq_neg_integral_smul φ₀
    have hi1 : Integrable (fun x => (φ : E → ℝ) x • B (f'_n n x) (g x)) μ :=
      φ₀.integrable_smul ((hg.locallyIntegrableOn.mono_set hW₀Ω).continuousOn_clm_apply
        W₀.isOpen.isLocallyClosed (B.continuous.comp_continuousOn (hf'n_cont n).continuousOn))
    have hi2 : Integrable (fun x => (φ : E → ℝ) x • B (f_n n x) (g' x)) μ :=
      φ₀.integrable_smul ((hg.locallyIntegrableOn_deriv.mono_set hW₀Ω).continuousOn_clm_apply
        W₀.isOpen.isLocallyClosed (B.continuous.comp_continuousOn (hfn_cont n).continuousOn))
    simp only [φ₀, TestFunction.coe_mk, smul_add] at h
    simp only [TestFunction.lineDeriv_eq_fderiv] at h
    rwa [integral_add hi1 hi2] at h
  have hunif : TendstoUniformlyOn f_n f atTop (tsupport (φ : E → ℝ)) :=
    ContDiffBump.tendstoUniformlyOn_normed_convolution_indicator (μ := μ) hρ0 W.isOpen
      φ.hasCompactSupport hφW (hfc.mono (subset_closure.trans hWΩ))
  let P : ℝ →L[ℝ] H →L[ℝ] H := ContinuousLinearMap.lsmul ℝ ℝ
  have ht1 : Tendsto (fun n => ∫ x, fderiv ℝ (φ : E → ℝ) x v • B (f_n n x) (g x) ∂μ)
      atTop (𝓝 (∫ x, fderiv ℝ (φ : E → ℝ) x v • B (f x) (g x) ∂μ)) := by
    simpa only [P, TestFunction.lineDerivOp_apply_eq_fderiv, ContinuousLinearMap.lsmul_apply,
        Function.comp_apply] using
      (∂_{v} φ).tendsto_integral_bilin_clm_of_tendstoUniformlyOn P hg.locallyIntegrableOn
        (.of_forall fun n => B.continuous.comp_continuousOn (hfn_cont n).continuousOn)
        (B.uniformContinuous.comp_tendstoUniformlyOn (hunif.mono (φ.tsupport_lineDerivOp_subset v)))
  have ht3 : Tendsto (fun n => ∫ x, (φ : E → ℝ) x • B (f_n n x) (g' x) ∂μ)
      atTop (𝓝 (∫ x, (φ : E → ℝ) x • B (f x) (g' x) ∂μ)) := by
    simpa only [P, ContinuousLinearMap.lsmul_apply, Function.comp_apply] using
      φ.tendsto_integral_bilin_clm_of_tendstoUniformlyOn P hg.locallyIntegrableOn_deriv
        (.of_forall fun n => B.continuous.comp_continuousOn (hfn_cont n).continuousOn)
        (B.uniformContinuous.comp_tendstoUniformlyOn hunif)
  have ht2 : Tendsto (fun n => ∫ x, (φ : E → ℝ) x • B (f'_n n x) (g x) ∂μ)
      atTop (𝓝 (∫ x, (φ : E → ℝ) x • B (f' x) (g x) ∂μ)) := by
    simpa only [P, f'_n, ContinuousLinearMap.lsmul_apply] using
      φ.tendsto_integral_bilin_normed_convolution P B hpq hWm hφW hf'W hgW hρ0
  have hrhs := (ht2.add ht3).neg
  have heq : (fun x => (φ : E → ℝ) x • (B (f' x) (g x) + B (f x) (g' x))) =
      fun x => (φ : E → ℝ) x • B (f' x) (g x) + (φ : E → ℝ) x • B (f x) (g' x) :=
    funext fun x => smul_add _ _ _
  rw [heq, integral_add (φ.integrable_smul hBf'g) (φ.integrable_smul hBfg')]
  simp only [TestFunction.lineDeriv_eq_fderiv]
  exact tendsto_nhds_unique (ht1.congr fun n => hid n) hrhs

end Endpoint

end TauCeti
