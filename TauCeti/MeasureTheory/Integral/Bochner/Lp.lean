/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import TauCeti.MeasureTheory.Function.Lp.Complete
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.SimpleFunc.Basic
import TauCeti.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Integrating representatives of Lᵖ curves

On a σ-finite sample measure, an integrable curve in `Lp E p`, with `1 ≤ p ≤ ∞` and
Banach codomain `E`, can be integrated samplewise whenever its representatives are jointly
almost everywhere strongly measurable. The resulting ordinary integral represents the
Bochner integral in `Lp E p`. This connects mean-square process integrals to ordinary
time integrals, and `Lᵖ`-valued integrals of evolution semigroups on `ℝⁿ` to pointwise
integrals, without treating point evaluation as a continuous functional on `Lᵖ`. On a finite
sample measure the representatives are moreover jointly integrable, and on a σ-finite one almost
every sample function `t ↦ X t ω` is integrable.

Such representatives always exist. An integrable curve `F` in `Lp E p P` has a jointly strongly
measurable representative `X`, with `F t = X (t, ·)` almost everywhere for almost every `t`, whose
sample functions are integrable and integrate to the Bochner integral of `F` at almost every sample
point. This holds for arbitrary measures when `p < ∞`, and for an arbitrary parameter measure and
a σ-finite sample measure when `p = ∞`. The representative is the pointwise limit of the joint
functions `(t, ω) ↦ G k t ω` of simple approximants `G k` of `F` converging at a summable rate in
`L¹`, as in the proof of the Riesz–Fischer theorem. Both measures can then be restricted to
σ-finite pieces carrying `F` and its representative.

## Main results

* `MeasureTheory.Integrable.coeFn_integral_Lp`: on a σ-finite sample measure, the samplewise
  integral of a jointly measurable representative represents the Bochner integral.
* `MeasureTheory.Integrable.ae_integrable_of_ae_eq_Lp`: on a σ-finite sample measure, almost
  every sample function of a jointly measurable representative is integrable.
* `MeasureTheory.Integrable.exists_integral_Lp_representative`: every integrable curve in `Lᵖ` has
  a jointly strongly measurable representative whose samplewise integrals represent its Bochner
  integral.

## References

* Hytönen, van Neerven, Veraar and Weis, *Analysis in Banach Spaces*, Volume I,
  Proposition 1.2.25 and Remark 1.2.26, pp. 26–27.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory

/-- Testing against a bounded measurable multiplier preserves convergence of the
integrals along an `L¹`-convergent family. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm {α : Type*} [MeasurableSpace α]
    {ι : Type*} {l : Filter ι} {ν : Measure α} {u : ι → α → ℝ} {v f : α → ℝ}
    (hu : ∀ᶠ i in l, Integrable (u i) ν)
    (hv : Integrable v ν) (hf : AEStronglyMeasurable f ν) {B : ℝ} (hB : ∀ᵐ x ∂ν, ‖f x‖ ≤ B)
    (h : Tendsto (fun n ↦ eLpNorm (u n - v) 1 ν) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, f x * u n x ∂ν) l (𝓝 (∫ x, f x * v x ∂ν)) := by
  have hF : ∀ᶠ i in l, Integrable (fun x ↦ f x * u i x) ν :=
    hu.mono fun _ hi ↦ hi.bdd_mul hf hB
  have hG : Integrable (fun x ↦ f x * v x) ν := hv.bdd_mul hf hB
  refine tendsto_integral_of_L1' _ hF ?_
  have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B) h (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [mul_zero] using hmul)
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hu, hF] with i hi hiF
  rw [eLpNorm_one_eq_lintegral_eNorm (hiF.sub hG).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm (hi.sub hv).aestronglyMeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hB] with x hx
  simp only [Pi.sub_apply, ← mul_sub, eNorm_mul]
  gcongr
  exact (Real.eNorm_eq_ofReal_abs _).le.trans (ENNReal.ofReal_le_ofReal hx)

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {μ : Measure α} {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : α → Lp E p P} {X : α → Ω → E}

/-- Jointly measurable representatives of an integrable Lᵖ curve, with `1 ≤ p ≤ ∞`,
are integrable on the product of the parameter measure and a finite sample measure. -/
theorem Integrable.integrable_uncurry_of_ae_eq_Lp [IsFiniteMeasure P] (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    Integrable (Function.uncurry X) (μ.prod P) := by
  refine (integrable_prod_iff hX).2 ⟨?_, ?_⟩
  · filter_upwards [heq] with t ht
    exact ((Lp.memLp (F t)).integrable Fact.out).congr ht
  · refine (hF.norm.const_mul
      ((P Set.univ ^ (1 - 1 / p.toReal)).toReal)).mono'
      hX.norm.integral_prod_right' ?_
    filter_upwards [heq] with t ht
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      ← integral_congr_ae (ht.mono fun ω hω ↦ congrArg (‖·‖) hω)]
    exact Lp.integral_norm_le_mul_norm (F t)

/-- A jointly strongly measurable representative of an integrable curve in `Lp E p P`. For finite
`p` it vanishes outside a set of samples on which `P` is σ-finite. -/
private theorem Integrable.exists_stronglyMeasurable_ae_eq_Lp [CompleteSpace E]
    (hF : Integrable F μ) :
    ∃ X : α × Ω → E, StronglyMeasurable X ∧ (∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] fun ω ↦ X (t, ω)) ∧
      (p ≠ ∞ → ∃ T, MeasurableSet T ∧ SigmaFinite (P.restrict T) ∧
        ∀ z : α × Ω, z.2 ∉ T → X z = 0) := by
  -- Simple functions `G k` with `‖G k - F‖_{L¹} < 2⁻ᵏ` converge to `F` at a summable rate.
  choose G hG using fun k : ℕ ↦ (memLp_one_iff_integrable.2 hF).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (ε := 2⁻¹ ^ k) (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
  have hsum : ∀ᵐ t ∂μ, ∑' k, ‖G k t - F t‖ₑ < ∞ := by
    refine TauCeti.ae_tsum_lt_top_of_eLpNorm_le le_rfl (b := fun k ↦ 2⁻¹ ^ k)
      (tsum_geometric_lt_top.2 (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)).ne fun k ↦ ?_
    have h := eLpNorm_eNorm (p := 1) _ ((G k).aestronglyMeasurable.sub hF.1)
    simp only [Pi.sub_apply] at h
    rw [h, eLpNorm_sub_comm]
    exact (hG k).1.le
  -- The joint functions `(t, ω) ↦ G k t ω` are strongly measurable, and so is their limit.
  set g : ℕ → α × Ω → E := fun k ↦ Function.uncurry ((fun y : Lp E p P ↦ ⇑y) ∘ G k)
  have hg (k : ℕ) : StronglyMeasurable (g k) :=
    (G k).stronglyMeasurable_uncurry_comp Lp.stronglyMeasurable
  refine ⟨fun z ↦ limUnder atTop (g · z), StronglyMeasurable.limUnder hg, ?_, fun hp ↦ ?_⟩
  · filter_upwards [hsum] with t ht
    have hlim := TauCeti.ae_tendsto_of_tsum_eLpNorm_sub_ne_top (μ := P) (p := p) Fact.out
      (f := fun k ↦ ⇑(G k t)) (g := ⇑(F t)) (fun _ ↦ Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _) (by simpa only [← Lp.edist_def, eDist_eq_eNorm_sub] using ht.ne)
    filter_upwards [hlim] with ω hω
    exact hω.limUnder_eq.symm
  · -- Every value of every `G k` vanishes off the supports of its finite-support approximants.
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
    have hfin (y : Lp E p P) := Lp.finStronglyMeasurable y hp0 hp
    let A : (Σ k, (G k).range) × ℕ → Set Ω := fun i ↦ Function.support ((hfin i.1.2).approx i.2)
    refine ⟨⋃ i, A i, .iUnion fun i ↦ SimpleFunc.measurableSet_support _,
      P.sigmaFinite_restrict_iUnion A fun i ↦ (hfin _).fin_support_approx _, fun z hz ↦ ?_⟩
    have hzero (k : ℕ) : g k z = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ : ∃ n, (hfin (G k z.1)).approx n z.2 ≠ 0 := by
        by_contra! h
        exact hne (tendsto_nhds_unique ((hfin (G k z.1)).tendsto_approx z.2) (by simp [h]))
      exact hz (Set.mem_iUnion.2 ⟨(⟨k, G k z.1, (G k).mem_range_self z.1⟩, n), hn⟩)
    simp only [hzero]
    exact tendsto_const_nhds.limUnder_eq

section SFinite

variable [SFinite μ] [NormedSpace ℝ E] [CompleteSpace E]

/-- The case of a finite sample measure of `MeasureTheory.Integrable.coeFn_integral_Lp`. -/
private theorem Integrable.coeFn_integral_Lp_of_isFiniteMeasure [IsFiniteMeasure P]
    (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    ⇑(∫ t, F t ∂μ) =ᵐ[P] fun ω ↦ ∫ t, X t ω ∂μ := by
  have hi := hF.integrable_uncurry_of_ae_eq_Lp hX heq
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable Fact.out) hi.integral_prod_right fun s hs _ ↦ ?_
  let q := ENNReal.conjExponent p
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let c := indicatorConstLp q hs (measure_ne_top P s) (1 : ℝ)
  let L := ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip.lpPairing P p q).flip c
  have hL (f : Lp E p P) : L f = ∫ ω in s, f ω ∂P := by
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral,
      ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs)
      (hμs := measure_ne_top P s) (c := (1 : ℝ))] with ω hω
    by_cases hmem : ω ∈ s <;> simp [c, hω, hmem]
  rw [← hL, ← L.integral_comp_comm hF]
  have hi' : Integrable (Function.uncurry X) (μ.prod (P.restrict s)) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [← integral_integral_swap hi']
  refine integral_congr_ae ?_
  filter_upwards [heq] with t ht
  rw [hL]
  exact integral_congr_ae (ae_restrict_of_ae ht)

/-- The ordinary samplewise integral of jointly measurable representatives of an
integrable Lᵖ curve, with `1 ≤ p ≤ ∞`, represents its Lᵖ-valued Bochner integral, on a
σ-finite sample measure. -/
theorem Integrable.coeFn_integral_Lp [SigmaFinite P] (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    ⇑(∫ t, F t ∂μ) =ᵐ[P] fun ω ↦ ∫ t, X t ω ∂μ := by
  -- On a set `s` of finite measure, restrict the curve to `Lp E p (P.restrict s)`.
  refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs ↦ ?_
  have _ : IsFiniteMeasure (P.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  set R := LpToLpRestrictCLM Ω E ℝ P p s
  have h := (R.integrable_comp hF).coeFn_integral_Lp_of_isFiniteMeasure
    (hX.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)) <| by
      filter_upwards [heq] with t ht
      exact (LpToLpRestrictCLM_coeFn ℝ s (F t)).trans (ae_restrict_of_ae ht)
  rw [R.integral_comp_comm hF] at h
  exact (LpToLpRestrictCLM_coeFn ℝ s _).symm.trans h

omit [CompleteSpace E] in
/-- Almost every sample function `t ↦ X t ω` of jointly measurable representatives of an integrable
Lᵖ curve, with `1 ≤ p ≤ ∞`, is integrable, on a σ-finite sample measure. -/
theorem Integrable.ae_integrable_of_ae_eq_Lp [SigmaFinite P] (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    ∀ᵐ ω ∂P, Integrable (fun t ↦ X t ω) μ := by
  -- On a set `s` of finite measure, restrict the curve to `Lp E p (P.restrict s)`.
  refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs ↦ ?_
  have _ : IsFiniteMeasure (P.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  set R := LpToLpRestrictCLM Ω E ℝ P p s
  refine Integrable.prod_left_ae (f := Function.uncurry X) ?_
  refine (R.integrable_comp hF).integrable_uncurry_of_ae_eq_Lp
    (hX.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)) ?_
  filter_upwards [heq] with t ht
  exact (LpToLpRestrictCLM_coeFn ℝ s (F t)).trans (ae_restrict_of_ae ht)

end SFinite

/-- The samplewise integrals of a representative vanishing outside `S × Ω` represent the integral
on a set `T` of samples, when `F` vanishes almost everywhere outside `S` and `μ.restrict S`,
`P.restrict T` are σ-finite. -/
private theorem Integrable.ae_restrict_integral_Lp_eq [NormedSpace ℝ E] [CompleteSpace E]
    (hF : Integrable F μ) {S : Set α} {T : Set Ω} [SigmaFinite (μ.restrict S)]
    [SigmaFinite (P.restrict T)] (hFS : ∀ᵐ t ∂μ, t ∉ S → F t = 0) {X : α × Ω → E}
    (hX : StronglyMeasurable X) (hXS : ∀ t ω, t ∉ S → X (t, ω) = 0)
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] fun ω ↦ X (t, ω)) :
    ∀ᵐ ω ∂P.restrict T,
      Integrable (fun t ↦ X (t, ω)) μ ∧ (∫ t, F t ∂μ) ω = ∫ t, X (t, ω) ∂μ := by
  set R := LpToLpRestrictCLM Ω E ℝ P p T
  have hRF : Integrable (fun t ↦ R (F t)) (μ.restrict S) := (R.integrable_comp hF).restrict
  have hX' : AEStronglyMeasurable (Function.uncurry (Function.curry X))
      ((μ.restrict S).prod (P.restrict T)) := by
    rw [Function.uncurry_curry]
    exact hX.aestronglyMeasurable
  have heq' : ∀ᵐ t ∂μ.restrict S, ⇑(R (F t)) =ᵐ[P.restrict T] Function.curry X t := by
    refine ae_restrict_of_ae ?_
    filter_upwards [heq] with t ht
    exact (LpToLpRestrictCLM_coeFn ℝ T (F t)).trans (ae_restrict_of_ae ht)
  have hRint : ∫ t in S, R (F t) ∂μ = R (∫ t, F t ∂μ) := by
    rw [R.integral_comp_comm hF.integrableOn, setIntegral_eq_integral_of_ae_compl_eq_zero hFS]
  filter_upwards [hRF.coeFn_integral_Lp hX' heq', hRF.ae_integrable_of_ae_eq_Lp hX' heq',
    LpToLpRestrictCLM_coeFn ℝ T (∫ t, F t ∂μ)] with ω h1 h2 h3
  refine ⟨(integrableOn_iff_integrable_of_support_subset fun t ht ↦ ?_).1 h2, ?_⟩
  · by_contra hS
    exact ht (hXS t ω hS)
  · rw [← h3, ← hRint, h1]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ hXS t ω ht

/-- Off a measurable set `T` of samples outside of which a representative vanishes, its samplewise
integrals vanish, and so does the integral of `F`. -/
private theorem Integrable.ae_restrict_compl_integral_Lp_eq [NormedSpace ℝ E] [CompleteSpace E]
    (hF : Integrable F μ) {T : Set Ω} (hT : MeasurableSet T) {X : α × Ω → E}
    (hXT : ∀ t ω, ω ∉ T → X (t, ω) = 0) (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] fun ω ↦ X (t, ω)) :
    ∀ᵐ ω ∂P.restrict Tᶜ,
      Integrable (fun t ↦ X (t, ω)) μ ∧ (∫ t, F t ∂μ) ω = ∫ t, X (t, ω) ∂μ := by
  set R := LpToLpRestrictCLM Ω E ℝ P p Tᶜ
  have hzero : (fun t ↦ R (F t)) =ᵐ[μ] 0 := by
    filter_upwards [heq] with t ht
    rw [Pi.zero_apply, Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ Tᶜ (F t), ae_restrict_of_ae ht,
      ae_restrict_mem hT.compl] with ω h1 h2 h3
    rw [h1, h2, hXT t ω h3, Pi.zero_apply]
  have hR0 : R (∫ t, F t ∂μ) = 0 := by
    rw [← R.integral_comp_comm hF, integral_eq_zero_of_ae hzero]
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ Tᶜ (∫ t, F t ∂μ), ae_restrict_mem hT.compl,
    Lp.coeFn_zero E p (P.restrict Tᶜ)] with ω h1 h2 h3
  simp only [(hXT · ω h2), integral_zero]
  exact ⟨integrable_zero _ _ _, by rw [← h1, hR0, h3, Pi.zero_apply]⟩

/-- **Jointly measurable representatives of `Lᵖ`-valued integrals.** An integrable curve `F` in
`Lp E p P`, with `1 ≤ p ≤ ∞` and Banach codomain `E`, has a jointly strongly measurable
representative `X`: `F t = X (t, ·)` almost everywhere for almost every `t`. At almost every
sample point `ω` the function `t ↦ X (t, ω)` is integrable and its integral is the value at `ω` of
the Bochner integral of `F`. The parameter measure `μ` is arbitrary; the sample measure `P` is
arbitrary when `p < ∞` and σ-finite when `p = ∞`. -/
theorem Integrable.exists_integral_Lp_representative [NormedSpace ℝ E] [CompleteSpace E]
    (hF : Integrable F μ) (hpP : p ≠ ∞ ∨ SigmaFinite P) :
    ∃ X : α × Ω → E, StronglyMeasurable X ∧ (∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] fun ω ↦ X (t, ω)) ∧
      ∀ᵐ ω ∂P, Integrable (fun t ↦ X (t, ω)) μ ∧ (∫ t, F t ∂μ) ω = ∫ t, X (t, ω) ∂μ := by
  obtain ⟨X₀, hX₀, heq₀, hsupp⟩ := hF.exists_stronglyMeasurable_ae_eq_Lp
  -- A set of samples `T` with `P.restrict T` σ-finite, outside of which `X₀` vanishes.
  obtain ⟨T, hT, hTσ, hX₀T⟩ : ∃ T, MeasurableSet T ∧ SigmaFinite (P.restrict T) ∧
      ∀ z : α × Ω, z.2 ∉ T → X₀ z = 0 := by
    rcases hpP with hp | hP
    · exact hsupp hp
    · exact ⟨Set.univ, .univ, inferInstance, fun z hz ↦ absurd (Set.mem_univ _) hz⟩
  -- A set of parameters `S` with `μ.restrict S` σ-finite, outside of which `F` vanishes a.e.
  have hFfin := hF.aefinStronglyMeasurable
  have hS : MeasurableSet hFfin.sigmaFiniteSet := hFfin.measurableSet
  have := hFfin.sigmaFinite_restrict
  have hFS : ∀ᵐ t ∂μ, t ∉ hFfin.sigmaFiniteSet → F t = 0 :=
    (ae_restrict_iff' hS.compl).1 hFfin.ae_eq_zero_compl
  -- The representative is `X₀` cut down to `S × Ω`.
  set X : α × Ω → E := (hFfin.sigmaFiniteSet ×ˢ Set.univ).indicator X₀ with hXdef
  have hXS (t : α) (ω : Ω) (ht : t ∉ hFfin.sigmaFiniteSet) : X (t, ω) = 0 :=
    Set.indicator_of_notMem (by simp [ht]) _
  have hXT (t : α) (ω : Ω) (hω : ω ∉ T) : X (t, ω) = 0 := by
    by_cases ht : t ∈ hFfin.sigmaFiniteSet
    · rw [hXdef, Set.indicator_of_mem (by simp [ht])]
      exact hX₀T _ hω
    · exact hXS t ω ht
  have hXm : StronglyMeasurable X := hX₀.indicator (hS.prod .univ)
  have heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] fun ω ↦ X (t, ω) := by
    filter_upwards [heq₀, hFS] with t ht htS
    by_cases h : t ∈ hFfin.sigmaFiniteSet
    · simpa [hXdef, h] using ht
    · rw [htS h]
      filter_upwards [Lp.coeFn_zero E p P] with ω hω
      rw [hω, hXS t ω h, Pi.zero_apply]
  refine ⟨X, hXm, heq, ?_⟩
  filter_upwards [(ae_restrict_iff' hT).1 (hF.ae_restrict_integral_Lp_eq hFS hXm hXS heq),
    (ae_restrict_iff' hT.compl).1 (hF.ae_restrict_compl_integral_Lp_eq hT hXT heq)] with ω h1 h2
  by_cases hω : ω ∈ T
  exacts [h1 hω, h2 hω]

end MeasureTheory
