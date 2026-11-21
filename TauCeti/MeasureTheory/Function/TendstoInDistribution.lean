/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Measure.Portmanteau

/-!
# Filter operations, law congruence, and Slutsky without separability

Mathlib defines `MeasureTheory.TendstoInDistribution X l Z μ μ'` along an arbitrary filter `l`,
packaging pointwise almost-everywhere measurability together with weak convergence of the laws in
`MeasureTheory.ProbabilityMeasure`. This file supplies basic filter operations (precomposition,
monotonicity, eventual almost-everywhere congruence, sequential characterization), law-invariance
and identity-limit adapters, and Slutsky's convergence-in-distribution replacement lemma without
second countability or Borel-space assumptions.

## Main statements

* `MeasureTheory.TendstoInDistribution.comp_tendsto` — precompose the index along a filter limit.
* `MeasureTheory.TendstoInDistribution.mono_left` — weaken the index filter.
* `MeasureTheory.TendstoInDistribution.congr'` — replace random variables eventually almost
  everywhere along the index filter.
* `MeasureTheory.tendstoInDistribution_iff_forall_seq_tendsto` — along a countably generated filter,
  convergence in distribution is equivalent to convergence in distribution along every sequence
  tending to the filter.
* `MeasureTheory.TendstoInDistribution.of_map_eq` and
  `MeasureTheory.tendstoInDistribution_congr_map` — convergence in distribution depends on the limit
  random variable only through its law.
* `MeasureTheory.tendstoInDistribution_id_iff` — convergence in distribution to the identity on
  `(E, ν)` is pointwise almost-everywhere measurability plus weak convergence of the pushforward
  laws to `ν`.
* `MeasureTheory.TendstoInDistribution.congr_of_tendstoInMeasure_dist` and
  `MeasureTheory.TendstoInDistribution.congr_of_tendstoInMeasure_sub` — Slutsky's replacement lemma
  along an arbitrary filter for any pseudometric space or seminormed group with opens-measurable
  structure, without second countability or Borel-space assumptions.

## Source

* `MeasureTheory.TendstoInDistribution.congr_of_tendstoInMeasure_dist` (and its helper
  `abs_integral_map_sub_le_of_lipschitz`) is adapted from Mathlib's proof of
  `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`
  (`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`), splitting the integral on a
  null-measurable Lipschitz deviation event instead of `{δ ≤ ‖Y - X‖}` and replacing Mathlib's
  countably generated Lipschitz portmanteau theorem with
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto`.

## References

* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Theorem 2.1 and
  Theorem 3.1.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §2, Lemma 2.8.
-/

public section

open Filter
open scoped Topology

namespace MeasureTheory

variable {ι κ E Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]

/-- Precomposing the index of a family of random variables with a function tending to `l` preserves
convergence in distribution. -/
protected theorem TendstoInDistribution.comp_tendsto {l : Filter ι} {l' : Filter κ}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {f : κ → ι}
    (h : TendstoInDistribution X l Z μ μ') (hf : Tendsto f l' l) :
    TendstoInDistribution (fun k ↦ X (f k)) l' Z (fun k ↦ μ (f k)) μ' where
  forall_aemeasurable k := h.forall_aemeasurable (f k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hf

/-- Convergence in distribution is monotone in the index filter. -/
protected theorem TendstoInDistribution.mono_left {l₁ l₂ : Filter ι}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l₂ Z μ μ') (hl : l₁ ≤ l₂) :
    TendstoInDistribution X l₁ Z μ μ' :=
  h.comp_tendsto (tendsto_id'.2 hl)

/-- Convergence in distribution is preserved when the random variables are modified on null sets
eventually along the index filter and at the limit. Pointwise almost-everywhere measurability of
the replacement family is required at all indices because `TendstoInDistribution` records it
globally. -/
protected theorem TendstoInDistribution.congr' {l : Filter ι}
    {X Y : (i : ι) → Ω i → E} {Z T : Ω' → E}
    (h : TendstoInDistribution X l Z μ μ') (hY : ∀ i, AEMeasurable (Y i) (μ i))
    (hXY : ∀ᶠ i in l, X i =ᵐ[μ i] Y i) (hZT : Z =ᵐ[μ'] T) :
    TendstoInDistribution Y l T μ μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    have hlim : (⟨μ'.map Z, inferInstance⟩ : ProbabilityMeasure E) = ⟨μ'.map T, inferInstance⟩ :=
      Subtype.ext (Measure.map_congr hZT)
    rw [← hlim]
    refine h.tendsto.congr' ?_
    filter_upwards [hXY] with i hi
    exact Subtype.ext (Measure.map_congr hi)

/-- Along a countably generated filter, convergence in distribution is equivalent to convergence in
distribution along every sequence tending to that filter. -/
theorem tendstoInDistribution_iff_forall_seq_tendsto {l : Filter ι} [l.IsCountablyGenerated]
    {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ u : ℕ → ι, Tendsto u atTop l →
        TendstoInDistribution (fun n ↦ X (u n)) atTop Z (fun n ↦ μ (u n)) μ' where
  mp h _ hu := h.comp_tendsto hu
  mpr h :=
    { forall_aemeasurable := hX
      aemeasurable_limit := hZ
      tendsto := tendsto_iff_seq_tendsto.2 fun u hu ↦ (h u hu).tendsto }

/-- Convergence in distribution depends on the limit random variable only through its law. -/
protected theorem TendstoInDistribution.of_map_eq {Ω'' : Type*} [MeasurableSpace Ω'']
    {μ'' : Measure Ω''} [IsProbabilityMeasure μ''] {l : Filter ι}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {W : Ω'' → E}
    (h : TendstoInDistribution X l Z μ μ') (hW : AEMeasurable W μ'')
    (heq : μ'.map Z = μ''.map W) :
    TendstoInDistribution X l W μ μ'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hW
  tendsto := by
    have hlim : (⟨μ'.map Z, inferInstance⟩ : ProbabilityMeasure E) =
        ⟨μ''.map W, inferInstance⟩ := Subtype.ext heq
    rw [← hlim]
    exact h.tendsto

/-- Two almost-everywhere measurable limit random variables with the same law determine the same
convergence-in-distribution predicate. -/
theorem tendstoInDistribution_congr_map {Ω'' : Type*} [MeasurableSpace Ω'']
    {μ'' : Measure Ω''} [IsProbabilityMeasure μ''] {l : Filter ι}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {W : Ω'' → E}
    (hZ : AEMeasurable Z μ') (hW : AEMeasurable W μ'') (heq : μ'.map Z = μ''.map W) :
    TendstoInDistribution X l Z μ μ' ↔ TendstoInDistribution X l W μ μ'' :=
  ⟨fun h ↦ h.of_map_eq hW heq, fun h ↦ h.of_map_eq hZ heq.symm⟩

/-- Convergence in distribution to the identity on `(E, ν)` is equivalent to pointwise
almost-everywhere measurability together with weak convergence of the pushforward laws to `ν` in
`ProbabilityMeasure E`. -/
theorem tendstoInDistribution_id_iff {l : Filter ι} {X : (i : ι) → Ω i → E}
    {ν : Measure E} [IsProbabilityMeasure ν] :
    TendstoInDistribution X l id μ ν ↔
      (∀ i, AEMeasurable (X i) (μ i)) ∧
        Tendsto (β := ProbabilityMeasure E) (fun i ↦ ⟨(μ i).map (X i), inferInstance⟩) l
          (𝓝 ⟨ν, inferInstance⟩) := by
  have hlim : (⟨ν.map id, inferInstance⟩ : ProbabilityMeasure E) = ⟨ν, inferInstance⟩ :=
    Subtype.ext Measure.map_id
  constructor
  · intro h
    exact ⟨h.forall_aemeasurable, hlim ▸ h.tendsto⟩
  · rintro ⟨hX, ht⟩
    exact
      { forall_aemeasurable := hX
        aemeasurable_limit := measurable_id.aemeasurable
        tendsto := hlim.symm ▸ ht }

/-- For a bounded `L`-Lipschitz `F : E → ℝ`, the integral difference between the pushforwards of `Y`
and `X` is bounded without assuming measurability of `dist (Y ·) (X ·)`: we split on the
null-measurable set where `L * δ < |F (Y ω) - F (X ω)|`, which lies inside `{δ ≤ dist (Y ω) (X ω)}`
whenever `0 < L`. -/
private theorem abs_integral_map_sub_le_of_lipschitz
    {E Ω'' : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace Ω''] {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {X Y : Ω'' → E} (hX : AEMeasurable X μ'') (hY : AEMeasurable Y μ'')
    {F : E → ℝ} {M : ℝ} (hF_bd : ∀ x y, dist (F x) (F y) ≤ M)
    {L : NNReal} (hL : 0 < L) (hF_lip : LipschitzWith L F) {δ : ℝ} (hδ : 0 < δ) :
    |∫ x, F x ∂(μ''.map Y) - ∫ x, F x ∂(μ''.map X)| ≤
      (L : ℝ) * δ + M * μ''.real {ω | δ ≤ dist (Y ω) (X ω)} := by
  have hF_meas : Measurable F := hF_lip.continuous.measurable
  have hFY_meas : AEStronglyMeasurable (fun ω ↦ F (Y ω)) μ'' :=
    (hF_meas.comp_aemeasurable hY).aestronglyMeasurable
  have hFX_meas : AEStronglyMeasurable (fun ω ↦ F (X ω)) μ'' :=
    (hF_meas.comp_aemeasurable hX).aestronglyMeasurable
  have hne : Nonempty Ω'' := nonempty_of_isProbabilityMeasure μ''
  let x₀ : E := X hne.some
  have hM_nonneg : 0 ≤ M := dist_nonneg.trans (hF_bd x₀ x₀)
  have h_int (W : Ω'' → E) (hW : AEStronglyMeasurable (fun ω ↦ F (W ω)) μ'') :
      Integrable (fun ω ↦ F (W ω)) μ'' := by
    refine Integrable.of_bound hW (‖F x₀‖ + M) (ae_of_all _ fun ω ↦ ?_)
    have h1 := hF_bd (W ω) x₀
    rw [Real.dist_eq] at h1
    linarith [abs_sub_abs_le_abs_sub (F (W ω)) (F x₀), Real.norm_eq_abs (F (W ω)),
      Real.norm_eq_abs (F x₀)]
  have h_int_Y := h_int Y hFY_meas
  have h_int_X := h_int X hFX_meas
  have h_int_sub : Integrable (fun ω ↦ ‖F (Y ω) - F (X ω)‖) μ'' := (h_int_Y.sub h_int_X).norm
  let S : Set Ω'' := {ω | (L : ℝ) * δ < ‖F (Y ω) - F (X ω)‖}
  have hS : NullMeasurableSet S μ'' :=
    nullMeasurableSet_lt aemeasurable_const (hFY_meas.sub hFX_meas).norm.aemeasurable
  have hS_sub : S ⊆ {ω | δ ≤ dist (Y ω) (X ω)} := by
    intro ω hω
    have hlip := hF_lip.dist_le_mul (Y ω) (X ω)
    rw [Real.dist_eq, ← Real.norm_eq_abs] at hlip
    exact ((mul_lt_mul_iff_right₀ (NNReal.coe_pos.2 hL)).1
      ((Set.mem_ofPred_eq.mp hω).trans_le hlip)).le
  rw [integral_map hY hF_meas.stronglyMeasurable.aestronglyMeasurable,
    integral_map hX hF_meas.stronglyMeasurable.aestronglyMeasurable,
    ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
  calc ‖∫ ω, F (Y ω) - F (X ω) ∂μ''‖
      ≤ ∫ ω, ‖F (Y ω) - F (X ω)‖ ∂μ'' := norm_integral_le_integral_norm _
    _ = ∫ ω in S, ‖F (Y ω) - F (X ω)‖ ∂μ'' + ∫ ω in Sᶜ, ‖F (Y ω) - F (X ω)‖ ∂μ'' :=
        (integral_add_compl₀ hS h_int_sub).symm
    _ ≤ ∫ _ in S, M ∂μ'' + ∫ _ in Sᶜ, (L : ℝ) * δ ∂μ'' := by
        gcongr ?_ + ?_
        · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun ω ↦ ?_
          simpa only [Real.norm_eq_abs, ← Real.dist_eq] using hF_bd (Y ω) (X ω)
        · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const hS.compl
            fun ω hω ↦ not_lt.1 hω
    _ = M * μ''.real S + (L : ℝ) * δ * μ''.real Sᶜ := by
        simp only [setIntegral_const, smul_eq_mul]
        ring
    _ ≤ M * μ''.real {ω | δ ≤ dist (Y ω) (X ω)} + (L : ℝ) * δ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left (measureReal_mono hS_sub) hM_nonneg)
          (mul_le_mul_of_nonneg_left measureReal_le_one (by positivity))
    _ = (L : ℝ) * δ + M * μ''.real {ω | δ ≤ dist (Y ω) (X ω)} := by ring

/-- **Slutsky's convergence-in-distribution replacement lemma without separability**, for a general
pseudometric space and arbitrary filter `l`. If `X i → Z` in distribution and
`dist (Y i) (X i) → 0` in probability, with `Y i` almost-everywhere measurable, then `Y i → Z` in
distribution. Adapted from Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub` using
`ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto`, dropping
`SecondCountableTopology`, `BorelSpace`, and countable generation of `l`. -/
protected theorem TendstoInDistribution.congr_of_tendstoInMeasure_dist
    {E Ω'' : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace Ω''] {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {l : Filter ι} {X Y : ι → Ω'' → E} {Z : Ω' → E}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : ∀ i, AEMeasurable (Y i) μ'')
    (hXY : TendstoInMeasure μ'' (fun i ω ↦ dist (Y i ω) (X i ω)) l (fun _ ↦ 0)) :
    TendstoInDistribution Y l Z (fun _ ↦ μ'') μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := hXZ.aemeasurable_limit
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto.2
    rintro F ⟨M, hF_bd⟩ ⟨L, hF_lip⟩
    obtain rfl | hL := eq_zero_or_pos L
    · have hne : Nonempty Ω' := nonempty_of_isProbabilityMeasure μ'
      have hconst : ∀ x, F x = F (Z hne.some) :=
        fun x ↦ (LipschitzWith.zero_iff F).1 hF_lip x (Z hne.some)
      simp only [hconst, integral_const, smul_eq_mul]
      simpa using tendsto_const_nhds
    rw [Metric.tendsto_nhds]
    intro ε hε
    set δ : ℝ := ε / (2 * (L : ℝ))
    have hδ : 0 < δ := by positivity
    have hLδ : (L : ℝ) * δ = ε / 2 := by
      dsimp [δ]
      field_simp
    have hdist : Tendsto (fun i ↦ μ''.real {ω | δ ≤ dist (Y i ω) (X i ω)}) l (𝓝 0) := by
      rw [tendstoInMeasure_iff_measureReal_norm] at hXY
      simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hXY δ hδ
    have hX_lim : Tendsto (fun i ↦ ∫ x, F x ∂(μ''.map (X i))) l (𝓝 (∫ x, F x ∂(μ'.map Z))) := by
      simpa using ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto.1 hXZ.tendsto
        F ⟨M, hF_bd⟩ ⟨L, hF_lip⟩
    have h_rhs : Tendsto (fun i ↦ ε / 2 + M * μ''.real {ω | δ ≤ dist (Y i ω) (X i ω)} +
        |∫ x, F x ∂(μ''.map (X i)) - ∫ x, F x ∂(μ'.map Z)|) l (𝓝 (ε / 2)) := by
      have h1 := ((tendsto_const_nhds (x := ε / 2)).add (hdist.const_mul M)).add
        (tendsto_iff_dist_tendsto_zero.1 hX_lim)
      simpa only [Real.dist_eq, mul_zero, add_zero] using h1
    filter_upwards [h_rhs.eventually_lt_const (half_lt_self hε)] with i hi
    rw [Real.dist_eq]
    simp only [ProbabilityMeasure.coe_mk]
    have hstep := abs_integral_map_sub_le_of_lipschitz (hXZ.forall_aemeasurable i) (hY i)
      hF_bd hL hF_lip hδ
    rw [hLδ] at hstep
    have htri := abs_sub_le (∫ x, F x ∂(μ''.map (Y i))) (∫ x, F x ∂(μ''.map (X i)))
      (∫ x, F x ∂(μ'.map Z))
    linarith

/-- **Slutsky's convergence-in-distribution replacement lemma without separability.** If `X i → Z`
in distribution and `Y i - X i → 0` in probability along an arbitrary filter `l` in a seminormed
group with opens-measurable structure, with `Y i` almost-everywhere measurable, then `Y i → Z` in
distribution. -/
protected theorem TendstoInDistribution.congr_of_tendstoInMeasure_sub
    {E Ω'' : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace Ω''] {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {l : Filter ι} {X Y : ι → Ω'' → E} {Z : Ω' → E}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : ∀ i, AEMeasurable (Y i) μ'')
    (hXY : TendstoInMeasure μ'' (fun i ω ↦ Y i ω - X i ω) l (fun _ ↦ 0)) :
    TendstoInDistribution Y l Z (fun _ ↦ μ'') μ' := by
  refine hXZ.congr_of_tendstoInMeasure_dist hY ?_
  rw [tendstoInMeasure_iff_norm] at hXY ⊢
  simpa only [sub_zero, dist_eq_norm_sub, Real.norm_eq_abs, abs_norm] using hXY

end MeasureTheory
