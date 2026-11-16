/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.Bochner.Set

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
  have hne : Nonempty Ω'' := not_isEmpty_iff.1 fun h ↦ by
    simpa [Set.univ_eq_empty_iff.2 h] using (measure_univ (μ := μ''))
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

/-- Pointwise Riemann-sum sandwich for `y ∈ [0, k * a]` with step size `a > 0`. -/
private theorem mul_card_filter_range_bounds {k : ℕ} {a y : ℝ} (ha : 0 < a) (hy0 : 0 ≤ y)
    (hyk : y ≤ k * a) :
    let n : ℕ := ((Finset.range k).filter fun j : ℕ ↦ (j : ℝ) * a < y).card
    y ≤ a * (n : ℝ) ∧ a * (n : ℝ) ≤ y + a := by
  intro n
  set I : Finset ℕ := (Finset.range k).filter fun j : ℕ ↦ (j : ℝ) * a < y
  constructor
  · by_contra! hlt
    have hcard_lt : I.card < k := by
      by_contra! hge
      have hkle : (k : ℝ) * a ≤ a * (I.card : ℝ) := by
        nlinarith [show (k : ℝ) ≤ I.card from Nat.cast_le.2 hge]
      linarith
    have hsub : Finset.range (I.card + 1) ⊆ I := by
      intro j hj
      rw [Finset.mem_range] at hj
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
      have hja : (j : ℝ) * a ≤ (I.card : ℝ) * a :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) ha.le
      linarith
    have hle := Finset.card_le_card hsub
    rw [Finset.card_range] at hle
    omega
  · rcases Nat.eq_zero_or_pos I.card with h0 | hpos
    · have hn0 : n = 0 := h0
      rw [hn0, Nat.cast_zero, mul_zero]
      linarith
    · have hex : ∃ j ∈ I, I.card - 1 ≤ j := by
        by_contra! hall
        have hle := Finset.card_le_card (s := I) (t := Finset.range (I.card - 1))
          fun j hj ↦ Finset.mem_range.2 (hall j hj)
        rw [Finset.card_range] at hle
        omega
      obtain ⟨j, hjI, hj⟩ := hex
      have hjlt : (j : ℝ) * a < y := (Finset.mem_filter.1 hjI).2
      have hcast : ((I.card : ℝ) - 1) * a ≤ (j : ℝ) * a := by
        refine mul_le_mul_of_nonneg_right ?_ ha.le
        have hle := (Nat.cast_le (α := ℝ)).2 hj
        rwa [Nat.cast_sub (by omega : 1 ≤ I.card), Nat.cast_one] at hle
      linarith

/-- Finite layer-cake approximation of the integral of a nonnegative bounded continuous function by
a Riemann sum of open superlevel-set probabilities. -/
private theorem integral_bounds_mul_sum_measureReal_gt
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (f : BoundedContinuousFunction E ℝ) (hf : 0 ≤ f)
    {k : ℕ} {a : ℝ} (ha : 0 < a) (hka : ∀ x, f x ≤ k * a) :
    ∫ x, f x ∂ν ≤ a * ∑ j ∈ Finset.range k, ν.real {x | (j : ℝ) * a < f x} ∧
      a * ∑ j ∈ Finset.range k, ν.real {x | (j : ℝ) * a < f x} ≤ (∫ x, f x ∂ν) + a := by
  classical
  let g : E → ℝ := fun x ↦
    a * ∑ j ∈ Finset.range k, ({x | (j : ℝ) * a < f x}.indicator (fun _ ↦ (1 : ℝ)) x)
  have hgx (x : E) :
      g x = a * (((Finset.range k).filter fun j : ℕ ↦ (j : ℝ) * a < f x).card : ℝ) := by
    simp only [g, Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_boole]
  have hU (j : ℕ) : IsOpen {x | (j : ℝ) * a < f x} := isOpen_lt continuous_const f.continuous
  have hind (j : ℕ) : Integrable ({x | (j : ℝ) * a < f x}.indicator (fun _ ↦ (1 : ℝ))) ν :=
    (integrable_indicator_iff (hU j).measurableSet).2 (integrable_const _).integrableOn
  have hg_int : Integrable g ν := (integrable_finsetSum _ fun j _ ↦ hind j).const_mul a
  have hg_eq : ∫ x, g x ∂ν = a * ∑ j ∈ Finset.range k, ν.real {x | (j : ℝ) * a < f x} := by
    simp only [g, integral_const_mul]
    rw [integral_finsetSum _ fun j _ ↦ hind j]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ integral_indicator_one (hU j).measurableSet
  rw [← hg_eq]
  refine ⟨integral_mono (f.integrable ν) hg_int fun x ↦ ?_, ?_⟩
  · rw [hgx]
    exact (mul_card_filter_range_bounds ha (hf x) (hka x)).1
  · have hadd : ∫ x, (f x + a) ∂ν = (∫ x, f x ∂ν) + a := by
      rw [integral_add (f.integrable ν) (integrable_const a), integral_const]
      simp
    rw [← hadd]
    exact integral_mono hg_int ((f.integrable ν).add (integrable_const a)) fun x ↦ by
      rw [hgx]
      exact (mul_card_filter_range_bounds ha (hf x) (hka x)).2

/-- Portmanteau `(O) ⇒ (T)` for an arbitrary filter, via finite Riemann-sum approximation of
bounded continuous functions. -/
private theorem tendsto_of_forall_isOpen_eventually_sub_lt
    {ι E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    {l : Filter ι} {μs : ι → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hopen : ∀ U : Set E, IsOpen U → ∀ ε > 0,
      ∀ᶠ i in l, (μ : Measure E).real U - ε < (μs i : Measure E).real U) :
    Tendsto μs l (𝓝 μ) := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 ?_
  refine BoundedContinuousFunction.tendsto_integral_of_forall_integral_le_liminf_integral
    fun f hf ↦ ?_
  have hbd_above : IsBoundedUnder (· ≤ ·) l (fun i ↦ ∫ x, f x ∂(μs i : Measure E)) :=
    BddAbove.isBoundedUnder l.univ_mem <| by
      simpa using (BoundedContinuousFunction.isBounded_range_integral
        (fun i ↦ (μs i : Measure E)) f).bddAbove
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set M : ℝ := ‖f‖ + 1
  have hM : 0 < M := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * M / ε)
  set k : ℕ := m + 1
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.succ_pos m)
  set a : ℝ := M / k
  have ha : 0 < a := by positivity
  have ha_lt : a < ε / 2 := by
    rw [show a = M / (k : ℝ) from rfl, div_lt_iff₀ hk_pos]
    nlinarith [(div_lt_iff₀ hε).1 hm, show (m : ℝ) < k from Nat.cast_lt.2 (Nat.lt_succ_self m)]
  have hka (x : E) : f x ≤ k * a := by
    rw [show (k : ℝ) * a = M from mul_div_cancel₀ M hk_pos.ne']
    linarith [le_trans (le_abs_self _) (f.norm_coe_le_norm x)]
  have hev : ∀ᶠ i in l, ∀ j ∈ Finset.range k,
      (μ : Measure E).real {x | (j : ℝ) * a < f x} - ε / (2 * M) <
        (μs i : Measure E).real {x | (j : ℝ) * a < f x} :=
    (Filter.eventually_all_finset (Finset.range k)).2 fun j _ ↦
      hopen _ (isOpen_lt continuous_const f.continuous) (ε / (2 * M)) (by positivity)
  have hev_int : ∀ᶠ i in l, ∫ x, f x ∂(μ : Measure E) - ε ≤ ∫ x, f x ∂(μs i : Measure E) := by
    filter_upwards [hev] with i hi
    have hμ_le := (integral_bounds_mul_sum_measureReal_gt (μ : Measure E) f hf ha hka).1
    have hμi_ge := (integral_bounds_mul_sum_measureReal_gt (μs i : Measure E) f hf ha hka).2
    have hsum : ∑ j ∈ Finset.range k,
        ((μ : Measure E).real {x | (j : ℝ) * a < f x} - ε / (2 * M)) ≤
        ∑ j ∈ Finset.range k, (μs i : Measure E).real {x | (j : ℝ) * a < f x} :=
      Finset.sum_le_sum fun j hj ↦ (hi j hj).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hmul := mul_le_mul_of_nonneg_left hsum ha.le
    have hcancel : a * ((k : ℝ) * (ε / (2 * M))) = ε / 2 := by dsimp [a]; field_simp
    linarith
  linarith [Filter.le_liminf_of_le hbd_above.isCobounded_ge hev_int]

/-- Portmanteau `(Lip) ⇒ (T)` for an arbitrary filter, removing the countable-generation
assumption from Mathlib's `tendsto_iff_forall_lipschitz_integral_tendsto`. -/
private theorem tendsto_of_forall_lipschitz_integral_tendsto
    {ι E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {l : Filter ι} {μs : ι → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (h : ∀ F : E → ℝ, (∃ M, ∀ x y, dist (F x) (F y) ≤ M) → (∃ L, LipschitzWith L F) →
      Tendsto (fun i ↦ ∫ x, F x ∂(μs i : Measure E)) l (𝓝 (∫ x, F x ∂(μ : Measure E)))) :
    Tendsto μs l (𝓝 μ) := by
  refine tendsto_of_forall_isOpen_eventually_sub_lt fun U hU ε hε ↦ ?_
  have hs : IsClosed Uᶜ := hU.isClosed_compl
  let fs : ℕ → E → ℝ := fun n x ↦
    thickenedIndicator (δ := (1 : ℝ) / (n + 1)) (by positivity) Uᶜ x
  have key₁ : Tendsto (fun n ↦ ∫ x, fs n x ∂(μ : Measure E)) atTop
      (𝓝 ((μ : Measure E).real Uᶜ)) :=
    tendsto_integral_thickenedIndicator_of_isClosed (μ : Measure E) hs
      (δs := fun n ↦ (1 : ℝ) / (n + 1)) (fun _ ↦ by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (key₁.eventually_lt_const (lt_add_of_pos_right _ (half_pos hε)))
  have hbd : ∃ C, ∀ x y, dist (fs M x) (fs M y) ≤ C := ⟨1, fun x y ↦ by
    rw [Real.dist_eq, abs_le]
    have h1 (z : E) : fs M z ≤ 1 := thickenedIndicator_le_one _ _ _
    have h2 (z : E) : 0 ≤ fs M z := by simp [fs]
    constructor <;> linarith [h1 x, h1 y, h2 x, h2 y]⟩
  have hlip : ∃ L, LipschitzWith L (fs M) :=
    ⟨_, lipschitzWith_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) Uᶜ⟩
  have key₂ := (h (fs M) hbd hlip).eventually_lt_const (lt_add_of_pos_right _ (half_pos hε))
  filter_upwards [key₂] with i hi
  have hle_i : (μs i : Measure E).real Uᶜ ≤ ∫ x, fs M x ∂(μs i : Measure E) := by
    rw [← integral_indicator_one hs.measurableSet]
    refine integral_mono ((integrable_indicator_iff hs.measurableSet).2
      (integrable_const _).integrableOn) (integrable_thickenedIndicator _ _) fun x ↦ ?_
    by_cases hx : x ∈ Uᶜ
    · have h1 := indicator_le_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) Uᶜ x
      simp only [Set.indicator_of_mem hx, Pi.one_apply] at h1 ⊢
      dsimp only [fs]
      exact_mod_cast h1
    · simp [fs, Set.indicator_of_notMem hx]
  have hc_μ : (μ : Measure E).real Uᶜ = 1 - (μ : Measure E).real U :=
    probReal_compl_eq_one_sub hU.measurableSet
  have hc_i : (μs i : Measure E).real Uᶜ = 1 - (μs i : Measure E).real U :=
    probReal_compl_eq_one_sub hU.measurableSet
  linarith [hM M le_rfl]

/-- **Slutsky's convergence-in-distribution replacement lemma without separability**, for a general
pseudometric space and arbitrary filter `l`. If `X i → Z` in distribution and
`dist (Y i) (X i) → 0` in probability, with `Y i` almost-everywhere measurable, then `Y i → Z` in
distribution. Unlike Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub`, neither
`SecondCountableTopology`, `BorelSpace`, nor countable generation of `l` is assumed. -/
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
    apply tendsto_of_forall_lipschitz_integral_tendsto
    rintro F ⟨M, hF_bd⟩ ⟨L, hF_lip⟩
    obtain rfl | hL := eq_zero_or_pos L
    · have hne : Nonempty Ω' := not_isEmpty_iff.1 fun h ↦ by
        simpa [Set.univ_eq_empty_iff.2 h] using (measure_univ (μ := μ'))
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
      let F' : BoundedContinuousFunction E ℝ :=
        { toFun := F
          continuous_toFun := hF_lip.continuous
          map_bounded' := ⟨M, hF_bd⟩ }
      simpa [F'] using ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hXZ.tendsto F'
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
