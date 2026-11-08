/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.SpecificLimits.Basic
public import TauCeti.Topology.Algebra.InfiniteSum.ENNReal
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RightContinuous

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Doob's maximal inequality over finite sets and in continuous time

Mathlib's `MeasureTheory.maximal_ineq` is Doob's maximal inequality for a nonnegative submartingale
indexed by `ℕ`. This file transfers it to a general linearly ordered time set. For a nonnegative
submartingale `f`, a time `T` and `ε : ℝ≥0`:

* over any finite set `F` of times `≤ T`, `ε P(∃ t ∈ F, ε ≤ f_t) ≤ E[f_T]`;
* if every path is right-continuous before `T` (almost surely), and the time set is second
  countable (for instance `ℝ≥0`), `ε P(∃ t ≤ T, ε < f_t) ≤ E[f_T]`.

The event `{∃ t ≤ T, ε < f_t}` need not be measurable; `P` is applied to it as an outer measure.
Under the same right-continuity hypothesis the running maximum `sup_{t ≤ T} f_t` is almost
everywhere measurable (`MeasureTheory.aemeasurable_iSup_le_ofReal`).

A weak-type bound of this kind controls the running maximum in every `Lᵖ` with `p < 1`. The file
records the case `p = 1 / 2`, `E[sup_{t ≤ T} √f_t] ≤ P(Ω) + 4 E[f_T]`. Applied to `f = g²`, it
bounds the expected running maximum of a nonnegative process `g` whose square is a submartingale;
this is how the running maximum of an exponential martingale is shown to be integrable.

## Main declarations

* `MeasureTheory.Submartingale.mul_measure_exists_mem_le_le`: the maximal inequality over a finite
  set of times.
* `MeasureTheory.Submartingale.mul_measure_exists_le_lt_le`: the maximal inequality over all times
  `t ≤ T`, for right-continuous paths.
* `MeasureTheory.Submartingale.lintegral_iSup_sqrt_le`: the bound on `E[sup_{t ≤ T} √f_t]`.
* `MeasureTheory.Martingale.submartingale_norm`: the norm of a Banach-valued martingale is a
  submartingale, using Mathlib's conditional Jensen inequality `norm_condExp_le`.
* `MeasureTheory.Martingale.mul_measure_exists_le_norm_lt_le`: the weak maximal inequality for
  martingale norms.
* `MeasureTheory.Martingale.measure_exists_le_norm_lt_le`: a terminal L¹ bound gives an outer
  probability bound for the path-error event.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991,
  Theorem 1.3.8.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, Springer, 1999,
  Theorem II.1.7.
-/

public section

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Doob's maximal inequality over a finite set of times.** For a nonnegative submartingale `f`
and a finite set `F` of times `≤ T`, `ε P(∃ t ∈ F, ε ≤ f_t) ≤ E[f_T]`. -/
theorem mul_measure_exists_mem_le_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hnonneg : 0 ≤ f) (ε : ℝ≥0) {F : Finset ι} {T : ι} (hF : ∀ t ∈ F, t ≤ T) :
    ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤ ENNReal.ofReal (∫ ω, f T ω ∂μ) := by
  classical
  -- Enumerate `G = F ∪ {T}` increasingly as `τ 0 ≤ ⋯ ≤ τ n = T`, extended constantly beyond `n`,
  -- and apply `maximal_ineq` to the discrete submartingale `j ↦ f (τ j)`.
  set G := insert T F
  set n := G.card - 1
  have hG : G.card = n + 1 :=
    (Nat.sub_add_cancel (Finset.card_pos.2 (Finset.insert_nonempty _ _))).symm
  set e := G.orderEmbOfFin hG
  let τ : ℕ → ι := fun j ↦ e ⟨min j n, by omega⟩
  have hτ : Monotone τ := fun i j hij ↦ e.monotone (Fin.mk_le_mk.2 (min_le_min_right _ hij))
  have hτn : τ n = T := by
    have hmax : G.max' (Finset.insert_nonempty _ _) = T :=
      le_antisymm (Finset.max'_le _ _ _ fun t ht ↦ by
        rcases Finset.mem_insert.1 ht with rfl | ht
        exacts [le_rfl, hF t ht]) (Finset.le_max' _ _ (Finset.mem_insert_self _ _))
    simpa [τ, hmax] using Finset.orderEmbOfFin_last hG (Nat.succ_pos n)
  let 𝒢 : Filtration ℕ m0 := ⟨fun j ↦ ℱ (τ j), fun _ _ hij ↦ ℱ.mono (hτ hij), fun _ ↦ ℱ.le _⟩
  have hg : Submartingale (fun j ↦ f (τ j)) 𝒢 μ :=
    ⟨fun j ↦ hf.stronglyAdapted (τ j), fun _ _ hij ↦ hf.ae_le_condExp (hτ hij),
      fun j ↦ hf.integrable (τ j)⟩
  have hsub : {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ⊆ {ω | (ε : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ f (τ k) ω} := by
    rintro ω ⟨t, ht, hεt⟩
    obtain ⟨i, rfl⟩ : t ∈ range e := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_insert_of_mem ht
    refine hεt.trans (Finset.le_sup'_of_le _ (Finset.mem_range.2 i.2) ?_)
    simp only [τ, min_eq_left (Nat.le_of_lt_succ i.2), le_refl]
  calc ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}
      ≤ ε * μ {ω | (ε : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ f (τ k) ω} := by
        gcongr
    _ ≤ ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ f (τ k) ω},
            f (τ n) ω ∂μ) := maximal_ineq hg (fun _ ↦ hnonneg _) n
    _ ≤ ENNReal.ofReal (∫ ω, f T ω ∂μ) := by
        rw [hτn]
        exact ENNReal.ofReal_le_ofReal
          (setIntegral_le_integral (hf.integrable T) (Eventually.of_forall (hnonneg T)))

section ContinuousTime

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- **Doob's maximal inequality in continuous time.** Let `f` be a nonnegative submartingale
indexed by a second countable time set, such as `ℝ≥0`, whose paths are almost surely
right-continuous at every time before `T`. Then `ε P(∃ t ≤ T, ε < f_t) ≤ E[f_T]`. -/
theorem mul_measure_exists_le_lt_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤ ENNReal.ofReal (∫ ω, f T ω ∂μ) := by
  classical
  -- By right-continuity the event is, up to a null set, the union over the finite subsets `F` of
  -- a countable set `S` of times `≤ T`, dense below `T`; this union is directed.
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt (α := ℝ) T
  have := hSc.to_subtype
  let A : Finset S → Set Ω := fun F ↦ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}
  have hA : ∀ F, ε * μ (A F) ≤ ENNReal.ofReal (∫ ω, f T ω ∂μ) := fun F ↦ by
    refine le_trans ?_ (hf.mul_measure_exists_mem_le_le hnonneg ε
      (F := F.map (Function.Embedding.subtype _)) fun t ht ↦ ?_)
    · gcongr
      rintro ω ⟨t, ht, hεt⟩
      exact ⟨t, Finset.mem_map_of_mem _ ht, hεt⟩
    · obtain ⟨⟨s, hs⟩, -, rfl⟩ := Finset.mem_map.1 ht
      exact hST hs
  have hdir : Directed (· ⊆ ·) A := fun F₁ F₂ ↦ ⟨F₁ ∪ F₂,
    fun _ ⟨t, ht, h⟩ ↦ ⟨t, Finset.mem_union_left _ ht, h⟩,
    fun _ ⟨t, ht, h⟩ ↦ ⟨t, Finset.mem_union_right _ ht, h⟩⟩
  have hsub : {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤ᵐ[μ] ⋃ F, A F := by
    filter_upwards [hcont] with ω hω ⟨t, htT, hεt⟩
    obtain ⟨s, hs, hεs⟩ := hS hω htT hεt
    exact mem_iUnion.2 ⟨{⟨s, hs⟩}, ⟨s, hs⟩, Finset.mem_singleton_self _, hεs.le⟩
  calc ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤ ε * μ (⋃ F, A F) := by
        gcongr 1
        exact measure_mono_ae hsub
    _ = ⨆ F, ε * μ (A F) := by rw [hdir.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ _ := iSup_le hA

/-- **The running maximum of the square root of a submartingale is integrable.** For a
nonnegative submartingale `f` whose paths are almost surely right-continuous before `T`,
`E[sup_{t ≤ T} √f_t] ≤ P(Ω) + 4 E[f_T]`. The integrand is almost everywhere measurable by
`MeasureTheory.aemeasurable_iSup_le_ofReal`. -/
theorem lintegral_iSup_sqrt_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) :
    ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal √(f t ω) ∂μ ≤
      μ univ + 4 * ENNReal.ofReal (∫ ω, f T ω ∂μ) := by
  set Y : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal √(f t ω)
  set E := ENNReal.ofReal (∫ ω, f T ω ∂μ)
  -- The level sets `{2^k < Y} = {∃ t ≤ T, 4^k < f_t}` have measure at most `E / 4^k`.
  have hlevel : ∀ k : ℕ, (2 : ℝ≥0∞) ^ (k + 1) * μ {ω | 2 ^ k < Y ω} ≤ 2 * 2⁻¹ ^ k * E := by
    intro k
    -- `2^k = √(4^k)`, read in `ℝ≥0∞`.
    have hsqrt : (2 : ℝ≥0∞) ^ k = ENNReal.ofReal √((4 ^ k : ℝ≥0) : ℝ) := by
      have : √((4 ^ k : ℝ≥0) : ℝ) = 2 ^ k := by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity), ← mul_pow]
        norm_num
      rw [this, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
    have hset : {ω | 2 ^ k < Y ω} = {ω | ∃ t ≤ T, ((4 ^ k : ℝ≥0) : ℝ) < f t ω} := by
      ext ω
      simp only [Y, mem_ofPred_eq, lt_iSup_iff, exists_prop, hsqrt,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _),
        Real.sqrt_lt_sqrt_iff (NNReal.coe_nonneg _)]
    have hmax := hf.mul_measure_exists_le_lt_le hnonneg hcont (4 ^ k)
    rw [← hset] at hmax
    -- `2^(k+1) = 2 · 2⁻ᵏ · 4^k`, since `2⁻ᵏ · 2ᵏ = 1` and `4^k = 2^k · 2^k`.
    have hinv : (2 : ℝ≥0∞)⁻¹ ^ k * 2 ^ k = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    have h4 : ((4 ^ k : ℝ≥0) : ℝ≥0∞) = 2 ^ k * 2 ^ k := by
      push_cast
      rw [← mul_pow]
      norm_num
    have hpow : (2 : ℝ≥0∞) ^ (k + 1) = 2 * 2⁻¹ ^ k * ((4 ^ k : ℝ≥0) : ℝ≥0∞) :=
      calc (2 : ℝ≥0∞) ^ (k + 1) = 2 * (2⁻¹ ^ k * 2 ^ k) * 2 ^ k := by rw [hinv]; ring
        _ = 2 * 2⁻¹ ^ k * ((4 ^ k : ℝ≥0) : ℝ≥0∞) := by rw [h4]; ring
    rw [hpow, mul_assoc]
    gcongr
  -- Replace the level sets by measurable supersets of the same measure.
  set B : ℕ → Set Ω := fun k ↦ toMeasurable μ {ω | 2 ^ k < Y ω}
  calc ∫⁻ ω, Y ω ∂μ
      ≤ ∫⁻ ω, 1 + ∑' k : ℕ, (B k).indicator (fun _ ↦ (2 : ℝ≥0∞) ^ (k + 1)) ω ∂μ := by
        refine lintegral_mono fun ω ↦ (ENNReal.le_one_add_tsum_pow_indicator (Y ω)).trans ?_
        gcongr with k
        split_ifs with h
        · rw [indicator_of_mem (subset_toMeasurable μ _ h)]
        · exact bot_le
    _ = μ univ + ∑' k : ℕ, 2 ^ (k + 1) * μ {ω | 2 ^ k < Y ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
          lintegral_tsum fun k ↦ (measurable_const.indicator
            (measurableSet_toMeasurable _ _)).aemeasurable]
        simp_rw [lintegral_indicator_const (measurableSet_toMeasurable _ _),
          measure_toMeasurable]
    _ ≤ μ univ + ∑' k : ℕ, 2 * 2⁻¹ ^ k * E := add_le_add le_rfl (tsum_le_tsum hlevel)
    _ = μ univ + 4 * E := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv]
        norm_num

end ContinuousTime

end MeasureTheory.Submartingale

namespace MeasureTheory.Martingale

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The norm of a Banach-valued martingale is a submartingale. -/
theorem submartingale_norm [Preorder ι] {ℱ : Filtration ι mΩ}
    {M : ι → Ω → E} (hM : Martingale M ℱ μ) :
    Submartingale (fun t ω ↦ ‖M t ω‖) ℱ μ := by
  refine ⟨fun t ↦ (hM.stronglyAdapted t).norm, fun s t hst ↦ ?_,
    fun t ↦ (hM.integrable t).norm⟩
  filter_upwards [norm_condExp_le (m := ℱ s) (M t), hM.condExp_ae_eq hst] with ω h₁ h₂
  simpa only [h₂] using h₁

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ} {M : ι → Ω → E}

/-- **Doob's weak maximal inequality for the norm of a martingale.** A terminal L¹
bound controls the outer probability of a uniform path error. -/
theorem mul_measure_exists_le_norm_lt_le (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    (ε : ℝ≥0) :
    ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < ‖M t ω‖} ≤
      ENNReal.ofReal (∫ ω, ‖M T ω‖ ∂μ) := by
  exact hM.submartingale_norm.mul_measure_exists_le_lt_le (fun _ _ ↦ norm_nonneg _)
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm) ε

/-- A terminal L¹ bound of `ε * δ` bounds by `δ` the outer probability that a martingale's
norm exceeds the positive threshold `ε` before `T`. Apply this to a difference of martingales
to control their uniform path error. -/
theorem measure_exists_le_norm_lt_le (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {ε δ : ℝ≥0} (hε : 0 < ε) (hterminal : ∫ ω, ‖M T ω‖ ∂μ ≤ (ε : ℝ) * δ) :
    μ {ω | ∃ t ≤ T, (ε : ℝ) < ‖M t ω‖} ≤ (δ : ℝ≥0∞) := by
  have hmax := hM.mul_measure_exists_le_norm_lt_le hcont ε
  have hbound : ENNReal.ofReal (∫ ω, ‖M T ω‖ ∂μ) ≤
      (ε : ℝ≥0∞) * (δ : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_mul ε.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal hterminal
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hε.ne') (by finiteness)).1
    (hmax.trans hbound)

end MeasureTheory.Martingale
