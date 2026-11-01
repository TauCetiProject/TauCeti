/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Doob's maximal inequality over finite sets and in continuous time

Mathlib's `MeasureTheory.maximal_ineq` is Doob's maximal inequality for a nonnegative submartingale
indexed by `ℕ`. This file transfers it to a general linearly ordered time set. For a nonnegative
submartingale `f`, a time `T` and `ε : ℝ≥0`:

* over any finite set `F` of times `≤ T`, `ε P(∃ t ∈ F, ε ≤ f_t) ≤ E[f_T]`;
* if every path is right-continuous before `T` (almost surely), and the time set is densely ordered
  and separable (for instance `ℝ≥0`), `ε P(∃ t ≤ T, ε < f_t) ≤ E[f_T]`.

The event `{∃ t ≤ T, ε < f_t}` need not be measurable; `P` is applied to it as an outer measure.
The running maximum `sup_{t ≤ T} f_t` itself is almost everywhere measurable under the same
right-continuity hypothesis, since it agrees almost everywhere with a supremum over countably many
times.

A weak-type bound of this kind controls the running maximum in every `Lᵖ` with `p < 1`. The file
records the case `p = 1 / 2`, `E[sup_{t ≤ T} √f_t] ≤ P(Ω) + 4 E[f_T]`. Applied to `f = g²`, it
bounds the expected running maximum of a nonnegative process `g` whose square is a submartingale;
this is how the running maximum of an exponential martingale is shown to be integrable.

## Main declarations

* `MeasureTheory.Submartingale.mul_measure_exists_mem_le_le`: the maximal inequality over a finite
  set of times.
* `MeasureTheory.Submartingale.mul_measure_exists_le_lt_le`: the maximal inequality over all times
  `t ≤ T`, for right-continuous paths.
* `MeasureTheory.aemeasurable_iSup_le_ofReal`: the running maximum of a process with
  right-continuous paths is almost everywhere measurable.
* `MeasureTheory.Submartingale.lintegral_iSup_sqrt_le`: the bound on `E[sup_{t ≤ T} √f_t]`.

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

variable [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]

/-- If `g` is right-continuous at every time before `T` and `a < g t` for some `t ≤ T`, then
`a < g s` for some `s` in `{T} ∪ (D ∩ (-∞, T])`, for any dense set `D`. -/
private theorem exists_mem_insert_inter_Iic_lt {D : Set ι} (hD : Dense D) {g : ι → ℝ} {T t : ι}
    (hg : ∀ t < T, ContinuousWithinAt g (Ioi t) t) (htT : t ≤ T) {a : ℝ} (ha : a < g t) :
    ∃ s ∈ insert T (D ∩ Iic T), a < g s := by
  rcases htT.lt_or_eq with htT | rfl
  · obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' htT).1
      ((hg t htT).preimage_mem_nhdsWithin (Ioi_mem_nhds ha))
    obtain ⟨s, hsD, hs⟩ := hD.exists_between (lt_min hu htT)
    exact ⟨s, Or.inr ⟨hsD, hs.2.le.trans (min_le_right _ _)⟩,
      hsub ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩⟩
  · exact ⟨t, mem_insert _ _, ha⟩

/-- The running maximum `sup_{t ≤ T} X_t` of a process with almost surely right-continuous paths
before `T` is almost everywhere measurable: it agrees almost everywhere with the supremum over a
countable set of times. -/
theorem _root_.MeasureTheory.aemeasurable_iSup_le_ofReal [TopologicalSpace.SeparableSpace ι]
    {X : ι → Ω → ℝ} (hX : ∀ t, AEMeasurable (X t) μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (X t ω)) μ := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ι
  set S : Set ι := insert T (D ∩ Iic T)
  have : Countable S := ((hDc.mono inter_subset_left).insert T).to_subtype
  refine (AEMeasurable.iSup fun s : S ↦ (hX s).ennreal_ofReal).congr ?_
  filter_upwards [hcont] with ω hω
  refine le_antisymm (iSup_le fun ⟨s, hs⟩ ↦ le_iSup₂_of_le s ?_ le_rfl) ?_
  · rcases hs with rfl | ⟨-, hs⟩
    exacts [le_rfl, hs]
  refine iSup₂_le fun t htT ↦ le_of_forall_lt fun a ha ↦ ?_
  have hatop : a ≠ ∞ := ha.ne_top
  rw [← ENNReal.ofReal_toReal hatop, ENNReal.ofReal_lt_ofReal_iff'] at ha
  obtain ⟨s, hs, has⟩ := exists_mem_insert_inter_Iic_lt hD hω htT ha.1
  refine lt_of_lt_of_le ?_ (le_iSup _ (⟨s, hs⟩ : S))
  rwa [← ENNReal.ofReal_toReal hatop, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]

/-- **Doob's maximal inequality in continuous time.** Let `f` be a nonnegative submartingale
indexed by a densely ordered separable time set, such as `ℝ≥0`, whose paths are almost surely
right-continuous at every time before `T`. Then `ε P(∃ t ≤ T, ε < f_t) ≤ E[f_T]`. -/
theorem mul_measure_exists_le_lt_le [TopologicalSpace.SeparableSpace ι] [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤ ENNReal.ofReal (∫ ω, f T ω ∂μ) := by
  classical
  -- By right-continuity the event is, up to a null set, the union over the finite subsets `F` of
  -- a countable set `S` of times `≤ T`, dense below `T`; this union is directed.
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ι
  set S : Set ι := insert T (D ∩ Iic T)
  have : Countable S := ((hDc.mono inter_subset_left).insert T).to_subtype
  let A : Finset S → Set Ω := fun F ↦ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}
  have hA : ∀ F, ε * μ (A F) ≤ ENNReal.ofReal (∫ ω, f T ω ∂μ) := fun F ↦ by
    refine le_trans ?_ (hf.mul_measure_exists_mem_le_le hnonneg ε
      (F := F.map (Function.Embedding.subtype _)) fun t ht ↦ ?_)
    · gcongr
      rintro ω ⟨t, ht, hεt⟩
      exact ⟨t, Finset.mem_map_of_mem _ ht, hεt⟩
    · obtain ⟨⟨s, hs⟩, -, rfl⟩ := Finset.mem_map.1 ht
      rcases hs with rfl | ⟨-, hs⟩
      exacts [le_rfl, hs]
  have hdir : Directed (· ⊆ ·) A := fun F₁ F₂ ↦ ⟨F₁ ∪ F₂,
    fun _ ⟨t, ht, h⟩ ↦ ⟨t, Finset.mem_union_left _ ht, h⟩,
    fun _ ⟨t, ht, h⟩ ↦ ⟨t, Finset.mem_union_right _ ht, h⟩⟩
  have hsub : {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤ᵐ[μ] ⋃ F, A F := by
    filter_upwards [hcont] with ω hω ⟨t, htT, hεt⟩
    obtain ⟨s, hs, hεs⟩ := exists_mem_insert_inter_Iic_lt hD hω htT hεt
    exact mem_iUnion.2 ⟨{⟨s, hs⟩}, ⟨s, hs⟩, Finset.mem_singleton_self _, hεs.le⟩
  calc ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤ ε * μ (⋃ F, A F) := by
        gcongr 1
        exact measure_mono_ae hsub
    _ = ⨆ F, ε * μ (A F) := by rw [hdir.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ _ := iSup_le hA

/-- A nonnegative extended real is at most `1 + ∑ₖ 2^(k+1) 1{2^k < y}`. -/
private theorem le_one_add_tsum_pow_indicator (y : ℝ≥0∞) :
    y ≤ 1 + ∑' k : ℕ, if (2 : ℝ≥0∞) ^ k < y then 2 ^ (k + 1) else 0 := by
  set R : ℝ≥0∞ := 1 + ∑' k : ℕ, if (2 : ℝ≥0∞) ^ k < y then 2 ^ (k + 1) else 0
  by_contra! hR
  -- If `R < y`, then inductively `2^k < y` and `2^(k+1) ≤ R` for every `k`, so `R = ∞`.
  have hk : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k < y := by
    intro k
    induction k with
    | zero => exact lt_of_le_of_lt (by simp [R]) hR
    | succ k ih =>
      refine lt_of_le_of_lt (le_trans ?_ le_add_self) hR
      exact le_trans (by simp [ih]) (ENNReal.le_tsum k)
  have hRtop : R ≠ ∞ := hR.ne_top
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hRtop
  have h2 : (2 : ℝ≥0∞) ^ (n + 1) ≤ R :=
    le_trans (by simp [hk n]) ((ENNReal.le_tsum n).trans le_add_self)
  have : (n : ℝ≥0∞) < 2 ^ (n + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  exact (hn.trans (this.trans_le h2)).false

/-- **The running maximum of the square root of a submartingale is integrable.** For a
nonnegative submartingale `f` whose paths are almost surely right-continuous before `T`,
`E[sup_{t ≤ T} √f_t] ≤ P(Ω) + 4 E[f_T]`. The integrand is almost everywhere measurable by
`MeasureTheory.aemeasurable_iSup_le_ofReal`. -/
theorem lintegral_iSup_sqrt_le [TopologicalSpace.SeparableSpace ι] [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) :
    ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal √(f t ω) ∂μ ≤
      μ univ + 4 * ENNReal.ofReal (∫ ω, f T ω ∂μ) := by
  set Y : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal √(f t ω)
  set E := ENNReal.ofReal (∫ ω, f T ω ∂μ)
  -- The level sets `{2^k < Y} = {∃ t ≤ T, 4^k < f_t}` have measure at most `E / 4^k`.
  have hlevel : ∀ k : ℕ, (2 : ℝ≥0∞) ^ (k + 1) * μ {ω | 2 ^ k < Y ω} ≤ 2 * 2⁻¹ ^ k * E := by
    intro k
    have hset : {ω | 2 ^ k < Y ω} = {ω | ∃ t ≤ T, ((4 ^ k : ℝ≥0) : ℝ) < f t ω} := by
      ext ω
      simp only [Y, mem_ofPred_eq, lt_iSup_iff, exists_prop]
      refine exists_congr fun t ↦ and_congr_right fun _ ↦ ?_
      rw [show (2 : ℝ≥0∞) ^ k = ENNReal.ofReal √(4 ^ k) by
        rw [show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
          Real.sqrt_sq (by positivity), ENNReal.ofReal_pow (by norm_num)]; simp,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _),
        Real.sqrt_lt_sqrt_iff (by positivity)]
      push_cast
      rfl
    have hmax := hf.mul_measure_exists_le_lt_le hnonneg hcont (4 ^ k)
    rw [← hset] at hmax
    have h4 : (2 : ℝ≥0∞) ^ (k + 1) = 2 * 2⁻¹ ^ k * ((4 ^ k : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_pow, show ((4 : ℝ≥0) : ℝ≥0∞) = 2 * 2 by norm_num, mul_pow, ← mul_assoc,
        mul_assoc 2, ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow,
        mul_one, pow_succ, mul_comm]
    rw [h4, mul_assoc]
    gcongr
  -- Replace the level sets by measurable supersets of the same measure.
  set B : ℕ → Set Ω := fun k ↦ toMeasurable μ {ω | 2 ^ k < Y ω}
  calc ∫⁻ ω, Y ω ∂μ
      ≤ ∫⁻ ω, 1 + ∑' k : ℕ, (B k).indicator (fun _ ↦ (2 : ℝ≥0∞) ^ (k + 1)) ω ∂μ := by
        refine lintegral_mono fun ω ↦ (le_one_add_tsum_pow_indicator (Y ω)).trans ?_
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
    _ ≤ μ univ + ∑' k : ℕ, 2 * 2⁻¹ ^ k * E := add_le_add le_rfl (ENNReal.tsum_le_tsum hlevel)
    _ = μ univ + 4 * E := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv]
        norm_num

end ContinuousTime

end MeasureTheory.Submartingale
