/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
public import Mathlib.Probability.Process.LocalProperty
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Process.StochasticInterval
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Localization, stopping compatibility, and general existence of the Itô integral

For a locally Brownian-integrable integrand `H` and an almost surely continuous filtered
pre-Brownian motion `W`, the continuous-time Itô stochastic integral is constructed by localizing
`H` with the closed-level energy localizers `TauCeti.nnvolume.energyLocalizer H (n + 1)`, taking
the `L²` Itô integrals of the localized cutoffs, verifying stopping compatibility on overlapping
stages, and patching the resulting continuous predictable stages via
`TauCeti.exists_isStronglyProgressive_patch_stoppedProcess` and
`MeasureTheory.StronglyAdapted.exists_isStronglyPredictable_indist_of_ae_continuous`.

This yields:
* `TauCeti.Probability.IsItoIntegral.of_stoppedProcess`: stability of `IsItoIntegral` under
  localization by measurable random times tending almost surely to `⊤`;
* `TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_ite_le_stoppedProcess` (and its `L²`
  base case `isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable`): stopping an Itô integral
  at any stopping time `τ` produces an Itô integral of the cutoff integrand `1_{[0, τ]} H`;
* `TauCeti.Probability.IsFilteredPreBrownianReal.exists_isItoIntegral`: existence of a predictable,
  almost surely continuous Itô integral that is a native local martingale on the raw filtration;
* `TauCeti.Probability.IsFilteredPreBrownianReal.locally_martingale_of_isItoIntegral` and
  `locally_martingale_sq_sub_of_isItoIntegral`: every strongly progressive Itô integral `I` is a
  native local martingale, and `I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` is a native local martingale.

No completeness or right continuity of the filtration is assumed anywhere.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H I : ℝ≥0 → Ω → ℝ}

/-! ### Localization stability of `IsItoIntegral` -/

/-- If `I` is almost surely continuous and, along measurable random times `τ n → ⊤` almost surely,
each stopped process `stoppedProcess I (τ n)` is indistinguishable from an Itô integral of a
process `Hseq n` that eventually agrees with `H` on every compact horizon `[0, T]` outside a common
null set, then `I` is an Itô integral of `H`. Neither monotonicity nor the stopping-time property
of `τ n` is required. -/
theorem IsItoIntegral.of_stoppedProcess [IsFiniteMeasure P]
    {τ : ℕ → Ω → WithTop ℝ≥0} {Hseq U : ℕ → ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H)
    (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hτ_meas : ∀ n, Measurable (τ n))
    (hτ : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hU : ∀ n, IsItoIntegral ℱ P W (Hseq n) (U n))
    (hstop : ∀ n, stoppedProcess I (τ n) ≡ᵐ[P] U n)
    (hHeq : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, EqOn (Hseq n · ω) (H · ω) (Iic T)) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hH, hIcont, fun t ↦ ?_⟩
  let E (m : ℕ) (ω : Ω) : ℝ≥0∞ := ∫⁻ s, ‖Hseq m s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t
  have hE_meas (m : ℕ) : Measurable (E m) :=
    ((((hU m).isStronglyPredictable.sub hH).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const
      2).lintegral_prod_left'
  let G (m : ℕ) : Set Ω := {ω | (t : WithTop ℝ≥0) < τ m ω} ∩ {ω | E m ω = 0}
  have hG_meas (m : ℕ) : MeasurableSet (G m) :=
    (measurableSet_lt measurable_const (hτ_meas m)).inter
      ((hE_meas m) (measurableSet_singleton 0))
  have hG_lim : Tendsto (fun m ↦ P (G m)ᶜ) atTop (𝓝 0) := by
    let B (m : ℕ) : Set Ω := ⋃ j ≥ m, (G j)ᶜ
    have hB_meas (m : ℕ) : MeasurableSet (B m) :=
      MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦ (hG_meas j).compl
    have hB_anti : Antitone B := fun m₁ m₂ hle ↦
      iUnion₂_mono' fun j hj ↦ ⟨j, hle.trans hj, subset_rfl⟩
    have hB_inter : P (⋂ m, B m) = 0 := by
      have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ m, B m := by
        filter_upwards [hτ, hHeq] with ω hτω hHω
        rw [mem_iInter, not_forall]
        have hlt : ∀ᶠ j in atTop, (t : WithTop ℝ≥0) < τ j ω :=
          hτω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))
        obtain ⟨m, hm⟩ := eventually_atTop.mp (hlt.and (hHω t))
        refine ⟨m, ?_⟩
        simp only [B, mem_iUnion, mem_compl_iff, not_exists, not_not]
        intro j hj
        refine ⟨(hm j hj).1, ?_⟩
        have hsupp : ∀ᵐ s ∂timeMeasure t, s ∈ Ioc 0 t := by
          rw [timeMeasure_def, ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall fun _ hs ↦ hs
        have hzero : (fun s ↦ ‖Hseq j s ω - H s ω‖ₑ ^ 2) =ᵐ[timeMeasure t] 0 := by
          filter_upwards [hsupp] with s hs
          simp [(hm j hj).2 hs.2]
        simpa only [E, mem_ofPred_eq, Pi.zero_apply, lintegral_zero] using lintegral_congr_ae hzero
      simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hae
    have hB_lim : Tendsto (fun m ↦ P (B m)) atTop (𝓝 0) := by
      rw [← hB_inter]
      exact tendsto_measure_iInter_atTop (fun m ↦ (hB_meas m).nullMeasurableSet) hB_anti
        ⟨0, measure_ne_top P (B 0)⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ ↦ zero_le) (fun m ↦ measure_mono (subset_iUnion₂_of_subset m le_rfl Subset.rfl))
  have hstep (k : ℕ) :
      ∃ (m : ℕ) (n : ℕ) (σ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ),
        MonotoneOn σ (Iic n) ∧
        (∀ j < n, StronglyMeasurable[ℱ (σ j)] (a j)) ∧
        (∀ j < n, ∃ C : ℝ, ∀ ω, ‖a j ω‖ ≤ C) ∧
        P (G m)ᶜ < ((k : ℝ≥0∞) + 1)⁻¹ / 2 ∧
        P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ ∫⁻ s, ‖Finance.simpleHolding σ n a s ω - Hseq m s ω‖ₑ ^ 2
            ∂timeMeasure t} < ((k : ℝ≥0∞) + 1)⁻¹ / 2 ∧
        P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ edist (Finance.simpleGains σ n a W t ω) (U m t ω)} <
          ((k : ℝ≥0∞) + 1)⁻¹ / 2 := by
    have hδ : 0 < ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.mpr (by simp)
    have hhalf : 0 < ((k : ℝ≥0∞) + 1)⁻¹ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
    obtain ⟨m, hm⟩ := (hG_lim.eventually (gt_mem_nhds hhalf)).exists
    obtain ⟨n', σ', a', hσ', ha', hb', hE', hM'⟩ := (hU m).approx t
    obtain ⟨j, hj1, hj2⟩ :=
      (((hE' _ hδ).eventually (gt_mem_nhds hhalf)).and
        ((hM' _ hδ).eventually (gt_mem_nhds hhalf))).exists
    exact ⟨m, n' j, σ' j, a' j, hσ' j, ha' j, hb' j, hm, hj1, hj2⟩
  choose m n σ a hσ ha hb hGm hEk hMk using hstep
  have hinv : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  refine ⟨n, σ, a, hσ, ha, hb, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · have hbound : ∀ᶠ k in atTop,
        P {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t} ≤ ((k : ℝ≥0∞) + 1)⁻¹ := by
      filter_upwards [hinv.eventually (gt_mem_nhds hε)] with k hk
      have hsub : {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
            ∂timeMeasure t} ⊆
          (G (m k))ᶜ ∪ {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤
            ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - Hseq (m k) s ω‖ₑ ^ 2
              ∂timeMeasure t} := by
        intro ω hω
        by_cases hGω : ω ∈ G (m k)
        · right
          have hHeq_ae : (fun s ↦ Hseq (m k) s ω) =ᵐ[timeMeasure t] fun s ↦ H s ω := by
            have hmeas : Measurable (fun s ↦ ‖Hseq (m k) s ω - H s ω‖ₑ ^ 2) :=
              (((((hU (m k)).isStronglyPredictable.sub hH).mono
                ℱ.predictable_le_prod).comp_measurable
                  measurable_prodMk_right).measurable.eNorm.pow_const 2)
            filter_upwards [(lintegral_eq_zero_iff hmeas).mp hGω.2] with s hs
            have hnorm : ‖Hseq (m k) s ω - H s ω‖ₑ = 0 := by
              simpa only [Pi.zero_apply, pow_eq_zero_iff (by norm_num : 2 ≠ 0)] using hs
            exact sub_eq_zero.mp (eNorm_eq_zero.mp hnorm)
          have hlint : (∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
                ∂timeMeasure t) =
              ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - Hseq (m k) s ω‖ₑ ^ 2
                ∂timeMeasure t :=
            lintegral_congr_ae (hHeq_ae.mono fun s hs ↦ by dsimp only at hs ⊢; rw [hs])
          exact hk.le.trans (hlint ▸ hω)
        · exact Or.inl hGω
      calc P _ ≤ P (G (m k))ᶜ + P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤
              ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - Hseq (m k) s ω‖ₑ ^ 2
                ∂timeMeasure t} := (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ ((k : ℝ≥0∞) + 1)⁻¹ / 2 + ((k : ℝ≥0∞) + 1)⁻¹ / 2 := add_le_add (hGm k).le (hEk k).le
        _ = ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.add_halves _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
      (Eventually.of_forall fun _ ↦ zero_le) hbound
  · let N : Set Ω := {ω | ¬ ∀ j, stoppedProcess I (τ j) t ω = U j t ω}
    have hN : P N = 0 := by
      have hae : ∀ᵐ ω ∂P, ∀ j, stoppedProcess I (τ j) t ω = U j t ω :=
        (ae_all_iff.mpr hstop).mono fun ω hω j ↦ hω j t
      exact ae_iff.mp hae
    have hbound : ∀ᶠ k in atTop,
        P {ω | ε ≤ edist (Finance.simpleGains (σ k) (n k) (a k) W t ω) (I t ω)} ≤
          ((k : ℝ≥0∞) + 1)⁻¹ := by
      filter_upwards [hinv.eventually (gt_mem_nhds hε)] with k hk
      have hsub : {ω | ε ≤ edist (Finance.simpleGains (σ k) (n k) (a k) W t ω) (I t ω)} ⊆
          N ∪ ((G (m k))ᶜ ∪ {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤
            edist (Finance.simpleGains (σ k) (n k) (a k) W t ω) (U (m k) t ω)}) := by
        intro ω hω
        by_cases hNω : ω ∈ N
        · exact Or.inl hNω
        · right
          by_cases hGω : ω ∈ G (m k)
          · right
            have hIU : I t ω = U (m k) t ω := by
              have h1 : stoppedProcess I (τ (m k)) t ω = U (m k) t ω :=
                (not_not.mp hNω) (m k)
              rwa [stoppedProcess_eq_of_le hGω.1.le] at h1
            exact hk.le.trans (hIU ▸ hω)
          · exact Or.inl hGω
      calc P _ ≤ P N + (P (G (m k))ᶜ + P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤
              edist (Finance.simpleGains (σ k) (n k) (a k) W t ω) (U (m k) t ω)}) :=
            (measure_mono hsub).trans ((measure_union_le _ _).trans
              (add_le_add_right (measure_union_le _ _) _))
        _ ≤ 0 + (((k : ℝ≥0∞) + 1)⁻¹ / 2 + ((k : ℝ≥0∞) + 1)⁻¹ / 2) := by
            rw [hN]
            exact add_le_add_right (add_le_add (hGm k).le (hMk k).le) _
        _ = ((k : ℝ≥0∞) + 1)⁻¹ := by rw [zero_add, ENNReal.add_halves]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
      (Eventually.of_forall fun _ ↦ zero_le) hbound

/-! ### Stopping compatibility for L² Itô integrals -/

namespace IsFilteredPreBrownianReal

private theorem coe_le_dyadicCeilTime_iff_gt_dyadic (m k : ℕ) {t : ℝ≥0}
    (ht : t ∈ Ioc ((k : ℝ≥0) / 2 ^ m) (((k + 1 : ℕ) : ℝ≥0) / 2 ^ m)) (u : WithTop ℝ≥0) :
    (t : WithTop ℝ≥0) ≤ dyadicCeilTime m u ↔
      (((k : ℝ≥0) / 2 ^ m : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m u := by
  cases u with
  | top =>
    rw [dyadicCeilTime_top]
    exact iff_of_true le_top (WithTop.coe_lt_top _)
  | coe r =>
    simp only [dyadicCeilTime_coe, WithTop.coe_le_coe, WithTop.coe_lt_coe]
    have hpos : (0 : ℝ≥0) < 2 ^ m := by positivity
    rw [div_lt_div_iff_of_pos_right hpos, Nat.cast_lt, le_div_iff₀ hpos]
    have h1 : (k : ℝ≥0) < t * 2 ^ m := (div_lt_iff₀ hpos).mp ht.1
    have h2 : t * 2 ^ m ≤ ((k + 1 : ℕ) : ℝ≥0) := (le_div_iff₀ hpos).mp ht.2
    constructor
    · intro hle
      exact Nat.cast_lt.mp (h1.trans_le hle)
    · intro hlt
      exact h2.trans (Nat.cast_le.mpr hlt)

private theorem ae_mem_Ioc_predictableMeasure [SFinite P] (T : ℝ≥0) :
    ∀ᵐ p : ℝ≥0 × Ω ∂ℱ.predictableMeasure P T, p.1 ∈ Ioc 0 T := by
  rw [ae_iff, ℱ.predictableMeasure_def]
  have hset : {p : ℝ≥0 × Ω | p.1 ∉ Ioc 0 T} = (Ioc 0 T ×ˢ (univ : Set Ω))ᶜ := by
    ext ⟨t, ω⟩; simp
  have hmeas : MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | p.1 ∉ Ioc 0 T} := by
    rw [hset]
    exact (measurableSet_predictable_Ioc_prod 0 T
      (MeasurableSet.univ : MeasurableSet[ℱ 0] univ)).compl
  rw [trim_measurableSet_eq ℱ.predictable_le_prod hmeas]
  have heq : {p : ℝ≥0 × Ω | p.1 ∉ Ioc 0 T} = (Ioc 0 T)ᶜ ×ˢ univ := by
    ext ⟨t, ω⟩; simp
  rw [heq, Measure.prod_prod, timeMeasure_def, Measure.restrict_apply measurableSet_Ioc.compl,
    compl_inter_self, measure_empty, zero_mul]

private theorem sum_dyadic_sub_eq (f : ℝ≥0 → ℝ) (m : ℕ) {T a b : ℝ≥0} (hab : a ≤ b)
    (u : WithTop ℝ≥0) :
    let d : ℕ → ℝ≥0 := fun k ↦ (k : ℝ≥0) / 2 ^ m
    let N : ℕ := ⌈T * 2 ^ m⌉₊
    let s : ℕ → ℝ≥0 := fun k ↦ max a (d k)
    let r : ℕ → ℝ≥0 := fun k ↦ max (s k) (min b (d (k + 1)))
    (∑ k ∈ Finset.range N,
        (if ((d k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m u then (1 : ℝ) else 0) *
          (f (min (r k) T) - f (min (s k) T))) =
      f (min b (min (T : WithTop ℝ≥0) (dyadicCeilTime m u)).untopA) -
        f (min a (min (T : WithTop ℝ≥0) (dyadicCeilTime m u)).untopA) := by
  intro d N s r
  let α : ℝ≥0 := min a T
  let β : ℝ≥0 := min b T
  have hαβ : α ≤ β := min_le_min_right T hab
  let g : ℕ → ℝ≥0 := fun k ↦ min β (max α (min (d k) T))
  have hterm (k : ℕ) : f (min (r k) T) - f (min (s k) T) = f (g (k + 1)) - f (g k) := by
    have hs : min (s k) T = max α (min (d k) T) := min_max_distrib_right a (d k) T
    have hmin_r : min (min b (d (k + 1))) T = min β (min (d (k + 1)) T) := by
      simp only [β, min_assoc, min_left_comm T (d (k + 1)), min_self]
    have hr : min (r k) T = max (max α (min (d k) T)) (min β (min (d (k + 1)) T)) := by
      dsimp only [r]
      rw [min_max_distrib_right, hs, hmin_r]
    have hxy : min (d k) T ≤ min (d (k + 1)) T :=
      min_le_min_right T (div_le_div_of_nonneg_right (Nat.cast_le.mpr k.le_succ) (by positivity))
    rw [hr, hs]
    dsimp only [g]
    rcases le_total β (max α (min (d k) T)) with h1 | h1
    · have h2 : β ≤ max α (min (d (k + 1)) T) := h1.trans (max_le_max_left α hxy)
      rw [max_eq_left ((min_le_left β _).trans h1), min_eq_left h1, min_eq_left h2,
        sub_self, sub_self]
    · rw [min_eq_right h1]
      rcases le_total (min (d (k + 1)) T) β with h2 | h2
      · rw [min_eq_right h2, max_assoc, max_eq_right hxy, min_eq_right (max_le hαβ h2)]
      · rw [min_eq_left h2, max_eq_right h1, min_eq_left (h2.trans (le_max_right α _))]
  have hg0 : g 0 = α := by
    dsimp only [g, d]
    rw [Nat.cast_zero, zero_div, min_eq_left (by positivity : (0 : ℝ≥0) ≤ T),
      max_eq_left (by positivity : (0 : ℝ≥0) ≤ α), min_eq_right hαβ]
  have hdk_lt (k : ℕ) (hk : k < N) : d k < T :=
    (div_lt_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ m)).mpr (Nat.lt_ceil.mp hk)
  have hT_le_dN : T ≤ d N := (le_div_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ m)).mpr (Nat.le_ceil _)
  rcases le_or_gt (T : WithTop ℝ≥0) (dyadicCeilTime m u) with hTu | hTu
  · have hmin : (min (T : WithTop ℝ≥0) (dyadicCeilTime m u)).untopA = T := by
      rw [min_eq_left hTu]; rfl
    rw [hmin]
    have hsum : (∑ k ∈ Finset.range N,
        (if ((d k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m u then (1 : ℝ) else 0) *
          (f (min (r k) T) - f (min (s k) T))) =
        ∑ k ∈ Finset.range N, (f (g (k + 1)) - f (g k)) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hlt : ((d k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m u :=
        (WithTop.coe_lt_coe.mpr (hdk_lt k (Finset.mem_range.mp hk))).trans_le hTu
      rw [ite_eq_left hlt, one_mul, hterm k]
    rw [hsum, Finset.sum_range_sub (fun k ↦ f (g k)) N, hg0]
    have hgN : g N = β := by
      dsimp only [g]
      rw [min_eq_right hT_le_dN, max_eq_right (min_le_right a T), min_eq_left (min_le_right b T)]
    rw [hgN]
  · cases u with
    | top =>
      rw [dyadicCeilTime_top] at hTu
      exact (not_lt_of_ge le_top hTu).elim
    | coe v =>
      let q : ℕ := ⌈v * 2 ^ m⌉₊
      have hdyad : dyadicCeilTime m (v : WithTop ℝ≥0) = ((d q : ℝ≥0) : WithTop ℝ≥0) := by
        rw [dyadicCeilTime_coe]
      have hqT : d q < T := WithTop.coe_lt_coe.mp (hdyad ▸ hTu)
      have hqN : q < N := Nat.lt_ceil.mpr ((div_lt_iff₀ (by positivity)).mp hqT)
      have hmin : (min (T : WithTop ℝ≥0) (dyadicCeilTime m (v : WithTop ℝ≥0))).untopA = d q := by
        rw [min_eq_right hTu.le, hdyad]; rfl
      rw [hmin]
      have hsum : (∑ k ∈ Finset.range N,
          (if ((d k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m (v : WithTop ℝ≥0) then (1 : ℝ)
              else 0) * (f (min (r k) T) - f (min (s k) T))) =
          ∑ k ∈ Finset.range q, (f (g (k + 1)) - f (g k)) := by
        rw [← Finset.sum_subset (Finset.range_mono hqN.le)]
        · refine Finset.sum_congr rfl fun k hk ↦ ?_
          have hlt : ((d k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m (v : WithTop ℝ≥0) := by
            rw [hdyad, WithTop.coe_lt_coe]
            exact div_lt_div_of_pos_right (Nat.cast_lt.mpr (Finset.mem_range.mp hk)) (by positivity)
          rw [ite_eq_left hlt, one_mul, hterm k]
        · intro k _ hk
          have hnot : ¬ ((d k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m (v : WithTop ℝ≥0) := by
            rw [hdyad, WithTop.coe_lt_coe, not_lt]
            exact div_le_div_of_nonneg_right
              (Nat.cast_le.mpr (not_lt.mp (mt Finset.mem_range.mpr hk))) (by positivity)
          rw [ite_eq_right hnot, zero_mul]
      rw [hsum, Finset.sum_range_sub (fun k ↦ f (g k)) q, hg0]
      rcases le_total a (d q) with haq | haq
      · have hgq : g q = min b (d q) := by
          simp only [g, β, α, min_eq_left hqT.le, min_eq_left (haq.trans hqT.le),
            max_eq_right haq, min_assoc, min_eq_right hqT.le]
        rw [hgq, min_eq_left haq]
        dsimp only [α]
        rw [min_eq_left (haq.trans hqT.le)]
      · have hgq : g q = α := by
          have hα : d q ≤ α := le_min haq hqT.le
          dsimp only [g]
          rw [min_eq_left hqT.le, max_eq_left hα, min_eq_right hαβ]
        rw [hgq, min_eq_right haq, min_eq_right (haq.trans hab), sub_self, sub_self]

private theorem brownianIntegrable_simpleHolding [IsFiniteMeasure P]
    {σ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (ha : ∀ j < n, StronglyMeasurable[ℱ (σ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) :
    BrownianIntegrable ℱ P (Finance.simpleHolding σ n a) :=
  ⟨Finance.isStronglyPredictable_simpleHolding ha, fun S ↦ by
    have h := Finance.memLp_simpleHolding_predictableMeasure ha ha₂ S
    rw [ℱ.memLp_predictableMeasure_iff P (Finance.isStronglyPredictable_simpleHolding ha) S 2] at h
    simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using h⟩

private theorem coeFn_l2Integral_ite_le_dyadicCeilTime_simpleHolding
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (m : ℕ)
    {σ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hσ : MonotoneOn σ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (σ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T ((((brownianIntegrable_simpleHolding ha ha₂).ite_le
        (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).toLp _) =ᵐ[P]
      stoppedProcess (Finance.simpleGains σ n a W) (fun ω ↦ dyadicCeilTime m (τ ω)) T := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hK := brownianIntegrable_simpleHolding ha ha₂
  let d : ℕ → ℝ≥0 := fun k ↦ (k : ℝ≥0) / 2 ^ m
  let N : ℕ := ⌈T * 2 ^ m⌉₊
  let A : ℕ → Set Ω := fun k ↦ {ω | ((d k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m (τ ω)}
  have hA_meas (k : ℕ) : MeasurableSet[ℱ (d k)] (A k) := by
    have h := ((hτ.dyadicCeilTime m) (d k)).compl
    simpa only [compl_ofPred, not_le] using h
  let s (j k : ℕ) : ℝ≥0 := max (σ j) (d k)
  let r (j k : ℕ) : ℝ≥0 := max (s j k) (min (σ (j + 1)) (d (k + 1)))
  let grid (j k : ℕ) : ℕ → ℝ≥0 := fun i ↦ if i = 0 then s j k else r j k
  have hgrid (j k : ℕ) : MonotoneOn (grid j k) (Iic 1) := by
    intro i₁ hi₁ i₂ hi₂ hle
    have hi₁' : i₁ ≤ 1 := mem_Iic.mp hi₁
    have hi₂' : i₂ ≤ 1 := mem_Iic.mp hi₂
    have h1 : i₁ = 0 ∨ i₁ = 1 := by omega
    have h2 : i₂ = 0 ∨ i₂ = 1 := by omega
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp [grid, r] at hle ⊢
  let ξ (j k : ℕ) (ω : Ω) : ℝ := (A k).indicator (a j) ω
  have hξ_sm (j : ℕ) (hj : j < n) (k : ℕ) : StronglyMeasurable[ℱ (s j k)] (ξ j k) :=
    ((ha j hj).mono (ℱ.mono (le_max_left _ _))).indicator
      (ℱ.mono (le_max_right _ _) _ (hA_meas k))
  have hξ_mem (j : ℕ) (hj : j < n) (k : ℕ) : MemLp (ξ j k) 2 P :=
    (ha₂ j hj).indicator (ℱ.le _ _ (hA_meas k)).nullMeasurableSet
  have hpiece_mem (j : ℕ) (hj : j < n) (k : ℕ) :
      MemLp (Function.uncurry (Finance.simpleHolding (grid j k) 1 (fun _ ↦ ξ j k))) 2
        (ℱ.predictableMeasure P T) :=
    Finance.memLp_simpleHolding_predictableMeasure
      (fun i hi ↦ by
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0; simpa [grid] using hξ_sm j hj k)
      (fun _ _ ↦ hξ_mem j hj k) T
  let f (p : ℕ × ℕ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    if h : p.1 < n then (hpiece_mem p.1 h p.2).toLp _ else 0
  let Hcut : ℝ≥0 → Ω → ℝ := fun t ω ↦
    if (t : WithTop ℝ≥0) ≤ dyadicCeilTime m (τ ω) then Finance.simpleHolding σ n a t ω else 0
  have hsum_Lp :
      ((hK.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).toLp (Function.uncurry Hcut) =
        ∑ p ∈ Finset.range n ×ˢ Finset.range N, f p := by
    apply Lp.ext
    have hterms : ∀ p ∈ Finset.range n ×ˢ Finset.range N,
        (f p : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
          Function.uncurry (Finance.simpleHolding (grid p.1 p.2) 1 (fun _ ↦ ξ p.1 p.2)) := by
      intro p hp
      have hp1 : p.1 < n := Finset.mem_range.mp (Finset.mem_product.mp hp).1
      have hfp : f p = (hpiece_mem p.1 hp1 p.2).toLp _ := by simp [f, hp1]
      rw [hfp]
      exact (hpiece_mem p.1 hp1 p.2).coeFn_toLp
    refine ((hK.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).coeFn_toLp.trans ?_
    filter_upwards [ae_mem_Ioc_predictableMeasure (ℱ := ℱ) (P := P) T,
      Lp.coeFn_finsetSum (s := Finset.range n ×ˢ Finset.range N) f,
      eventuallyEq_sum hterms] with ⟨t, ω⟩ hxT hsumx htx
    rw [hsumx, htx]
    simp only [Finset.sum_apply, Finset.sum_product, Function.uncurry_apply_pair,
      Finance.simpleHolding_def, Finset.range_one, Finset.sum_singleton, grid, ↓reduceIte,
      zero_add, one_ne_zero, Set.indicator_apply]
    dsimp only at hxT
    have h2pos : (0 : ℝ≥0) < 2 ^ m := by positivity
    let k₀ : ℕ := ⌈t * 2 ^ m⌉₊ - 1
    have hceil_pos : 0 < ⌈t * 2 ^ m⌉₊ := Nat.ceil_pos.mpr (mul_pos hxT.1 h2pos)
    have hk₀ : k₀ ∈ Finset.range N := Finset.mem_range.mpr <| by
      have hle : ⌈t * 2 ^ m⌉₊ ≤ N :=
        Nat.ceil_mono (mul_le_mul_of_nonneg_right hxT.2 h2pos.le)
      omega
    have hxk₀ : t ∈ Ioc (d k₀) (d (k₀ + 1)) := by
      refine ⟨(div_lt_iff₀ h2pos).mpr (Nat.lt_ceil.mp (Nat.sub_lt hceil_pos zero_lt_one)),
        (le_div_iff₀ h2pos).mpr ?_⟩
      simpa only [k₀, Nat.sub_add_cancel hceil_pos] using Nat.le_ceil (t * 2 ^ m)
    have hiff := coe_le_dyadicCeilTime_iff_gt_dyadic m k₀ hxk₀ (τ ω)
    have hrhs (j : ℕ) :
        (∑ k ∈ Finset.range N,
          if t ∈ Ioc (s j k) (r j k) then ξ j k ω else 0) =
        if (t : WithTop ℝ≥0) ≤ dyadicCeilTime m (τ ω) then
          if t ∈ Ioc (σ j) (σ (j + 1)) then a j ω else 0
        else 0 := by
      rw [Finset.sum_eq_single k₀]
      · have hmem : t ∈ Ioc (s j k₀) (r j k₀) ↔ t ∈ Ioc (σ j) (σ (j + 1)) := by
          simp only [mem_Ioc, s, r, max_lt_iff, le_max_iff, le_min_iff]
          constructor
          · rintro ⟨⟨h1, _⟩, (h2 | h2) | ⟨h2, _⟩⟩
            · exact False.elim (h1.not_ge h2)
            · exact False.elim (hxk₀.1.not_ge h2)
            · exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨⟨h1, hxk₀.1⟩, Or.inr ⟨h2, hxk₀.2⟩⟩
        by_cases hcond : (t : WithTop ℝ≥0) ≤ dyadicCeilTime m (τ ω)
        · rw [ite_eq_left hcond]
          have hA : ω ∈ A k₀ := hiff.mp hcond
          by_cases hJ : t ∈ Ioc (σ j) (σ (j + 1))
          · simp [hJ, hmem.mpr hJ, ξ, hA]
          · simp [hJ, mt hmem.mp hJ]
        · rw [ite_eq_right hcond]
          have hA : ω ∉ A k₀ := mt hiff.mpr hcond
          simp [ξ, hA]
      · intro k _ hne
        have hnot : t ∉ Ioc (s j k) (r j k) := by
          intro hmem
          have h1 : d k < t := (le_max_right _ _).trans_lt hmem.1
          have h2 : t ≤ d (k + 1) := by
            rcases le_max_iff.mp hmem.2 with hle | hle
            · exact False.elim (hmem.1.not_ge hle)
            · exact hle.trans (min_le_right _ _)
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · have hle : d (k + 1) ≤ d k₀ :=
              div_le_div_of_nonneg_right (Nat.cast_le.mpr hlt) h2pos.le
            exact (h2.trans hle).not_gt hxk₀.1
          · have hle : d (k₀ + 1) ≤ d k :=
              div_le_div_of_nonneg_right (Nat.cast_le.mpr hlt) h2pos.le
            exact (hxk₀.2.trans hle).not_gt h1
        simp [hnot]
      · intro hnot
        exact (hnot hk₀).elim
    simp_rw [hrhs]
    by_cases hcond : (t : WithTop ℝ≥0) ≤ dyadicCeilTime m (τ ω)
    · rw [ite_eq_left hcond]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [ite_eq_left hcond]
    · rw [ite_eq_right hcond]
      symm
      exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right hcond
  rw [hsum_Lp, map_sum]
  have heach : ∀ p ∈ Finset.range n ×ˢ Finset.range N,
      (hW.l2Integral T (f p) : Ω → ℝ) =ᵐ[P] fun ω ↦
        ξ p.1 p.2 ω * (W (min (r p.1 p.2) T) ω - W (min (s p.1 p.2) T) ω) := by
    intro p hp
    have hp1 : p.1 < n := Finset.mem_range.mp (Finset.mem_product.mp hp).1
    have hfp : f p = (hpiece_mem p.1 hp1 p.2).toLp _ := by simp [f, hp1]
    rw [hfp]
    have h1 := hW.coeFn_l2Integral_simpleHolding (hgrid p.1 p.2)
      (fun i hi ↦ by
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0; simpa [grid] using hξ_sm p.1 hp1 p.2)
      (fun _ _ ↦ hξ_mem p.1 hp1 p.2) T
    filter_upwards [h1] with ω hω
    simpa only [Finance.simpleGains_def, Finset.range_one, Finset.sum_singleton, grid, ↓reduceIte,
      zero_add, one_ne_zero] using hω
  filter_upwards [Lp.coeFn_finsetSum (s := Finset.range n ×ˢ Finset.range N)
      (fun p ↦ hW.l2Integral T (f p)), eventuallyEq_sum heach] with ω hω hsumω
  rw [hω, hsumω]
  simp only [Finset.sum_apply, Finset.sum_product, stoppedProcess_eq_stoppedValue_apply,
    stoppedValue, Finance.simpleGains_def]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hle : σ j ≤ σ (j + 1) := hσ (mem_Iic.mpr hj'.le) (mem_Iic.mpr hj') (Nat.le_succ j)
  have hpull : (∑ k ∈ Finset.range N,
        ξ j k ω * (W (min (r j k) T) ω - W (min (s j k) T) ω)) =
      a j ω * ∑ k ∈ Finset.range N,
        (if ((d k : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m (τ ω) then (1 : ℝ) else 0) *
          (W (min (r j k) T) ω - W (min (s j k) T) ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [ξ, A, indicator_apply, mem_ofPred_eq]
    split_ifs <;> ring
  rw [hpull, sum_dyadic_sub_eq (fun t ↦ W t ω) m hle (τ ω)]

private theorem untopA_min_dyadicCeilTime_mem (m : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0) :
    (min (T : WithTop ℝ≥0) (dyadicCeilTime m u)).untopA ∈
      insert T ((Finset.range ⌈T * 2 ^ m⌉₊).image fun q : ℕ ↦ (q : ℝ≥0) / 2 ^ m) := by
  rcases le_or_gt (T : WithTop ℝ≥0) (dyadicCeilTime m u) with h | h
  · have hmin : (min (T : WithTop ℝ≥0) (dyadicCeilTime m u)).untopA = T := by
      rw [min_eq_left h]; rfl
    rw [hmin]
    exact Finset.mem_insert_self T _
  · cases u with
    | top =>
      rw [dyadicCeilTime_top] at h
      exact (not_lt_of_ge le_top h).elim
    | coe r =>
      let d : ℕ → ℝ≥0 := fun q ↦ (q : ℝ≥0) / 2 ^ m
      let q : ℕ := ⌈r * 2 ^ m⌉₊
      have hdyad : dyadicCeilTime m (r : WithTop ℝ≥0) = ((d q : ℝ≥0) : WithTop ℝ≥0) := by
        rw [dyadicCeilTime_coe]
      have hqT : d q < T := WithTop.coe_lt_coe.mp (hdyad ▸ h)
      have hqN : q < ⌈T * 2 ^ m⌉₊ := Nat.lt_ceil.mpr ((div_lt_iff₀ (by positivity)).mp hqT)
      have hmin : (min (T : WithTop ℝ≥0) (dyadicCeilTime m (r : WithTop ℝ≥0))).untopA = d q := by
        rw [min_eq_right h.le, hdyad]; rfl
      rw [hmin]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem d (Finset.mem_range.mpr hqN))

private theorem stronglyMeasurable_stoppedProcess_dyadicCeilTime
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (m : ℕ) (T : ℝ≥0) :
    StronglyMeasurable (stoppedProcess X (fun ω ↦ dyadicCeilTime m (τ ω)) T) := by
  let S : Finset ℝ≥0 := insert T ((Finset.range ⌈T * 2 ^ m⌉₊).image fun q : ℕ ↦ (q : ℝ≥0) / 2 ^ m)
  let tval (ω : Ω) : ℝ≥0 := (min (T : WithTop ℝ≥0) (dyadicCeilTime m (τ ω))).untopA
  have htval_meas (u : ℝ≥0) : MeasurableSet {ω | tval ω = u} := by
    have hmin_meas : Measurable (fun ω ↦ min (T : WithTop ℝ≥0) (dyadicCeilTime m (τ ω))) :=
      measurable_const.min (hτ.dyadicCeilTime m).measurable'
    have heq : {ω | tval ω = u} =
        {ω | min (T : WithTop ℝ≥0) (dyadicCeilTime m (τ ω)) = (u : WithTop ℝ≥0)} := by
      ext ω
      have hne : min (T : WithTop ℝ≥0) (dyadicCeilTime m (τ ω)) ≠ ⊤ :=
        ne_of_lt ((min_le_left _ _).trans_lt (WithTop.coe_lt_top T))
      simp only [mem_ofPred_eq, tval]
      cases hmin : min (T : WithTop ℝ≥0) (dyadicCeilTime m (τ ω)) with
      | top => exact (hne hmin).elim
      | coe a =>
        simp only [WithTop.untopA, WithTop.untopD_coe, WithTop.coe_eq_coe]
    rw [heq]
    exact hmin_meas (measurableSet_singleton _)
  have heq : stoppedProcess X (fun ω ↦ dyadicCeilTime m (τ ω)) T =
      fun ω ↦ ∑ u ∈ S, {ω | tval ω = u}.indicator (X u) ω := by
    ext ω
    rw [Finset.sum_eq_single (tval ω)]
    · simp [stoppedProcess, tval]
    · intro u _ hne; simp [Ne.symm hne]
    · intro hnot; exact (hnot (untopA_min_dyadicCeilTime_mem m T (τ ω))).elim
  rw [heq]
  exact Finset.stronglyMeasurable_fun_sum S fun u _ ↦
    ((hX u).mono (ℱ.le u)).indicator (htval_meas u)

private theorem ae_eq_stoppedProcess_dyadicCeilTime_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adapt : StronglyAdapted ℱ I) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (m : ℕ) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).toLp _) =ᵐ[P]
      stoppedProcess I (fun ω ↦ dyadicCeilTime m (τ ω)) T := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime m (τ ω)
  have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime m
  obtain ⟨n, g, a, C, -, hg, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    (memLp_const (C k)).mono' ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable
      (Eventually.of_forall (hb k j hj))
  let M (k : ℕ) : ℝ≥0 → Ω → ℝ := Finance.simpleGains (g k) (n k) (a k) W
  let L : Ω → ℝ := hW.l2Integral T (((hH.ite_le hσ).memLp_predictableMeasure T).toLp _)
  let R : Ω → ℝ := stoppedProcess I σ T
  have hL_lim : Tendsto (fun k ↦ eLpNorm (L - stoppedProcess (M k) σ T) 2 P) atTop (𝓝 0) := by
    have hK (k : ℕ) : BrownianIntegrable ℱ P (Finance.simpleHolding (g k) (n k) (a k)) :=
      brownianIntegrable_simpleHolding (ha k) (ha₂ k)
    have hle (k : ℕ) : eLpNorm (L - stoppedProcess (M k) σ T) 2 P ≤
        eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (g k) (n k) (a k) p.1 p.2 - H p.1 p.2)
          2 ((timeMeasure T).prod P) := by
      let fH := ((hH.ite_le hσ).memLp_predictableMeasure T).toLp _
      let fK := (((hK k).ite_le hσ).memLp_predictableMeasure T).toLp _
      have heq1 : eLpNorm (L - stoppedProcess (M k) σ T) 2 P =
          edist (hW.l2Integral T fH) (hW.l2Integral T fK) := by
        rw [Lp.edist_def]
        exact eLpNorm_congr_ae (EventuallyEq.rfl.sub
          (hW.coeFn_l2Integral_ite_le_dyadicCeilTime_simpleHolding hτ m (hg k).monotoneOn
            (ha k) (ha₂ k) T).symm)
      rw [heq1, (hW.l2Integral T).isometry.edist_eq, Lp.edist_def]
      have heq2 : eLpNorm (⇑fH - ⇑fK) 2 (ℱ.predictableMeasure P T) =
          eLpNorm
            (Function.uncurry (fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0) -
              Function.uncurry (fun (t : ℝ≥0) ω ↦
                if (t : WithTop ℝ≥0) ≤ σ ω then
                  Finance.simpleHolding (g k) (n k) (a k) t ω else 0))
            2 (ℱ.predictableMeasure P T) :=
        eLpNorm_congr_ae (((hH.ite_le hσ).memLp_predictableMeasure T).coeFn_toLp.sub
          (((hK k).ite_le hσ).memLp_predictableMeasure T).coeFn_toLp)
      rw [heq2, ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod
        ((hH.ite_le hσ).isStronglyPredictable.sub ((hK k).ite_le hσ).isStronglyPredictable)]
      refine eLpNorm_mono ((((hH.ite_le hσ).isStronglyPredictable.sub
          ((hK k).ite_le hσ).isStronglyPredictable).mono
            ℱ.predictable_le_prod).aestronglyMeasurable) fun ⟨t, ω⟩ ↦ ?_
      dsimp only [Pi.sub_apply, Function.uncurry_apply_pair]
      split_ifs
      · rw [norm_sub_rev]
      · simp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim T)
      (fun _ ↦ zero_le) hle
  have hR_lim : Tendsto (fun k ↦ eLpNorm (stoppedProcess (M k) σ T - R) 2 P) atTop (𝓝 0) := by
    let S : Finset ℝ≥0 :=
      insert T ((Finset.range ⌈T * 2 ^ m⌉₊).image fun q : ℕ ↦ (q : ℝ≥0) / 2 ^ m)
    have hM_adapt (k : ℕ) : StronglyAdapted ℱ (M k) :=
      Finance.stronglyAdapted_simpleGains (hg k).monotoneOn (ha k)
        (fun t ↦ (hW.adapted t).stronglyMeasurable)
    have hle (k : ℕ) : eLpNorm (stoppedProcess (M k) σ T - R) 2 P ≤
        ∑ u ∈ S, eLpNorm (M k u - I u) 2 P := by
      have h1 : eLpNorm (stoppedProcess (M k) σ T - R) 2 P ≤
          eLpNorm (∑ u ∈ S, fun ω ↦ ‖(M k u - I u) ω‖) 2 P := by
        refine eLpNorm_mono
          (((stronglyMeasurable_stoppedProcess_dyadicCeilTime (hM_adapt k) hτ m T).sub
            (stronglyMeasurable_stoppedProcess_dyadicCeilTime hI_adapt hτ m
              T)).aestronglyMeasurable)
          fun ω ↦ ?_
        rw [Finset.sum_apply,
          Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
        let tval : ℝ≥0 := (min (T : WithTop ℝ≥0) (σ ω)).untopA
        have heq : ‖(stoppedProcess (M k) σ T - R) ω‖ = ‖(M k tval - I tval) ω‖ := rfl
        rw [heq]
        exact Finset.single_le_sum (f := fun u ↦ ‖(M k u - I u) ω‖) (fun _ _ ↦ norm_nonneg _)
          (untopA_min_dyadicCeilTime_mem m T (τ ω))
      refine h1.trans ((eLpNorm_sum_le one_le_two).trans_eq (Finset.sum_congr rfl fun u _ ↦ ?_))
      exact eLpNorm_norm (M k u - I u)
        (((hM_adapt k u).mono (ℱ.le u)).sub ((hI_adapt u).mono (ℱ.le u))).aestronglyMeasurable
    have hterm_lim (u : ℝ≥0) : Tendsto (fun k ↦ eLpNorm (M k u - I u) 2 P) atTop (𝓝 0) := by
      have heq (k : ℕ) : eLpNorm (M k u - I u) 2 P =
          eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (g k) (n k) (a k) p.1 p.2 - H p.1 p.2)
            2 ((timeMeasure u).prod P) := by
        let fK := (Finance.memLp_simpleHolding_predictableMeasure (ha k) (ha₂ k) u).toLp _
        let fH := (hH.memLp_predictableMeasure u).toLp (Function.uncurry H)
        have h1 : eLpNorm (M k u - I u) 2 P = edist (hW.l2Integral u fK) (hW.l2Integral u fH) := by
          rw [Lp.edist_def]
          exact eLpNorm_congr_ae
            ((hW.coeFn_l2Integral_simpleHolding (hg k).monotoneOn (ha k) (ha₂ k) u).symm.sub
              (hW.ae_eq_l2Integral_of_isItoIntegral hH hI u))
        rw [h1, (hW.l2Integral u).isometry.edist_eq, Lp.edist_def]
        have h2 : eLpNorm (⇑fK - ⇑fH) 2 (ℱ.predictableMeasure P u) =
            eLpNorm (fun p : ℝ≥0 × Ω ↦
              Finance.simpleHolding (g k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2
              (ℱ.predictableMeasure P u) :=
          eLpNorm_congr_ae
            ((Finance.memLp_simpleHolding_predictableMeasure (ha k) (ha₂ k) u).coeFn_toLp.sub
              (hH.memLp_predictableMeasure u).coeFn_toLp)
        rw [h2, ℱ.predictableMeasure_def]
        exact eLpNorm_trim ℱ.predictable_le_prod
          ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub hH.isStronglyPredictable)
      simpa only [heq] using hlim u
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [Finset.sum_const_zero] using tendsto_finsetSum S fun u _ ↦ hterm_lim u)
      (fun _ ↦ zero_le) hle
  have hzero : eLpNorm (L - R) 2 P = 0 := by
    have htri (k : ℕ) : eLpNorm (L - R) 2 P ≤
        eLpNorm (L - stoppedProcess (M k) σ T) 2 P +
          eLpNorm (stoppedProcess (M k) σ T - R) 2 P := by
      have hsplit : L - R = (L - stoppedProcess (M k) σ T) + (stoppedProcess (M k) σ T - R) := by
        ext ω; simp
      rw [hsplit]
      exact eLpNorm_add_le one_le_two
    have hlim0 : Tendsto (fun _ : ℕ ↦ eLpNorm (L - R) 2 P) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hL_lim.add hR_lim) (fun _ ↦ zero_le) htri
    exact tendsto_nhds_unique tendsto_const_nhds hlim0
  exact ((eLpNorm_eq_zero_iff (by norm_num)).mp hzero).mono fun ω hω ↦ sub_eq_zero.mp hω

/-- **Stopping compatibility for L² Itô integrals.** For a Brownian-integrable integrand `H`, a
strongly adapted Itô integral `I`, and any stopping time `τ`, the stopped process
`stoppedProcess I τ` is an Itô integral of the cutoff integrand `1_{[0, τ]} H`. Path continuity of
`W` is not required. -/
theorem isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adapt : StronglyAdapted ℱ I) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (stoppedProcess I τ) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hstop_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ stoppedProcess I τ t ω) :=
    hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess
  refine (hW.isItoIntegral_iff_ae_eq_l2Integral (hH.ite_le hτ) hstop_cont).mpr fun T ↦ ?_
  let Hτ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0
  let Hm (m : ℕ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
    if (t : WithTop ℝ≥0) ≤ dyadicCeilTime m (τ ω) then H t ω else 0
  let Lm (m : ℕ) : Ω → ℝ :=
    hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).toLp _)
  let L : Ω → ℝ := hW.l2Integral T (((hH.ite_le hτ).memLp_predictableMeasure T).toLp _)
  have hL_lim : Tendsto (fun m ↦ eLpNorm (Lm m - L) 2 P) atTop (𝓝 0) := by
    have heq (m : ℕ) : eLpNorm (Lm m - L) 2 P =
        eLpNorm (fun p : ℝ≥0 × Ω ↦ Hm m p.1 p.2 - Hτ p.1 p.2) 2 ((timeMeasure T).prod P) := by
      let fm := ((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).toLp _
      let f0 := ((hH.ite_le hτ).memLp_predictableMeasure T).toLp _
      have h1 : eLpNorm (Lm m - L) 2 P = edist (hW.l2Integral T fm) (hW.l2Integral T f0) := by
        rw [Lp.edist_def]
      rw [h1, (hW.l2Integral T).isometry.edist_eq, Lp.edist_def]
      have h2 : eLpNorm (⇑fm - ⇑f0) 2 (ℱ.predictableMeasure P T) =
          eLpNorm (fun p : ℝ≥0 × Ω ↦ Hm m p.1 p.2 - Hτ p.1 p.2) 2
            (ℱ.predictableMeasure P T) :=
        eLpNorm_congr_ae
          (((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).coeFn_toLp.sub
            ((hH.ite_le hτ).memLp_predictableMeasure T).coeFn_toLp)
      rw [h2, ℱ.predictableMeasure_def]
      exact eLpNorm_trim ℱ.predictable_le_prod
        ((hH.ite_le (hτ.dyadicCeilTime m)).isStronglyPredictable.sub
          (hH.ite_le hτ).isStronglyPredictable)
    simp_rw [heq]
    have hHmem : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using hH.memLp T
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (Eventually.of_forall fun m ↦ (((hH.ite_le (hτ.dyadicCeilTime m)).isStronglyPredictable).mono
        ℱ.predictable_le_prod).aestronglyMeasurable) hHmem
      (Eventually.of_forall fun m ↦ Eventually.of_forall fun p ↦ by
        simp only [Hm, Hτ, ENNReal.coe_one, one_mul]
        split_ifs <;> simp [Function.uncurry_def])
      (Eventually.of_forall fun p ↦ ?_)
    by_cases hp : (p.1 : WithTop ℝ≥0) ≤ τ p.2
    · refine tendsto_const_nhds.congr fun m ↦ ?_
      have hm : (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime m (τ p.2) :=
        hp.trans (le_dyadicCeilTime m (τ p.2))
      dsimp only [Hm, Hτ]
      rw [ite_eq_left hp, ite_eq_left hm]
    · refine tendsto_const_nhds.congr' ?_
      have hlt : τ p.2 < (p.1 : WithTop ℝ≥0) := not_le.mp hp
      filter_upwards [(tendsto_dyadicCeilTime (τ p.2)).eventually (gt_mem_nhds hlt)] with m hm
      dsimp only [Hm, Hτ]
      rw [ite_eq_right hp, ite_eq_right (not_le.mpr hm)]
  have hR_lim : Tendsto (fun m ↦ eLpNorm
      (stoppedProcess I (fun ω ↦ dyadicCeilTime m (τ ω)) T - stoppedProcess I τ T) 2 P)
      atTop (𝓝 0) :=
    (hW.martingale_of_isItoIntegral hH hI hI_adapt).tendsto_eLpNorm_stoppedProcess_dyadicCeilTime
      (hI.ae_continuous.mono fun _ hω ↦ hω.isRightContinuous) hτ T one_le_two (by norm_num)
      (hW.memLp_of_isItoIntegral hH hI T)
  have hzero : eLpNorm (stoppedProcess I τ T - L) 2 P = 0 := by
    have htri (m : ℕ) : eLpNorm (stoppedProcess I τ T - L) 2 P ≤
        eLpNorm (stoppedProcess I (fun ω ↦ dyadicCeilTime m (τ ω)) T - stoppedProcess I τ T) 2 P +
          eLpNorm (Lm m - L) 2 P := by
      have hsub : eLpNorm (stoppedProcess I τ T - L) 2 P =
          eLpNorm ((stoppedProcess I τ T - stoppedProcess I (fun ω ↦ dyadicCeilTime m (τ ω)) T) +
            (Lm m - L)) 2 P := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [hW.ae_eq_stoppedProcess_dyadicCeilTime_of_brownianIntegrable
          hH hI hI_adapt hτ m T] with ω hω
        dsimp only [Lm, Pi.sub_apply, Pi.add_apply] at hω ⊢
        rw [hω]
        ring
      rw [hsub]
      refine (eLpNorm_add_le one_le_two).trans ?_
      gcongr
      rw [← eLpNorm_neg, neg_sub]
    have hlim0 : Tendsto (fun _ : ℕ ↦ eLpNorm (stoppedProcess I τ T - L) 2 P) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hR_lim.add hL_lim) (fun _ ↦ zero_le) htri
    exact tendsto_nhds_unique tendsto_const_nhds hlim0
  exact ((eLpNorm_eq_zero_iff (by norm_num)).mp hzero).mono fun ω hω ↦ sub_eq_zero.mp hω

/-! ### General existence, native local-martingale property, stopping, and square compensation -/

/-- Shared energy-localization construction producing the patched predictable Itô integral and
its compatible `L²` martingale stages along the closed-level energy localizers. -/
private theorem exists_energyLocalized_integrals (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    let σ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
    let Hseq : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦
      if (t : WithTop ℝ≥0) ≤ σ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
    ∃ (I : ℝ≥0 → Ω → ℝ) (U : ℕ → ℝ≥0 → Ω → ℝ),
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      (∀ n, IsItoIntegral ℱ P W (Hseq n) (U n)) ∧
      (∀ n, IsStronglyPredictable ℱ (U n)) ∧
      (∀ n, Martingale (U n) ℱ P) ∧
      (∀ n, stoppedProcess I (σ n) ≡ᵐ[P] U n) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let σ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  let Hseq : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦
    if (t : WithTop ℝ≥0) ≤ σ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
  have hloc : IsLocalizingSequence ℱ σ P := hH.isLocalizingSequence_energyLocalizer
  have hHseq (n : ℕ) : BrownianIntegrable ℱ P (Hseq n) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)
  have hex (n : ℕ) := hW.exists_isItoIntegral_of_brownianIntegrable hcont (hHseq n)
  choose U hUI hUpred hUmart using hex
  have hcompat (m n : ℕ) (hmn : m ≤ n) : stoppedProcess (U n) (σ m) ≡ᵐ[P] U m := by
    have hσ_le : ∀ ω, σ m ω ≤ σ n ω := fun ω ↦
      nnvolume.monotone_energyLocalizer H ω (add_le_add_left (Nat.cast_le.mpr hmn) 1)
    have hHeq : (fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ σ m ω then Hseq n t ω else 0) =
        Hseq m := by
      ext t ω
      dsimp only [Hseq]
      by_cases ht : (t : WithTop ℝ≥0) ≤ σ m ω
      · rw [ite_eq_left ht, ite_eq_left (ht.trans (hσ_le ω)), ite_eq_left ht]
      · rw [ite_eq_right ht, ite_eq_right ht]
    have hstopI : IsItoIntegral ℱ P W (Hseq m) (stoppedProcess (U n) (σ m)) := by
      rw [← hHeq]
      exact hW.isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable (hHseq n) (hUI n)
        (hUpred n).isStronglyProgressive.stronglyAdapted (hloc.isStoppingTime m)
    exact hW.isItoIntegral_unique hstopI (hUI m)
  obtain ⟨V, hVprog, hVcont, hVstop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hloc.tendsto_top (fun n ↦ (hUpred n).isStronglyProgressive) (fun n ↦ (hUI n).ae_continuous)
    hcompat
  obtain ⟨I, hIpred, hIcont, hIV⟩ :=
    hVprog.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_continuous hVcont
  have hIstop (n : ℕ) : stoppedProcess I (σ n) ≡ᵐ[P] U n := by
    filter_upwards [hIV, hVstop n] with ω hω hVω t
    simpa only [stoppedProcess, hω] using hVω t
  have hII : IsItoIntegral ℱ P W H I :=
    IsItoIntegral.of_stoppedProcess hH.isStronglyPredictable hIcont
      (fun n ↦ (hloc.isStoppingTime n).measurable') hloc.tendsto_top hUI hIstop
      hH.ae_eventually_ite_le_energyLocalizer_eqOn
  exact ⟨I, U, hII, hIpred, hUI, hUpred, hUmart, hIstop⟩

/-- **Existence of the general Itô stochastic integral.** Every locally Brownian-integrable
process against an almost surely continuous filtered pre-Brownian motion admits a predictable,
almost surely continuous Itô integral that is a native local martingale on the raw filtration.
Neither completeness nor right continuity of the filtration is required. -/
theorem exists_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ,
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
        Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  obtain ⟨I, U, hII, hIpred, -, -, hUmart, hIstop⟩ :=
    hW.exists_energyLocalized_integrals hcont hH
  refine ⟨I, hII, hIpred, ?_⟩
  refine hIpred.isStronglyProgressive.locally_martingale_of_ae_stopped_eq
    hH.isLocalizingSequence_energyLocalizer hUmart fun n t ↦ ?_
  filter_upwards [hIstop n] with ω hω
  have hpos : (⊥ : WithTop ℝ≥0) < nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω :=
    nnvolume.energyLocalizer_pos H (by positivity) ω
  rw [stoppedProcess_indicator_pos_apply, ite_eq_left hpos]
  exact (hω t).symm

/-- Every strongly progressive Itô integral against an almost surely continuous filtered
pre-Brownian motion is a native local martingale on the raw filtration. -/
theorem locally_martingale_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I) (hI_prog : IsStronglyProgressive ℱ I) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  obtain ⟨J, hJ, -, hJloc⟩ := hW.exists_isItoIntegral hcont hI.locallyBrownianIntegrable
  exact hI_prog.locally_martingale_of_indist hJloc (hW.isItoIntegral_unique hJ hI)

/-- **Stopping compatibility for general Itô integrals.** For any Itô integral `I` of `H` against
an almost surely continuous filtered pre-Brownian motion and any stopping time `τ`, the stopped
process `stoppedProcess I τ` is an Itô integral of the cutoff integrand `1_{[0, τ]} H`. -/
theorem isItoIntegral_ite_le_stoppedProcess (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (stoppedProcess I τ) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hH := hI.locallyBrownianIntegrable
  let σ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  let Hseq : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦
    if (t : WithTop ℝ≥0) ≤ σ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
  obtain ⟨I₀, U, hI₀, -, hUI, hUpred, -, hI₀stop⟩ :=
    hW.exists_energyLocalized_integrals hcont hH
  have hII₀ : I ≡ᵐ[P] I₀ := hW.isItoIntegral_unique hI hI₀
  have hloc := hH.isLocalizingSequence_energyLocalizer
  have hHseq (n : ℕ) : BrownianIntegrable ℱ P (Hseq n) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)
  refine IsItoIntegral.of_stoppedProcess (hH.ite_le hτ).isStronglyPredictable
    (hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess)
    (fun n ↦ (hloc.isStoppingTime n).measurable') hloc.tendsto_top
    (fun n ↦ hW.isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable (hHseq n) (hUI n)
      (hUpred n).isStronglyProgressive.stronglyAdapted hτ)
    (fun n ↦ ?_) ?_
  · filter_upwards [hII₀, hI₀stop n] with ω hω h0ω t
    have hcomm : stoppedProcess (stoppedProcess I τ) (σ n) t ω =
        stoppedProcess (stoppedProcess I (σ n)) τ t ω := by
      rw [stoppedProcess_stoppedProcess, stoppedProcess_stoppedProcess, inf_comm]
    rw [hcomm]
    have hstopω : ∀ u, stoppedProcess I (σ n) u ω = U n u ω := fun u ↦ by
      simpa only [stoppedProcess, hω] using h0ω u
    exact hstopω _
  · filter_upwards [hH.ae_eventually_ite_le_energyLocalizer_eqOn] with ω hω T
    filter_upwards [hω T] with n hn t ht
    by_cases h1 : (t : WithTop ℝ≥0) ≤ τ ω
    · simp only [ite_eq_left h1]
      exact hn ht
    · simp only [ite_eq_right h1]

/-- **Local-martingale Itô square compensation (quadratic variation bracket).** For any strongly
progressive Itô integral `I` of `H` against an almost surely continuous filtered pre-Brownian
motion, the process `I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` is a native local martingale on the
raw filtration. -/
theorem locally_martingale_sq_sub_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I) (hI_prog : IsStronglyProgressive ℱ I) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hH := hI.locallyBrownianIntegrable
  let σ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  let Hseq : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦
    if (t : WithTop ℝ≥0) ≤ σ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
  obtain ⟨I₀, U, hI₀, -, hUI, hUpred, -, hI₀stop⟩ :=
    hW.exists_energyLocalized_integrals hcont hH
  have hII₀ : I ≡ᵐ[P] I₀ := hW.isItoIntegral_unique hI hI₀
  have hHseq (n : ℕ) : BrownianIntegrable ℱ P (Hseq n) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)
  have hA_prog : IsStronglyProgressive ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    hH.isStronglyPredictable.isStronglyPredictable_integral_sq_timeMeasure.isStronglyProgressive
  have hX_prog : IsStronglyProgressive ℱ
      (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    fun t ↦ ((hI_prog t).pow 2).sub (hA_prog t)
  have hZ (n : ℕ) :
      Martingale (fun t ω ↦ U n t ω ^ 2 - ∫ s, Hseq n s ω ^ 2 ∂timeMeasure t) ℱ P :=
    hW.martingale_sq_sub_of_isItoIntegral (hHseq n) (hUI n)
      (hUpred n).isStronglyProgressive.stronglyAdapted
  refine hX_prog.locally_martingale_of_ae_stopped_eq
    hH.isLocalizingSequence_energyLocalizer hZ fun n t ↦ ?_
  filter_upwards [hII₀, hI₀stop n, hH.ae_accumulatedEnergy_lt_top] with ω hω h0ω hfin
  have hpos : (⊥ : WithTop ℝ≥0) < σ n ω := nnvolume.energyLocalizer_pos H (by positivity) ω
  rw [stoppedProcess_indicator_pos_apply, ite_eq_left hpos]
  let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (σ n ω)).untopA
  have hI_eq : U n t ω = I u ω := by
    have h1 := (h0ω t).symm
    simpa only [stoppedProcess, hω] using h1
  have hE_eq : (∫ s, Hseq n s ω ^ 2 ∂timeMeasure t) = ∫ s, H s ω ^ 2 ∂timeMeasure u := by
    rw [(hHseq n).isStronglyPredictable.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy t ω,
      hH.isStronglyPredictable.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy u ω]
    congr 1
    have hclock : (fun v ω ↦ ∫⁻ s in Ioc 0 v, ‖nnvolume.finiteEnergyCutoff H s ω‖ₑ ^ 2 ∂nnvolume) =
        nnvolume.accumulatedEnergy (nnvolume.finiteEnergyCutoff H) :=
      funext fun v ↦ funext fun ω' ↦ (nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc _ v ω').symm
    have hstop_e := setLIntegral_ite_le_eq_stoppedProcess
      (fun s ω' ↦ ‖nnvolume.finiteEnergyCutoff H s ω'‖ₑ ^ 2) (σ n) nnvolume 0 t ω
    rw [hclock] at hstop_e
    have h1 : nnvolume.accumulatedEnergy (Hseq n) t ω =
        nnvolume.accumulatedEnergy (nnvolume.finiteEnergyCutoff H) u ω := by
      rw [nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc]
      simpa only [Hseq, apply_ite, eNorm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
        stoppedProcess] using hstop_e
    rw [h1, nnvolume.accumulatedEnergy_def, nnvolume.accumulatedEnergy_def]
    exact setLIntegral_congr_fun measurableSet_Iic fun s hs ↦ by
      have hfe := nnvolume.finiteEnergyCutoff_eqOn (hfin u) hs
      dsimp only at hfe
      rw [hfe]
  rw [hI_eq, hE_eq]

end IsFilteredPreBrownianReal

end TauCeti.Probability
