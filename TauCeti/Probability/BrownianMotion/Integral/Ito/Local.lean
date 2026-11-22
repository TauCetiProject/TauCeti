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
import TauCeti.Probability.BrownianMotion.Integral.Locality
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.Process.ElementaryDensity
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Martingale.Local.Congruence
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
    (measurableSet_lt measurable_const (hτ_meas m)).inter (hE_meas m (measurableSet_singleton 0))
  have hG_lim : Tendsto (fun m ↦ P (G m)ᶜ) atTop (𝓝 0) := by
    let B (m : ℕ) : Set Ω := ⋃ j ≥ m, (G j)ᶜ
    have hB_inter : P (⋂ m, B m) = 0 := by
      have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ m, B m := by
        filter_upwards [hτ, hHeq] with ω hτω hHω
        rw [mem_iInter, not_forall]
        obtain ⟨m, hm⟩ := eventually_atTop.mp
          ((hτω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).and (hHω t))
        refine ⟨m, ?_⟩
        simp only [B, mem_iUnion, mem_compl_iff, not_exists, not_not]
        intro j hj
        refine ⟨(hm j hj).left, ?_⟩
        have hzero : (fun s ↦ ‖Hseq j s ω - H s ω‖ₑ ^ 2) =ᵐ[timeMeasure t] 0 :=
          (ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ by simp [(hm j hj).right hs.right]
        simpa only [E, mem_ofPred_eq, Pi.zero_apply, lintegral_zero] using lintegral_congr_ae hzero
      simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hae
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hB_inter ▸ tendsto_measure_iInter_atTop (μ := P) (s := B)
        (fun m ↦ (MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦
          (hG_meas j).compl).nullMeasurableSet)
        (fun _ _ hle ↦ iUnion₂_mono' fun j hj ↦ ⟨j, hle.trans hj, subset_rfl⟩)
        ⟨0, measure_ne_top P (B 0)⟩)
      (fun _ ↦ zero_le) (fun m ↦ measure_mono (subset_iUnion₂_of_subset m le_rfl Subset.rfl))
  have hstep (k : ℕ) : ∃ m n σ a,
      MonotoneOn σ (Iic n) ∧ (∀ j < n, StronglyMeasurable[ℱ (σ j)] (a j)) ∧
      P (G m)ᶜ < ((k : ℝ≥0∞) + 1)⁻¹ / 2 ∧
      P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ ∫⁻ s, ‖Finance.simpleHolding σ n a s ω - Hseq m s ω‖ₑ ^ 2
          ∂timeMeasure t} < ((k : ℝ≥0∞) + 1)⁻¹ / 2 ∧
      P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ edist (Finance.simpleGains σ n a W t ω) (U m t ω)} <
        ((k : ℝ≥0∞) + 1)⁻¹ / 2 := by
    have hδ : 0 < ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.mpr (by simp)
    have hhalf : 0 < ((k : ℝ≥0∞) + 1)⁻¹ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
    obtain ⟨m, hm⟩ := (hG_lim.eventually (gt_mem_nhds hhalf)).exists
    obtain ⟨n', σ', a', hσ', ha', hE', hM'⟩ := (hU m).exists_approx t
    obtain ⟨j, hj1, hj2⟩ :=
      (((hE' _ hδ).eventually (gt_mem_nhds hhalf)).and
        ((hM' _ hδ).eventually (gt_mem_nhds hhalf))).exists
    exact ⟨m, n' j, σ' j, a' j, hσ' j, ha' j, hm, hj1, hj2⟩
  choose m n σ a hσ ha hGm hEk hMk using hstep
  have hinv : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  refine ⟨n, σ, a, hσ, ha, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [hinv.eventually (gt_mem_nhds hε)] with k hk
    have hsub : {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t} ⊆
        (G (m k))ᶜ ∪ {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤
          ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - Hseq (m k) s ω‖ₑ ^ 2
            ∂timeMeasure t} := fun ω hω ↦ by
      refine if hGω : ω ∈ G (m k) then Or.inr ?_ else Or.inl hGω
      have hHeq_ae : (fun s ↦ Hseq (m k) s ω) =ᵐ[timeMeasure t] fun s ↦ H s ω :=
        ((lintegral_eq_zero_iff (((((hU (m k)).isStronglyPredictable.sub hH).mono
          ℱ.predictable_le_prod).comp_measurable
            measurable_prodMk_right).measurable.eNorm.pow_const 2)).mp hGω.right).mono fun _ hs ↦
          sub_eq_zero.mp (eNorm_eq_zero.mp (by
            simpa only [Function.comp_apply, Pi.sub_apply, Function.uncurry_apply_pair,
              Pi.zero_apply, pow_eq_zero_iff (by norm_num : 2 ≠ 0)] using hs))
      have hlint : (∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
            ∂timeMeasure t) =
          ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - Hseq (m k) s ω‖ₑ ^ 2
            ∂timeMeasure t :=
        lintegral_congr_ae (hHeq_ae.mono fun _ hs ↦ by dsimp only at hs ⊢; rw [hs])
      exact hk.le.trans (hlint ▸ hω)
    exact ((measure_mono hsub).trans (measure_union_le _ _)).trans <|
      (add_le_add (hGm k).le (hEk k).le).trans_eq (ENNReal.add_halves _)
  · let N : Set Ω := {ω | ¬ ∀ j, stoppedProcess I (τ j) t ω = U j t ω}
    have hN : P N = 0 := ae_iff.mp ((ae_all_iff.mpr hstop).mono fun ω hω j ↦ hω j t)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [hinv.eventually (gt_mem_nhds hε)] with k hk
    have hsub : {ω | ε ≤ edist (Finance.simpleGains (σ k) (n k) (a k) W t ω) (I t ω)} ⊆
        N ∪ ((G (m k))ᶜ ∪ {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤
          edist (Finance.simpleGains (σ k) (n k) (a k) W t ω) (U (m k) t ω)}) := fun ω hω ↦ by
      classical
      refine if hNω : ω ∈ N then Or.inl hNω else
        if hGω : ω ∈ G (m k) then Or.inr (Or.inr ?_) else Or.inr (Or.inl hGω)
      have hIU : I t ω = U (m k) t ω := by
        have h1 := (not_not.mp hNω) (m k)
        rwa [stoppedProcess_eq_of_le hGω.left.le] at h1
      exact hk.le.trans (hIU ▸ hω)
    calc P _ ≤ P N + (P (G (m k))ᶜ + P _) :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add_right (measure_union_le _ _) _))
      _ ≤ 0 + (((k : ℝ≥0∞) + 1)⁻¹ / 2 + ((k : ℝ≥0∞) + 1)⁻¹ / 2) := by
          rw [hN]; exact add_le_add_right (add_le_add (hGm k).le (hMk k).le) _
      _ = ((k : ℝ≥0∞) + 1)⁻¹ := by rw [zero_add, ENNReal.add_halves]

/-! ### Stopping compatibility for L² Itô integrals -/

namespace IsFilteredPreBrownianReal

private theorem coe_le_dyadicCeilTime_iff_gt_dyadic (m k : ℕ) {t : ℝ≥0}
    (ht : t ∈ Ioc ((k : ℝ≥0) / 2 ^ m) (((k + 1 : ℕ) : ℝ≥0) / 2 ^ m)) (u : WithTop ℝ≥0) :
    (t : WithTop ℝ≥0) ≤ dyadicCeilTime m u ↔
      (((k : ℝ≥0) / 2 ^ m : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime m u := by
  cases u with
  | top => rw [dyadicCeilTime_top]; exact iff_of_true le_top (WithTop.coe_lt_top _)
  | coe r =>
    simp only [dyadicCeilTime_coe, WithTop.coe_le_coe, WithTop.coe_lt_coe]
    have hpos : (0 : ℝ≥0) < 2 ^ m := by positivity
    rw [div_lt_div_iff_of_pos_right hpos, Nat.cast_lt, le_div_iff₀ hpos]
    exact ⟨fun hle ↦ Nat.cast_lt.mp (((div_lt_iff₀ hpos).mp ht.left).trans_le hle),
      fun hlt ↦ ((le_div_iff₀ hpos).mp ht.right).trans (Nat.cast_le.mpr hlt)⟩

private theorem ae_eq_stoppedProcess_dyadicCeilTime_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (m : ℕ) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).toLp _) =ᵐ[P]
      stoppedProcess I (fun ω ↦ dyadicCeilTime m (τ ω)) T := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime m (τ ω)
  have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime m
  let d : ℕ → ℝ≥0 := fun k ↦ (k : ℝ≥0) / 2 ^ m
  let N : ℕ := ⌈T * 2 ^ m⌉₊
  let t : ℕ → ℝ≥0 := fun k ↦ min (d k) T
  let A : ℕ → Set Ω := fun k ↦ {ω | ((d k : ℝ≥0) : WithTop ℝ≥0) < σ ω}
  have h2pos : (0 : ℝ≥0) < 2 ^ m := by positivity
  have hdk_lt (k : ℕ) (hk : k < N) : d k < T := (div_lt_iff₀ h2pos).mpr (Nat.lt_ceil.mp hk)
  have ht_eq (k : ℕ) (hk : k < N) : t k = d k := min_eq_left (hdk_lt k hk).le
  have ht_mono : Monotone t := fun _ _ h ↦
    min_le_min_right T (div_le_div_of_nonneg_right (Nat.cast_le.mpr h) h2pos.le)
  have hA_meas (k : ℕ) (hk : k < N) : MeasurableSet[ℱ (t k)] (A k) := by
    rw [ht_eq k hk]
    simpa only [compl_ofPred, not_le] using (hσ (d k)).compl
  let fH := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  let piece (k : ℕ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    if hk : k < N then
      ((Lp.memLp fH).indicator (measurableSet_predictable_Ioc_prod (t k) (t (k + 1))
        (hA_meas k hk)).nullMeasurableSet).toLp
          ((Ioc (t k) (t (k + 1)) ×ˢ A k).indicator fH)
    else 0
  have hsum_Lp :
      ((hH.ite_le hσ).memLp_predictableMeasure T).toLp _ = ∑ k ∈ Finset.range N, piece k := by
    apply Lp.ext
    have hterms : ∀ k ∈ Finset.range N, (piece k : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
        (Ioc (t k) (t (k + 1)) ×ˢ A k).indicator (Function.uncurry H) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      simp only [piece, dite_eq_left hk']
      filter_upwards [((Lp.memLp fH).indicator (measurableSet_predictable_Ioc_prod (t k) (t (k + 1))
        (hA_meas k hk')).nullMeasurableSet).coeFn_toLp,
        (hH.memLp_predictableMeasure T).coeFn_toLp] with p hp hHp
      dsimp only [fH] at hp ⊢; simp only [hp, indicator_apply, hHp]
    have hIoc := ℱ.ae_mem_Ioc_prod_predictableMeasure P T
    filter_upwards [((hH.ite_le hσ).memLp_predictableMeasure T).coeFn_toLp, hIoc,
      Lp.coeFn_finsetSum (s := Finset.range N) piece, eventuallyEq_sum hterms]
      with ⟨s, ω⟩ hL hsT hsum htms
    rw [hL, hsum, htms]
    simp only [Finset.sum_apply, Function.uncurry_apply_pair]
    let k₀ : ℕ := ⌈s * 2 ^ m⌉₊ - 1
    have hceil_pos : 0 < ⌈s * 2 ^ m⌉₊ := Nat.ceil_pos.mpr (mul_pos hsT.left.left h2pos)
    have hk₀ : k₀ ∈ Finset.range N := Finset.mem_range.mpr <| by
      have : ⌈s * 2 ^ m⌉₊ ≤ N := Nat.ceil_mono (mul_le_mul_of_nonneg_right hsT.left.right h2pos.le)
      omega
    have hsk₀ : s ∈ Ioc (d k₀) (d (k₀ + 1)) :=
      ⟨(div_lt_iff₀ h2pos).mpr (Nat.lt_ceil.mp (Nat.sub_lt hceil_pos zero_lt_one)),
        (le_div_iff₀ h2pos).mpr (by
          simpa only [k₀, Nat.sub_add_cancel hceil_pos] using Nat.le_ceil _)⟩
    rw [Finset.sum_eq_single k₀]
    · have hst : s ∈ Ioc (t k₀) (t (k₀ + 1)) :=
        ⟨by rw [ht_eq k₀ (Finset.mem_range.mp hk₀)]; exact hsk₀.left,
          le_min hsk₀.right hsT.left.right⟩
      have hiff := coe_le_dyadicCeilTime_iff_gt_dyadic m k₀ hsk₀ (τ ω)
      by_cases hc : (s : WithTop ℝ≥0) ≤ σ ω
      · rw [ite_eq_left hc, indicator_of_mem (mem_prod.mpr ⟨hst, hiff.mp hc⟩)]; rfl
      · rw [ite_eq_right hc, indicator_of_notMem (fun h ↦ hc (hiff.mpr (mem_prod.mp h).right))]
    · intro k hk hne
      refine indicator_of_notMem (f := Function.uncurry H) fun h ↦ ?_
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact ((mem_prod.mp h).left.right.trans <| (min_le_left _ _).trans <|
          div_le_div_of_nonneg_right (Nat.cast_le.mpr hlt) h2pos.le).not_gt hsk₀.left
      · exact (hsk₀.right.trans <| (ht_eq k (Finset.mem_range.mp hk)).symm ▸
          div_le_div_of_nonneg_right (Nat.cast_le.mpr hlt) h2pos.le).not_gt
            (mem_prod.mp h).left.left
    · exact fun hnot ↦ (hnot hk₀).elim
  rw [hsum_Lp, map_sum]
  have hresH {u : ℝ≥0} (hu : u ≤ T) :
      ℱ.predictableMeasureRestrictLp P ℝ hu fH =
        (hH.memLp_predictableMeasure u).toLp (Function.uncurry H) :=
    Lp.ext <| (ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := ℝ) hu fH).trans
      (((ℱ.predictableMeasure_mono P hu).absolutelyContinuous.ae_eq
        ((hH.memLp_predictableMeasure T).coeFn_toLp)).trans
        (hH.memLp_predictableMeasure u).coeFn_toLp.symm)
  have heach : ∀ k ∈ Finset.range N, (hW.l2Integral T (piece k) : Ω → ℝ) =ᵐ[P]
      (A k).indicator (fun ω ↦ I (t (k + 1)) ω - I (t k) ω) := fun k hk ↦ by
    have hk' := Finset.mem_range.mp hk
    simp only [piece, dite_eq_left hk']
    have hloc := hW.coeFn_l2Integral_indicator_Ioc_prod T (t k) (t (k + 1)) (hA_meas k hk') fH
    have hbT : t (k + 1) ≤ T := min_le_right _ _
    have haT : t k ≤ T := (ht_mono k.le_succ).trans hbT
    have hstrip :
        ((Lp.memLp fH).indicator (measurableSet_predictable_Ioc_prod (t k) (t (k + 1))
          (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
            ((Ioc (t k) (t (k + 1)) ×ˢ univ).indicator fH) =
          ℱ.predictableMeasureExtendLp P ℝ hbT (ℱ.predictableMeasureRestrictLp P ℝ hbT fH) -
            ℱ.predictableMeasureExtendLp P ℝ haT (ℱ.predictableMeasureRestrictLp P ℝ haT fH) := by
      apply Lp.ext
      filter_upwards [((Lp.memLp fH).indicator (measurableSet_predictable_Ioc_prod (t k) (t (k + 1))
          (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).coeFn_toLp,
        Lp.coeFn_sub
          (ℱ.predictableMeasureExtendLp P ℝ hbT (ℱ.predictableMeasureRestrictLp P ℝ hbT fH))
          (ℱ.predictableMeasureExtendLp P ℝ haT (ℱ.predictableMeasureRestrictLp P ℝ haT fH)),
        ℱ.coeFn_predictableMeasureExtendLp_predictableMeasureRestrictLp P (𝕜 := ℝ) hbT fH,
        ℱ.coeFn_predictableMeasureExtendLp_predictableMeasureRestrictLp P (𝕜 := ℝ) haT fH,
        ℱ.ae_mem_Ioc_prod_predictableMeasure P T] with p hp hsub hpb hpa hpT
      rw [hp, hsub, Pi.sub_apply, hpb, hpa]
      rcases le_or_gt p.fst (t k) with h2 | h2
      · have h1 : p.fst ≤ t (k + 1) := h2.trans (ht_mono k.le_succ)
        have hn : p ∉ Ioc (t k) (t (k + 1)) ×ˢ (univ : Set Ω) :=
          fun h ↦ h2.not_gt (mem_prod.mp h).left.left
        have hm1 : p ∈ Ioc 0 (t (k + 1)) ×ˢ (univ : Set Ω) :=
          mem_prod.mpr ⟨⟨hpT.left.left, h1⟩, mem_univ _⟩
        have hm0 : p ∈ Ioc 0 (t k) ×ˢ (univ : Set Ω) :=
          mem_prod.mpr ⟨⟨hpT.left.left, h2⟩, mem_univ _⟩
        rw [indicator_of_notMem hn, indicator_of_mem hm1, indicator_of_mem hm0, sub_self]
      · by_cases h1 : p.fst ≤ t (k + 1)
        · have hm : p ∈ Ioc (t k) (t (k + 1)) ×ˢ (univ : Set Ω) :=
            mem_prod.mpr ⟨⟨h2, h1⟩, mem_univ _⟩
          have hm1 : p ∈ Ioc 0 (t (k + 1)) ×ˢ (univ : Set Ω) :=
            mem_prod.mpr ⟨⟨hpT.left.left, h1⟩, mem_univ _⟩
          have hn0 : p ∉ Ioc 0 (t k) ×ˢ (univ : Set Ω) :=
            fun h ↦ h2.not_ge (mem_prod.mp h).left.right
          rw [indicator_of_mem hm, indicator_of_mem hm1, indicator_of_notMem hn0, sub_zero]
        · have hn : p ∉ Ioc (t k) (t (k + 1)) ×ˢ (univ : Set Ω) :=
            fun h ↦ h1 (mem_prod.mp h).left.right
          have hn1 : p ∉ Ioc 0 (t (k + 1)) ×ˢ (univ : Set Ω) :=
            fun h ↦ h1 (mem_prod.mp h).left.right
          have hn0 : p ∉ Ioc 0 (t k) ×ˢ (univ : Set Ω) :=
            fun h ↦ h1 ((mem_prod.mp h).left.right.trans (ht_mono k.le_succ))
          rw [indicator_of_notMem hn, indicator_of_notMem hn1, indicator_of_notMem hn0, sub_self]
    rw [hstrip, map_sub, hW.l2Integral_predictableMeasureExtendLp hbT,
      hW.l2Integral_predictableMeasureExtendLp haT, hresH hbT, hresH haT] at hloc
    let g1 := hW.l2Integral (t (k + 1)) ((hH.memLp_predictableMeasure _).toLp (Function.uncurry H))
    let g0 := hW.l2Integral (t k) ((hH.memLp_predictableMeasure _).toLp (Function.uncurry H))
    filter_upwards [hloc, Lp.coeFn_sub g1 g0,
      hW.ae_eq_l2Integral_of_isItoIntegral hH hI (t (k + 1)),
      hW.ae_eq_l2Integral_of_isItoIntegral hH hI (t k)] with ω h1 h2 hI1 hI0
    dsimp only [g1, g0] at h1 h2
    rw [h1]
    by_cases hω : ω ∈ A k
    · simp only [indicator_of_mem hω, h2, Pi.sub_apply, hI1, hI0]
    · simp only [indicator_of_notMem hω]
  filter_upwards [Lp.coeFn_finsetSum (s := Finset.range N) (fun k ↦ hW.l2Integral T (piece k)),
    eventuallyEq_sum heach, hI.eval_zero_ae_eq_zero] with ω hω hsumω hI0
  rw [hω, hsumω, Finset.sum_apply]
  have ht0 : t 0 = 0 := by simp [t, d]
  have htN : t N = T := min_eq_right ((le_div_iff₀ h2pos).mpr (Nat.le_ceil _))
  rcases le_or_gt (T : WithTop ℝ≥0) (σ ω) with hTσ | hTσ
  · have hsum : (∑ k ∈ Finset.range N, (A k).indicator (fun ω ↦ I (t (k + 1)) ω - I (t k) ω) ω) =
        ∑ k ∈ Finset.range N, (I (t (k + 1)) ω - I (t k) ω) :=
      Finset.sum_congr rfl fun k hk ↦ indicator_of_mem
        ((WithTop.coe_lt_coe.mpr (hdk_lt k (Finset.mem_range.mp hk))).trans_le hTσ) _
    rw [hsum, Finset.sum_range_sub (fun k ↦ I (t k) ω) N, htN, ht0, hI0, Pi.zero_apply, sub_zero,
      stoppedProcess_eq_of_le hTσ]
  · cases hτω : τ ω with
    | top => simp only [σ, hτω, dyadicCeilTime_top] at hTσ; exact (not_top_lt hTσ).elim
    | coe v =>
      let q : ℕ := ⌈v * 2 ^ m⌉₊
      have hdyad : σ ω = ((d q : ℝ≥0) : WithTop ℝ≥0) := by
        dsimp only [σ, d, q]; rw [hτω, dyadicCeilTime_coe]
      have hqN : q < N :=
        Nat.lt_ceil.mpr ((div_lt_iff₀ h2pos).mp (WithTop.coe_lt_coe.mp (hdyad ▸ hTσ)))
      have hsum : (∑ k ∈ Finset.range N, (A k).indicator (fun ω ↦ I (t (k + 1)) ω - I (t k) ω) ω) =
          ∑ k ∈ Finset.range q, (I (t (k + 1)) ω - I (t k) ω) := by
        rw [← Finset.sum_subset (Finset.range_mono hqN.le)]
        · exact Finset.sum_congr rfl fun k hk ↦ indicator_of_mem (by
            rw [mem_ofPred_eq, hdyad, WithTop.coe_lt_coe]
            exact div_lt_div_of_pos_right (Nat.cast_lt.mpr (Finset.mem_range.mp hk)) h2pos) _
        · exact fun k _ hk ↦ indicator_of_notMem (fun h ↦ hk <| Finset.mem_range.mpr <| by
            rwa [mem_ofPred_eq, hdyad, WithTop.coe_lt_coe, div_lt_div_iff_of_pos_right h2pos,
              Nat.cast_lt] at h) _
      rw [hsum, Finset.sum_range_sub (fun k ↦ I (t k) ω) q, ht_eq q hqN, ht0, hI0, Pi.zero_apply,
        sub_zero, stoppedProcess, min_eq_right hTσ.le, hdyad]; rfl

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
  let Lm (m : ℕ) : Ω → ℝ :=
    hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T).toLp _)
  let L : Ω → ℝ := hW.l2Integral T (((hH.ite_le hτ).memLp_predictableMeasure T).toLp _)
  have hL_lim : Tendsto (fun m ↦ eLpNorm (Lm m - L) 2 P) atTop (𝓝 0) := by
    have heq (m : ℕ) : eLpNorm (Lm m - L) 2 P =
        eLpNorm (fun p : ℝ≥0 × Ω ↦
          (if (p.fst : WithTop ℝ≥0) ≤ dyadicCeilTime m (τ p.snd) then H p.fst p.snd else 0) -
            (if (p.fst : WithTop ℝ≥0) ≤ τ p.snd then H p.fst p.snd else 0))
          2 ((timeMeasure T).prod P) := by
      rw [← Lp.edist_def, (hW.l2Integral T).isometry.edist_eq, Lp.edist_def,
        eLpNorm_congr_ae (MemLp.coeFn_toLp _ |>.sub (MemLp.coeFn_toLp _)),
        ℱ.predictableMeasure_def]
      exact eLpNorm_trim ℱ.predictable_le_prod
        ((hH.ite_le (hτ.dyadicCeilTime m)).isStronglyPredictable.sub
          (hH.ite_le hτ).isStronglyPredictable)
    simp_rw [heq]
    have hHmem : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P) :=
      hH.memLp_timeMeasure T
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (Eventually.of_forall fun m ↦ ((hH.ite_le (hτ.dyadicCeilTime m)).isStronglyPredictable.mono
        ℱ.predictable_le_prod).aestronglyMeasurable) hHmem
      (Eventually.of_forall fun m ↦ Eventually.of_forall fun p ↦ by
        simp only [ENNReal.coe_one, one_mul, Function.uncurry_def]; split_ifs <;> simp)
      (Eventually.of_forall fun p ↦ ?_)
    by_cases hp : (p.fst : WithTop ℝ≥0) ≤ τ p.snd
    · exact tendsto_const_nhds.congr fun m ↦ by
        rw [ite_eq_left hp, ite_eq_left (hp.trans (le_dyadicCeilTime m (τ p.snd)))]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_dyadicCeilTime (τ p.snd)).eventually (gt_mem_nhds (not_le.mp hp))]
        with m hm
      rw [ite_eq_right hp, ite_eq_right (not_le.mpr hm)]
  have hR_lim := (hI.martingale hW hH hI_adapt)
    |>.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime
      (hI.ae_continuous.mono fun _ hω ↦ hω.isRightContinuous) hτ T one_le_two (by norm_num)
      (hI.memLp hW hH T)
  have hzero : eLpNorm (stoppedProcess I τ T - L) 2 P = 0 :=
    tendsto_nhds_unique tendsto_const_nhds <|
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hR_lim.add hL_lim) (fun _ ↦ zero_le) fun m ↦ by
        rw [eLpNorm_congr_ae ((hW.ae_eq_stoppedProcess_dyadicCeilTime_of_brownianIntegrable hH hI
          hτ m T).mono fun ω hω ↦ show (stoppedProcess I τ T - L) ω =
            ((stoppedProcess I τ T - stoppedProcess I (fun ω ↦ dyadicCeilTime m (τ ω)) T) +
              (Lm m - L)) ω by dsimp only [Lm, Pi.sub_apply, Pi.add_apply] at hω ⊢; rw [hω]; ring)]
        refine (eLpNorm_add_le one_le_two).trans ?_
        gcongr; rw [← eLpNorm_neg, neg_sub]
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
  choose U hUI hUpred hUmart using fun n ↦
    (hHseq n).exists_isItoIntegral hW hcont
  have hcompat (m n : ℕ) (hmn : m ≤ n) : stoppedProcess (U n) (σ m) ≡ᵐ[P] U m := by
    have hσ_le (ω : Ω) : σ m ω ≤ σ n ω :=
      nnvolume.monotone_energyLocalizer H ω (add_le_add_left (Nat.cast_le.mpr hmn) 1)
    have hHeq : (fun (t : ℝ≥0) ω ↦
        if (t : WithTop ℝ≥0) ≤ σ m ω then Hseq n t ω else 0) = Hseq m := by
      ext t ω; dsimp only [Hseq]
      by_cases ht : (t : WithTop ℝ≥0) ≤ σ m ω
      · simp only [ite_eq_left ht, ite_eq_left (ht.trans (hσ_le ω))]
      · simp only [ite_eq_right ht]
    exact isItoIntegral_unique hW (hHeq ▸
      hW.isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable (hHseq n) (hUI n)
        (hUpred n).isStronglyProgressive.stronglyAdapted (hloc.isStoppingTime m)) (hUI m)
  obtain ⟨V, hVprog, hVcont, hVstop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hloc.tendsto_top (fun n ↦ (hUpred n).isStronglyProgressive) (fun n ↦ (hUI n).ae_continuous)
    hcompat
  obtain ⟨I, hIpred, hIcont, hIV⟩ :=
    hVprog.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_continuous hVcont
  have hIstop (n : ℕ) : stoppedProcess I (σ n) ≡ᵐ[P] U n := by
    filter_upwards [hIV, hVstop n] with ω hω hVω t
    simpa only [stoppedProcess, hω] using hVω t
  exact ⟨I, U, IsItoIntegral.of_stoppedProcess hH.isStronglyPredictable hIcont
    (fun n ↦ (hloc.isStoppingTime n).measurable') hloc.tendsto_top hUI hIstop
    hH.ae_eventually_ite_le_energyLocalizer_eqOn, hIpred, hUI, hUpred, hUmart, hIstop⟩

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
  obtain ⟨I, U, hII, hIpred, -, -, hUmart, hIstop⟩ := hW.exists_energyLocalized_integrals hcont hH
  refine ⟨I, hII, hIpred, hIpred.isStronglyProgressive.locally_martingale_of_ae_stopped_eq
    hH.isLocalizingSequence_energyLocalizer hUmart fun n t ↦ ?_⟩
  filter_upwards [hIstop n] with ω hω
  rw [stoppedProcess_indicator_pos_apply,
    ite_eq_left (show (⊥ : WithTop ℝ≥0) < _ from nnvolume.energyLocalizer_pos H (by positivity) ω)]
  exact (hω t).symm

/-- Every strongly progressive Itô integral against an almost surely continuous filtered
pre-Brownian motion is a native local martingale on the raw filtration. -/
theorem locally_martingale_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I) (hI_prog : IsStronglyProgressive ℱ I) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  obtain ⟨J, hJ, -, hJloc⟩ := hW.exists_isItoIntegral hcont hI.locallyBrownianIntegrable
  exact hI_prog.locally_martingale_of_indist hJloc (isItoIntegral_unique hW hJ hI)

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
  obtain ⟨I₀, U, hI₀, -, hUI, hUpred, -, hI₀stop⟩ := hW.exists_energyLocalized_integrals hcont hH
  have hII₀ : I ≡ᵐ[P] I₀ := isItoIntegral_unique hW hI hI₀
  have hloc := hH.isLocalizingSequence_energyLocalizer
  refine IsItoIntegral.of_stoppedProcess (hH.ite_le hτ).isStronglyPredictable
    (hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess)
    (fun n ↦ (hloc.isStoppingTime n).measurable') hloc.tendsto_top
    (fun n ↦ hW.isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable
      (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
      (hUI n) (hUpred n).isStronglyProgressive.stronglyAdapted hτ)
    (fun n ↦ ?_) ?_
  · filter_upwards [hII₀, hI₀stop n] with ω hω h0ω t
    rw [stoppedProcess_stoppedProcess, inf_comm, ← stoppedProcess_stoppedProcess]
    simpa only [stoppedProcess, hω] using h0ω _
  · filter_upwards [hH.ae_eventually_ite_le_energyLocalizer_eqOn] with ω hω T
    filter_upwards [hω T] with n hn t ht
    dsimp only; exact ite_congr rfl (fun _ ↦ hn ht) (fun _ ↦ rfl)

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
  obtain ⟨I₀, U, hI₀, -, hUI, hUpred, -, hI₀stop⟩ := hW.exists_energyLocalized_integrals hcont hH
  have hII₀ : I ≡ᵐ[P] I₀ := isItoIntegral_unique hW hI hI₀
  have hHseq (n : ℕ) : BrownianIntegrable ℱ P (Hseq n) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)
  have hX_prog : IsStronglyProgressive ℱ (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    fun t ↦ ((hI_prog t).pow 2).sub
      (hH.isStronglyPredictable.isStronglyPredictable_integral_sq_timeMeasure
        |>.isStronglyProgressive t)
  refine hX_prog.locally_martingale_of_ae_stopped_eq hH.isLocalizingSequence_energyLocalizer
    (fun n ↦ hW.martingale_sq_sub_of_isItoIntegral (hHseq n) (hUI n)
      (hUpred n).isStronglyProgressive.stronglyAdapted) fun n t ↦ ?_
  filter_upwards [hII₀, hI₀stop n, hH.ae_accumulatedEnergy_lt_top] with ω hω h0ω hfin
  rw [stoppedProcess_indicator_pos_apply,
    ite_eq_left (show (⊥ : WithTop ℝ≥0) < _ from nnvolume.energyLocalizer_pos H (by positivity) ω)]
  let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (σ n ω)).untopA
  have hI_eq : U n t ω = I u ω := by simpa only [stoppedProcess, hω] using (h0ω t).symm
  have hE_eq : (∫ s, Hseq n s ω ^ 2 ∂timeMeasure t) = ∫ s, H s ω ^ 2 ∂timeMeasure u := by
    rw [(hHseq n).isStronglyPredictable.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy t ω,
      hH.isStronglyPredictable.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy u ω,
      nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc,
      nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc]
    congr 1
    have h1 : ∫⁻ s in Ioc 0 t, ‖Hseq n s ω‖ₑ ^ 2 ∂nnvolume =
        ∫⁻ s in Ioc 0 u, ‖nnvolume.finiteEnergyCutoff H s ω‖ₑ ^ 2 ∂nnvolume := by
      simpa only [Hseq, apply_ite, eNorm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
        stoppedProcess] using setLIntegral_ite_le_eq_stoppedProcess
          (fun s ω' ↦ ‖nnvolume.finiteEnergyCutoff H s ω'‖ₑ ^ 2) (σ n) nnvolume 0 t ω
    rw [h1]
    exact setLIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by
      have hfe := nnvolume.finiteEnergyCutoff_eqOn (hfin u) hs.right; dsimp only at hfe; rw [hfe]
  rw [hI_eq, hE_eq]

end IsFilteredPreBrownianReal

end TauCeti.Probability
