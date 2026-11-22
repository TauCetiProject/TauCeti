/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
public import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Integral.Indicator
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.BrownianMotion.Integral.Locality
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.AccumulatedEnergy
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.TimeAverage

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
* `TauCeti.Probability.IsItoIntegral.ite_Ioc_add`: adjacent stochastic-interval concatenation for
  Itô integrals;
* `TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_ite_le_stoppedProcess`,
  `isItoIntegral_ite_Ioc_stoppedProcess_sub`, and `indist_ite_Ioc_add_stoppedProcess_sub` (with
  the `L²` base case `isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable`): stopping an Itô
  integral at any stopping time `τ` or stochastic interval `(σ, τ]` produces an Itô integral of
  `1_{[0, τ]} H` or `1_{(σ, τ]} H`, obeying adjacent-interval concatenation;
* `TauCeti.Probability.IsFilteredPreBrownianReal.exists_isItoIntegral` and
  `exists_isItoIntegral_of_isStronglyProgressive`: existence of a predictable, almost surely
  continuous Itô integral (and predictable representative for strongly progressive inputs) that
  is a native local martingale on the raw filtration;
* `TauCeti.Probability.IsFilteredPreBrownianReal.locally_martingale_of_isItoIntegral` and
  `locally_martingale_sq_sub_of_isItoIntegral`: every strongly progressive Itô integral `I` is a
  native local martingale, and `I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` is a native local
  martingale.

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

private theorem tendsto_measure_compl_goodEvent [IsFiniteMeasure P]
    {τ : ℕ → Ω → WithTop ℝ≥0} {Hseq : ℕ → ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℝ}
    (hτ_meas : ∀ n, Measurable (τ n))
    (hHseq_meas : ∀ n, Measurable (fun p : ℝ≥0 × Ω ↦ Hseq n p.1 p.2 - H p.1 p.2))
    (hτ : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hHeq : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, EqOn (Hseq n · ω) (H · ω) (Iic T))
    (t : ℝ≥0) :
    let G (m : ℕ) : Set Ω := {ω | (t : WithTop ℝ≥0) < τ m ω} ∩
      {ω | ∫⁻ s, ‖Hseq m s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t = 0}
    (∀ m, MeasurableSet (G m)) ∧ Tendsto (fun m ↦ P (G m)ᶜ) atTop (𝓝 0) := by
  intro G
  have hE_meas (m : ℕ) : Measurable (fun ω ↦ ∫⁻ s, ‖Hseq m s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t) :=
    ((hHseq_meas m).eNorm.pow_const 2).lintegral_prod_left'
  have hG_meas (m : ℕ) : MeasurableSet (G m) :=
    (measurableSet_lt measurable_const (hτ_meas m)).inter (hE_meas m (measurableSet_singleton 0))
  refine ⟨hG_meas, ?_⟩
  simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    MeasurableSet.empty (fun m ↦ (hG_meas m).compl) <| by
      filter_upwards [hτ, hHeq] with ω hτω hHω
      obtain ⟨m, hm⟩ := eventually_atTop.mp
        ((hτω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).and (hHω t))
      refine eventually_atTop.mpr ⟨m, fun j hj ↦ ?_⟩
      simp only [mem_compl_iff, mem_empty_iff_false, iff_false, not_not, G, mem_inter_iff,
        Set.mem_ofPred_eq]
      exact ⟨(hm j hj).1, (TauCeti.ae_eq_iff_lintegral_enorm_sub_sq_eq_zero
        (((hHseq_meas j).comp measurable_prodMk_right).eNorm.pow_const 2).aemeasurable).mp
        ((ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ (hm j hj).2 hs.2)⟩

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
  have hdiff_meas (m : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ Hseq m p.1 p.2 - H p.1 p.2) :=
    (((hU m).isStronglyPredictable.sub hH).mono ℱ.predictable_le_prod).measurable
  let G (m : ℕ) : Set Ω := {ω | (t : WithTop ℝ≥0) < τ m ω} ∩
    {ω | ∫⁻ s, ‖Hseq m s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t = 0}
  obtain ⟨-, hG_lim⟩ := tendsto_measure_compl_goodEvent hτ_meas hdiff_meas hτ hHeq t
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
  · refine TauCeti.tendsto_measure_of_subset_union hinv measure_empty
      (Eventually.of_forall fun k ↦ (hGm k).le) (Eventually.of_forall fun k ↦ (hEk k).le) ?_
    filter_upwards [hinv.eventually (gt_mem_nhds hε)] with k hk ω hω
    refine if hGω : ω ∈ G (m k) then Or.inr (Or.inr ?_) else Or.inr (Or.inl hGω)
    have hHeq_ae : (fun s ↦ Hseq (m k) s ω) =ᵐ[timeMeasure t] fun s ↦ H s ω :=
      (TauCeti.ae_eq_iff_lintegral_enorm_sub_sq_eq_zero
        (((hdiff_meas (m k)).comp measurable_prodMk_right).eNorm.pow_const 2).aemeasurable).mpr
        hGω.2
    have hlint : (∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (σ k) (n k) (a k) s ω - Hseq (m k) s ω‖ₑ ^ 2
          ∂timeMeasure t :=
      lintegral_congr_ae (hHeq_ae.mono fun _ hs ↦ by dsimp only at hs ⊢; rw [hs])
    exact hk.le.trans (hlint ▸ hω)
  · let N : Set Ω := {ω | ¬ ∀ j, stoppedProcess I (τ j) t ω = U j t ω}
    have hN : P N = 0 := ae_iff.mp ((ae_all_iff.mpr hstop).mono fun ω hω j ↦ hω j t)
    refine TauCeti.tendsto_measure_of_subset_union hinv hN
      (Eventually.of_forall fun k ↦ (hGm k).le) (Eventually.of_forall fun k ↦ (hMk k).le) ?_
    filter_upwards [hinv.eventually (gt_mem_nhds hε)] with k hk ω hω
    by_cases hNω : ω ∈ N
    · exact Or.inl hNω
    · by_cases hGω : ω ∈ G (m k)
      · refine Or.inr (Or.inr ?_)
        have hIU : I t ω = U (m k) t ω := by
          have h1 := (not_not.mp hNω) (m k)
          rwa [stoppedProcess_eq_of_le hGω.1.le] at h1
        exact hk.le.trans (hIU ▸ hω)
      · exact Or.inr (Or.inl hGω)

/-- **Adjacent stochastic-interval concatenation for Itô integrals.** For ordered random times
`σ ≤ τ ≤ ρ`, summing Itô integrals of the restrictions `1_{(σ, τ]} H` and `1_{(τ, ρ]} H` yields
an Itô integral of `1_{(σ, ρ]} H`. Neither stopping-time properties nor path continuity of `W` is
needed. -/
theorem IsItoIntegral.ite_Ioc_add {σ τ ρ : Ω → WithTop ℝ≥0} (hστ : σ ≤ τ) (hτρ : τ ≤ ρ)
    {J₁ J₂ : ℝ≥0 → Ω → ℝ}
    (hJ₁ : IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J₁)
    (hJ₂ : IsItoIntegral ℱ P W
      (fun t ω ↦ if τ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0) J₂) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0)
      (fun t ω ↦ J₁ t ω + J₂ t ω) := by
  have hint_eq : (fun (t : ℝ≥0) ω ↦
      if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0) =
      fun (t : ℝ≥0) ω ↦
        (if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) +
          (if τ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0) := by
    ext t ω
    rcases le_or_gt (t : WithTop ℝ≥0) (σ ω) with htσ | hσt
    · have htτ : (t : WithTop ℝ≥0) ≤ τ ω := htσ.trans (hστ ω)
      rw [ite_eq_right (not_and_of_not_left _ (not_lt.mpr htσ)),
        ite_eq_right (not_and_of_not_left _ (not_lt.mpr htσ)),
        ite_eq_right (not_and_of_not_left _ (not_lt.mpr htτ)), add_zero]
    · rcases le_or_gt (t : WithTop ℝ≥0) (τ ω) with htτ | hτt
      · have htρ : (t : WithTop ℝ≥0) ≤ ρ ω := htτ.trans (hτρ ω)
        rw [ite_eq_left ⟨hσt, htρ⟩, ite_eq_left ⟨hσt, htτ⟩,
          ite_eq_right (not_and_of_not_left _ (not_lt.mpr htτ)), add_zero]
      · have hστ_lt : σ ω < (t : WithTop ℝ≥0) := (hστ ω).trans_lt hτt
        by_cases htρ : (t : WithTop ℝ≥0) ≤ ρ ω
        · rw [ite_eq_left ⟨hστ_lt, htρ⟩, ite_eq_right (not_and_of_not_right _ (not_le.mpr hτt)),
            ite_eq_left ⟨hτt, htρ⟩, zero_add]
        · rw [ite_eq_right (not_and_of_not_right _ htρ),
            ite_eq_right (not_and_of_not_right _ (not_le.mpr hτt)),
            ite_eq_right (not_and_of_not_right _ htρ), add_zero]
  rw [hint_eq]
  exact hJ₁.add hJ₂

/-! ### Stopping compatibility for L² Itô integrals -/

namespace IsFilteredPreBrownianReal

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
  let N : ℕ := ⌈T * 2 ^ m⌉₊
  let t : ℕ → ℝ≥0 := fun k ↦ min ((k : ℝ≥0) / 2 ^ m) T
  let A : ℕ → Set Ω := fun k ↦ {ω | (((k : ℝ≥0) / 2 ^ m : ℝ≥0) : WithTop ℝ≥0) < σ ω}
  have ht_mono : Monotone t := fun _ _ h ↦
    min_le_min_right T (div_le_div_of_nonneg_right (Nat.cast_le.mpr h) (by positivity))
  let fH := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  let piece (k : ℕ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    if hk : k < N then
      ((Lp.memLp fH).indicator (measurableSet_predictable_Ioc_prod (t k) (t (k + 1))
        (hτ.measurableSet_gt_dyadicCeilTime m hk)).nullMeasurableSet).toLp
          ((Ioc (t k) (t (k + 1)) ×ˢ A k).indicator fH)
    else 0
  rw [hH.toLp_ite_le_dyadicCeilTime_eq_sum hτ m T, map_sum]
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
    have hloc := hW.coeFn_l2Integral_indicator_Ioc_prod T (t k) (t (k + 1))
      (hτ.measurableSet_gt_dyadicCeilTime m hk') fH
    have hbT : t (k + 1) ≤ T := min_le_right _ _
    rw [ℱ.indicator_Ioc_prod_eq_predictableMeasureExtendLp_sub P (𝕜 := ℝ) fH
        (ht_mono k.le_succ) hbT,
      map_sub, hW.l2Integral_predictableMeasureExtendLp hbT,
      hW.l2Integral_predictableMeasureExtendLp ((ht_mono k.le_succ).trans hbT),
      hresH hbT, hresH ((ht_mono k.le_succ).trans hbT)] at hloc
    let g1 := hW.l2Integral (t (k + 1)) ((hH.memLp_predictableMeasure _).toLp (Function.uncurry H))
    let g0 := hW.l2Integral (t k) ((hH.memLp_predictableMeasure _).toLp (Function.uncurry H))
    filter_upwards [hloc, Lp.coeFn_sub g1 g0,
      hW.ae_eq_l2Integral_of_isItoIntegral hH hI (t (k + 1)),
      hW.ae_eq_l2Integral_of_isItoIntegral hH hI (t k)] with ω h1 h2 hI1 hI0
    dsimp only [g1, g0] at h1 h2
    rw [h1]
    by_cases hω : ω ∈ A k
    · dsimp only [A, σ] at hω ⊢
      rw [indicator_of_mem hω, indicator_of_mem hω, h2, Pi.sub_apply, hI1, hI0]
    · dsimp only [A, σ] at hω ⊢
      rw [indicator_of_notMem hω, indicator_of_notMem hω]
  filter_upwards [Lp.coeFn_finsetSum (s := Finset.range N) (fun k ↦ hW.l2Integral T (piece k)),
    eventuallyEq_sum heach, hI.eval_zero_ae_eq_zero] with ω hω hsumω hI0
  rw [hω, hsumω, Finset.sum_apply]
  exact TauCeti.sum_indicator_stopped_sub_eq_stoppedProcess I τ m T ω hI0

/-- **Stopping compatibility for L² Itô integrals.** For a Brownian-integrable integrand `H`, an
Itô integral `I`, and any stopping time `τ`, the stopped process `stoppedProcess I τ` is an Itô
integral of the cutoff integrand `1_{[0, τ]} H`. Neither adaptedness of `I` nor path continuity of
`W` is required. -/
theorem isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
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
          2 ((timeMeasure T).prod P) :=
      hW.eLpNorm_l2Integral_sub T
        (hH.ite_le (hτ.dyadicCeilTime m)).isStronglyPredictable
        (hH.ite_le hτ).isStronglyPredictable
        ((hH.ite_le (hτ.dyadicCeilTime m)).memLp_predictableMeasure T)
        ((hH.ite_le hτ).memLp_predictableMeasure T)
    simp_rw [heq]
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (Eventually.of_forall fun m ↦ ((hH.ite_le (hτ.dyadicCeilTime m)).isStronglyPredictable.mono
        ℱ.predictable_le_prod).aestronglyMeasurable) (hH.memLp_timeMeasure T)
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
  obtain ⟨φ, hφ, hφ_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hL_lim).exists_seq_tendsto_ae
  filter_upwards [hφ_ae, hI.ae_continuous, ae_all_iff.mpr fun k ↦
    hW.ae_eq_stoppedProcess_dyadicCeilTime_of_brownianIntegrable hH hI hτ (φ k) T] with
    ω hLω hIω hdyad
  have hstop_lim : Tendsto (fun k ↦ stoppedProcess I (fun ω ↦ dyadicCeilTime (φ k) (τ ω)) T ω)
      atTop (𝓝 (stoppedProcess I τ T ω)) :=
    (TauCeti.tendsto_stoppedProcess_dyadicCeilTime I τ T ω
      hIω.continuousAt.continuousWithinAt).comp hφ.tendsto_atTop
  exact tendsto_nhds_unique hstop_lim (hLω.congr fun k ↦ hdyad k)

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
        (hloc.isStoppingTime m)) (hUI m)
  obtain ⟨V, hVprog, hVcont, hVstop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hloc.tendsto_top (fun n ↦ (hUpred n).isStronglyProgressive) (fun n ↦ (hUI n).ae_continuous)
    hcompat
  obtain ⟨I, hIpred, hIcont, hIV⟩ :=
    hVprog.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_continuous hVcont
  have hIstop (n : ℕ) : stoppedProcess I (σ n) ≡ᵐ[P] U n :=
    (hIV.stoppedProcess (σ n)).trans (hVstop n)
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
  simp only [stoppedProcess_indicator_comm']
  have hpos : ω ∈ {ω | ⊥ < nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω} :=
    bot_le.trans_lt (nnvolume.energyLocalizer_pos H (C := (n : ℝ≥0) + 1) (by positivity) ω)
  rw [Set.indicator_of_mem hpos]
  exact (hω t).symm

/-- **Existence of the Itô integral for strongly progressive integrands.** Against an almost
surely continuous filtered pre-Brownian motion, every strongly progressive integrand with almost
surely finite pathwise square energy on every finite horizon admits a predictable representative `G`
agreeing with `H` almost everywhere with respect to `(timeMeasure T).prod P` on every finite
horizon `T`, together with a predictable, almost surely continuous Itô integral `I` of `G` that is
a native local martingale on the raw filtration. By
`TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_congr`, any two such predictable
representatives yield indistinguishable Itô integrals. -/
theorem exists_isItoIntegral_of_isStronglyProgressive (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : IsStronglyProgressive ℱ H)
    (hHmem : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, MemLp (fun t ↦ H t ω) 2 (timeMeasure T)) :
    ∃ G I : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable ℱ G ∧
      (∀ T : ℝ≥0, Function.uncurry G =ᵐ[(timeMeasure T).prod P] Function.uncurry H) ∧
      IsItoIntegral ℱ P W G I ∧ IsStronglyPredictable ℱ I ∧
        Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨G, hGpred, hGH_real⟩ := hH.exists_isStronglyPredictable_ae_prod P
  have hmp (T : ℝ≥0) :
      MeasurePreserving ((↑) : ℝ≥0 → ℝ) (timeMeasure T) (volume.restrict (Ioc 0 (T : ℝ))) := by
    refine ⟨NNReal.isClosedEmbedding_coe.measurableEmbedding.measurable, ?_⟩
    have hsub : Ioc 0 (T : ℝ) ⊆ Set.range ((↑) : ℝ≥0 → ℝ) := fun x hx ↦ ⟨⟨x, hx.1.le⟩, rfl⟩
    rw [timeMeasure_def, ← NNReal.comap_volume_restrict_Ioc,
      NNReal.isClosedEmbedding_coe.measurableEmbedding.map_comap,
      Measure.restrict_restrict
        NNReal.isClosedEmbedding_coe.measurableEmbedding.measurableSet_range,
      inter_eq_self_of_subset_right hsub]
  have hGH (T : ℝ≥0) :
      Function.uncurry G =ᵐ[(timeMeasure T).prod P] Function.uncurry H :=
    (((hmp T).prod (MeasurePreserving.id P)).quasiMeasurePreserving.ae_eq_comp
      (hGH_real T)).mono fun ⟨s, ω⟩ hp ↦ by
      simpa only [Function.uncurry_apply_pair, Function.comp_apply, Prod.map_apply, id_eq,
        Real.toNNReal_coe] using hp
  have hG_loc : LocallyBrownianIntegrable ℱ P G := by
    refine locallyBrownianIntegrable_iff_nat.2 ⟨hGpred, fun n ↦ ?_⟩
    have hsec : ∀ᵐ ω ∂P, (fun t ↦ H t ω) =ᵐ[timeMeasure n] fun t ↦ G t ω := by
      filter_upwards [Measure.ae_ae_of_ae_prod
        ((Measure.measurePreserving_swap (μ := P) (ν := timeMeasure n)).quasiMeasurePreserving
          |>.ae_eq_comp (hGH n))] with ω heq
      exact heq.mono fun t ht ↦ by
        simpa only [Function.comp_apply, Prod.swap, Function.uncurry_apply_pair] using ht.symm
    filter_upwards [hHmem, hsec] with ω hω heq
    rw [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
    exact (hω n).ae_eq heq
  obtain ⟨I, hI, hIpred, hIloc⟩ := hW.exists_isItoIntegral hcont hG_loc
  exact ⟨G, I, hGpred, hGH, hI, hIpred, hIloc⟩

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
  obtain ⟨I₀, U, hI₀, -, hUI, -, -, hI₀stop⟩ := hW.exists_energyLocalized_integrals hcont hH
  have hII₀ : I ≡ᵐ[P] I₀ := isItoIntegral_unique hW hI hI₀
  have hloc := hH.isLocalizingSequence_energyLocalizer
  refine IsItoIntegral.of_stoppedProcess (hH.ite_le hτ).isStronglyPredictable
    (hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess)
    (fun n ↦ (hloc.isStoppingTime n).measurable') hloc.tendsto_top
    (fun n ↦ hW.isItoIntegral_ite_le_stoppedProcess_of_brownianIntegrable
      (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
      (hUI n) hτ)
    (fun n ↦ ?_) ?_
  · filter_upwards
      [((hII₀.stoppedProcess (nnvolume.energyLocalizer H ((n : ℝ≥0) + 1))).trans
        (hI₀stop n)).stoppedProcess τ]
      with ω hω t
    rw [stoppedProcess_stoppedProcess, inf_comm, ← stoppedProcess_stoppedProcess]
    exact hω t
  · filter_upwards [hH.ae_eventually_ite_le_energyLocalizer_eqOn] with ω hω T
    filter_upwards [hω T] with n hn t ht
    dsimp only; exact ite_congr rfl (fun _ ↦ hn ht) (fun _ ↦ rfl)

/-- **Stochastic-interval restriction for Itô integrals.** For ordered stopping times `σ ≤ τ`
and any Itô integral `I` of `H` against an almost surely continuous filtered pre-Brownian
motion, `stoppedProcess I τ - stoppedProcess I σ` is an Itô integral of `1_{(σ, τ]} H`. -/
theorem isItoIntegral_ite_Ioc_stoppedProcess_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (fun t ω ↦ stoppedProcess I τ t ω - stoppedProcess I σ t ω) := by
  have hint_eq : (fun (t : ℝ≥0) ω ↦
      if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) =
      fun (t : ℝ≥0) ω ↦ (if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) -
        (if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0) := by
    ext t ω
    by_cases htσ : (t : WithTop ℝ≥0) ≤ σ ω
    · have htτ : (t : WithTop ℝ≥0) ≤ τ ω := htσ.trans (hστ ω)
      rw [ite_eq_right (not_and_of_not_left _ (not_lt.mpr htσ)), ite_eq_left htτ, ite_eq_left htσ,
        sub_self]
    · have hσt : σ ω < (t : WithTop ℝ≥0) := not_le.mp htσ
      by_cases htτ : (t : WithTop ℝ≥0) ≤ τ ω
      · rw [ite_eq_left ⟨hσt, htτ⟩, ite_eq_left htτ, ite_eq_right htσ, sub_zero]
      · rw [ite_eq_right (not_and_of_not_right _ htτ), ite_eq_right htτ, ite_eq_right htσ,
          sub_zero]
  rw [hint_eq]
  exact (hW.isItoIntegral_ite_le_stoppedProcess hcont hI hτ).sub
    (hW.isItoIntegral_ite_le_stoppedProcess hcont hI hσ)

/-- **Adjacent stochastic-interval concatenation for stopped Itô integrals.** For ordered random
times `σ ≤ τ ≤ ρ` where `σ` and `ρ` are stopping times, summing Itô integrals of `1_{(σ, τ]} H` and
`1_{(τ, ρ]} H` is indistinguishable from `stoppedProcess I ρ - stoppedProcess I σ`. -/
theorem indist_ite_Ioc_add_stoppedProcess_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I) {σ τ ρ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hρ : IsStoppingTime ℱ ρ)
    (hστ : σ ≤ τ) (hτρ : τ ≤ ρ) {J₁ J₂ : ℝ≥0 → Ω → ℝ}
    (hJ₁ : IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J₁)
    (hJ₂ : IsItoIntegral ℱ P W
      (fun t ω ↦ if τ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0) J₂) :
    (fun t ω ↦ J₁ t ω + J₂ t ω) ≡ᵐ[P]
      fun t ω ↦ stoppedProcess I ρ t ω - stoppedProcess I σ t ω :=
  isItoIntegral_unique hW (hJ₁.ite_Ioc_add hστ hτρ hJ₂)
    (hW.isItoIntegral_ite_Ioc_stoppedProcess_sub hcont hI hσ hρ (hστ.trans hτρ))

private theorem stoppedProcess_integral_sq_timeMeasure_eq
    (hH : IsStronglyPredictable ℱ H) {τ : Ω → WithTop ℝ≥0}
    (hcut : IsStronglyPredictable ℱ (fun s ω ↦
      if (s : WithTop ℝ≥0) ≤ τ ω then nnvolume.finiteEnergyCutoff H s ω else 0))
    (t : ℝ≥0) {ω : Ω} (hfin : ∀ u : ℝ≥0, nnvolume.accumulatedEnergy H u ω < ∞) :
    (∫ s, (if (s : WithTop ℝ≥0) ≤ τ ω then nnvolume.finiteEnergyCutoff H s ω else 0) ^ 2
      ∂timeMeasure t) =
      stoppedProcess (fun u ω' ↦ ∫ s, H s ω' ^ 2 ∂timeMeasure u) τ t ω := by
  have hacc : ∀ u, nnvolume.accumulatedEnergy (nnvolume.finiteEnergyCutoff H) u ω =
      nnvolume.accumulatedEnergy H u ω := fun u ↦
    nnvolume.accumulatedEnergy_finiteEnergyCutoff_of_lt_top (hfin u)
  have hLHS :
      (∫ s, (if (s : WithTop ℝ≥0) ≤ τ ω then nnvolume.finiteEnergyCutoff H s ω else 0) ^ 2
        ∂timeMeasure t) =
        (stoppedProcess (nnvolume.accumulatedEnergy H) τ t ω).toReal := by
    rw [hcut.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy t ω,
      nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc _ t ω,
      nnvolume.setLIntegral_enorm_sq_ite_le_eq_stoppedProcess_accumulatedEnergy
        (nnvolume.finiteEnergyCutoff H) τ t ω]
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hacc]
  have hRHS :
      stoppedProcess (fun u ω' ↦ ∫ s, H s ω' ^ 2 ∂timeMeasure u) τ t ω =
        (stoppedProcess (nnvolume.accumulatedEnergy H) τ t ω).toReal := by
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue,
      hH.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy]
  exact hLHS.trans hRHS.symm

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
  filter_upwards [(hII₀.stoppedProcess (σ n)).trans (hI₀stop n),
    hH.ae_accumulatedEnergy_lt_top] with ω hIω hfin
  simp only [stoppedProcess_indicator_comm']
  have hpos : ω ∈ {ω | ⊥ < nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω} :=
    bot_le.trans_lt (nnvolume.energyLocalizer_pos H (C := (n : ℝ≥0) + 1) (by positivity) ω)
  rw [Set.indicator_of_mem hpos]
  have hI_eq : U n t ω = stoppedProcess I (σ n) t ω := (hIω t).symm
  have hE_eq := stoppedProcess_integral_sq_timeMeasure_eq hH.isStronglyPredictable
    (hHseq n).isStronglyPredictable t (τ := σ n) hfin
  have hstop_sub :
      stoppedProcess (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) (σ n) t ω =
        stoppedProcess I (σ n) t ω ^ 2 -
          stoppedProcess (fun u ω' ↦ ∫ s, H s ω' ^ 2 ∂timeMeasure u) (σ n) t ω := by
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue]
  rw [hstop_sub, ← hI_eq, ← hE_eq]

end IsFilteredPreBrownianReal

end TauCeti.Probability
