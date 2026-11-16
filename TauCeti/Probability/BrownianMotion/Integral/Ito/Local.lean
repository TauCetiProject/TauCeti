/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
import Mathlib.MeasureTheory.Integral.Indicator
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.StoppedValue
import TauCeti.Probability.Process.Stopping

/-!
# Optional stopping, local-martingale property, and localized Brownian Itô integration

`TauCeti.LocallyBrownianIntegrable ℱ P H` relaxes `TauCeti.BrownianIntegrable ℱ P H` to predictable
integrands with a.s. finite pathwise square energy on every finite horizon. On a raw filtration,
optional stopping (`IsItoIntegral.stoppedProcess`, `stoppedProcess_indist`) and the local-martingale
property (`IsItoIntegral.locally_martingale`) hold for any filtered pre-Brownian motion `W`, and
`LocallyBrownianIntegrable.exists_isItoIntegral` constructs a strongly progressive continuous
local-martingale Itô integral whenever `W` has a.s. continuous paths.

## Main results

* `TauCeti.IsItoIntegral.stoppedProcess`, `TauCeti.IsItoIntegral.stoppedProcess_indist`: stopping a
  continuous Itô integral at a stopping time `σ` integrates `H · 1_{[0, σ]}`.
* `TauCeti.IsItoIntegral.locally_martingale`: strongly progressive continuous Itô integrals are
  native local martingales on the raw filtration.
* `TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral`: existence of a strongly progressive
  continuous local-martingale Itô integral for `LocallyBrownianIntegrable` integrands.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H I J : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0}

/-! ### Optional stopping and local-martingale property -/

namespace IsItoIntegral

private theorem tendsto_inv_add_one : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
  simpa [Function.comp_def] using ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)

private theorem tendstoInMeasure_stoppedProcess_simpleGains_dyadicCeilTime
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {T : ℝ≥0} (k : ℕ)
    {n : ℕ → ℕ} {τ₀ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ₀ : ∀ m, MonotoneOn (τ₀ m) (Iic (n m)))
    (ha : ∀ m i, i < n m → StronglyMeasurable[ℱ (τ₀ m i)] (a m i))
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ₀ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure T}) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun m ↦ MeasureTheory.stoppedProcess (Finance.simpleGains (τ₀ m) (n m) (a m) W)
        (fun ω ↦ dyadicCeilTime k (σ ω)) T)
      atTop (MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (σ ω)) T) := by
  let S : Finset ℝ≥0 := insert T ((range ⌈T * 2 ^ k⌉₊).image fun r : ℕ ↦ (r : ℝ≥0) / 2 ^ k)
  have hsT {s : ℝ≥0} (hs : s ∈ S) : s ≤ T := by
    rcases mem_insert.mp hs with rfl | hs'
    · exact le_rfl
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp hs'
      exact ((div_lt_iff₀ (by positivity)).mpr (Nat.lt_ceil.mp (mem_range.mp hr))).le
  have hrange (ω : Ω) : (min (T : WithTop ℝ≥0) (dyadicCeilTime k (σ ω))).untopA ∈ S := by
    rcases le_or_gt (T : WithTop ℝ≥0) (dyadicCeilTime k (σ ω)) with hle | hgt
    · rw [min_eq_left hle, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      exact mem_insert_self T _
    · cases hσω : σ ω with
      | top => rw [hσω, dyadicCeilTime_top] at hgt; exact (not_top_lt hgt).elim
      | coe u =>
        rw [hσω, dyadicCeilTime_coe] at hgt
        rw [dyadicCeilTime_coe, min_eq_right hgt.le,
          WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
        exact mem_insert_of_mem (mem_image.mpr ⟨⌈u * 2 ^ k⌉₊, mem_range.mpr
          (Nat.lt_ceil.mpr ((div_lt_iff₀ (by positivity)).mp (WithTop.coe_lt_coe.mp hgt))), rfl⟩)
  have hgains_s {s : ℝ≥0} (hs : s ∈ S) :
      TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ₀ m) (n m) (a m) W s) atTop (I s) :=
    hI.tendstoInMeasure_simpleGains hW hτ₀ ha fun ε hε ↦
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (henergy ε hε)
        (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω hω ↦ by
          simp only [Set.mem_ofPred_eq] at hω ⊢
          refine hω.trans ?_
          rw [← min_eq_left (hsT hs), ← Probability.timeMeasure_restrict T s]
          exact lintegral_mono' Measure.restrict_le_self le_rfl
  exact fun ε hε ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using tendsto_finsetSum S fun s hs ↦ hgains_s hs ε hε) (fun _ ↦ zero_le) fun m ↦
    (measure_mono fun ω hω ↦ mem_biUnion (hrange ω) hω).trans (measure_biUnion_finset_le S _)

private theorem tendsto_measure_lintegral_ite_le_dyadicCeilTime_sub_sq [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (hσ : IsStoppingTime ℱ σ) (T : ℝ≥0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
        if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2
      ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  let D (k : ℕ) (ω : Ω) : ℝ≥0∞ := ∫⁻ s,
    ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
      if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2 ∂Probability.timeMeasure T
  have hdiff_m (k : ℕ) : Measurable (Function.uncurry fun (s : ℝ≥0) ω ↦
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
        if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2) :=
    (((hH.ite_le (hσ.dyadicCeilTime k)).isStronglyPredictable.sub
      (hH.ite_le hσ).isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
  have hmem : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∈ {ω | ε ≤ D k ω} ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hH.ae_memLp] with ω hω
    have hT : MemLp (fun s ↦ H s ω) 2 (Probability.timeMeasure T) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hω T
    have hdom (k : ℕ) (s : ℝ≥0) :
        ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
          if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2 ≤ ‖H s ω‖ₑ ^ 2 := by
      by_cases hs : (s : WithTop ℝ≥0) ≤ σ ω
      · rw [ite_eq_left (hs.trans (le_dyadicCeilTime k (σ ω))), ite_eq_left hs]; simp
      · rw [ite_eq_right hs, sub_zero]; split_ifs <;> simp
    have hpt (s : ℝ≥0) : Tendsto (fun k ↦
        ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
          if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2) atTop (𝓝 0) := by
      by_cases hs : (s : WithTop ℝ≥0) ≤ σ ω
      · refine tendsto_const_nhds.congr fun k ↦ ?_
        rw [ite_eq_left (hs.trans (le_dyadicCeilTime k (σ ω))), ite_eq_left hs]; simp
      · refine tendsto_const_nhds.congr' <|
          ((tendsto_dyadicCeilTime (σ ω)).eventually (eventually_lt_nhds (lt_of_not_ge hs))).mono
            fun k hk ↦ by dsimp only; rw [ite_eq_right hk.not_ge, ite_eq_right hs]; simp
    have hD0 : Tendsto (fun k ↦ D k ω) atTop (𝓝 0) := by
      simpa [D] using tendsto_lintegral_of_dominated_convergence (fun s ↦ ‖H s ω‖ₑ ^ 2)
        (fun k ↦ (hdiff_m k).comp (measurable_id.prodMk measurable_const))
        (fun k ↦ .of_forall (hdom k))
        (hT.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.mp hT).ne (.of_forall hpt)
    exact (hD0.eventually (eventually_lt_nhds hε)).mono fun _ hk ↦ by simp [hk.not_ge]
  simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
    (fun k ↦ measurableSet_le measurable_const (hdiff_m k).lintegral_prod_left') hmem

private theorem tendstoInMeasure_stoppedProcess_diag
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hσ : IsStoppingTime ℱ σ) (hI : IsItoIntegral ℱ P W H I) {T : ℝ≥0}
    {N : ℕ → ℕ} {γ : ℕ → ℕ → ℝ≥0} {c : ℕ → ℕ → Ω → ℝ}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ} {m : ℕ → ℕ}
    (hstep : ∀ k, TendstoInMeasure P
      (fun j ↦ MeasureTheory.stoppedProcess (Finance.simpleGains (τ j) (n j) (a j) W)
        (fun ω ↦ dyadicCeilTime k (σ ω)) T)
      atTop (MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (σ ω)) T))
    (hτ : ∀ j, MonotoneOn (τ j) (Iic (n j)))
    (ha : ∀ j i, i < n j → StronglyMeasurable[ℱ (τ j i)] (a j i))
    (hgains_eq : ∀ k ω, Finance.simpleGains (γ k) (N k) (c k) W T ω =
      MeasureTheory.stoppedProcess (Finance.simpleGains (τ (m k)) (n (m k)) (a (m k)) W)
        (fun ω ↦ dyadicCeilTime k (σ ω)) T ω)
    (hm_gain : ∀ k : ℕ, P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ edist
      (MeasureTheory.stoppedProcess (Finance.simpleGains (τ (m k)) (n (m k)) (a (m k)) W)
        (fun ω ↦ dyadicCeilTime k (σ ω)) T ω)
      (MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (σ ω)) T ω)} <
        ((k : ℝ≥0∞) + 1)⁻¹) :
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (γ k) (N k) (c k) W T) atTop
      (MeasureTheory.stoppedProcess I σ T) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hI_lim : TendstoInMeasure P
      (fun k ↦ MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (σ ω)) T)
      atTop (MeasureTheory.stoppedProcess I σ T) :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (hstep k).aestronglyMeasurable fun j ↦
      (((Finance.stronglyAdapted_simpleGains (hτ j) (ha j) hW.adapted.stronglyAdapted)
        |>.stoppedProcess_of_countable_range (hσ.dyadicCeilTime k)
          (countable_range_dyadicCeilTime σ k) T).mono (ℱ.le T)).aestronglyMeasurable)
      (hI.ae_continuous.mono fun ω hω ↦
        tendsto_stoppedProcess_dyadicCeilTime I σ T ω hω.continuousAt.continuousWithinAt)
  have hdiff : TendstoInMeasure P
      (fun k ω ↦ Finance.simpleGains (γ k) (N k) (c k) W T ω -
        MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (σ ω)) T ω) atTop 0 :=
    tendstoInMeasure_of_tendsto_measure_rate_lt_edist tendsto_inv_add_one <|
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_inv_add_one
        (fun _ ↦ zero_le) fun k ↦ (measure_mono fun ω hω ↦ by
          simp only [Set.mem_ofPred_eq, Pi.zero_apply, hgains_eq k ω, eDist_eq_eNorm_sub,
            sub_zero] at hω ⊢
          exact hω.le).trans (hm_gain k).le
  exact (hdiff.add hI_lim).congr (fun _ ↦ .of_forall fun _ ↦ sub_add_cancel _ _)
    (.of_forall fun _ ↦ zero_add _)

private theorem tendsto_measure_lintegral_stoppedProcess_diag [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (hσ : IsStoppingTime ℱ σ) {T : ℝ≥0}
    {N : ℕ → ℕ} {γ : ℕ → ℕ → ℝ≥0} {c : ℕ → ℕ → Ω → ℝ}
    {n : ℕ → ℕ} {τ₀ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ} {m : ℕ → ℕ}
    (hcm : ∀ k j, j < N k → StronglyMeasurable[ℱ (γ k j)] (c k j))
    (hhold : ∀ k, ∀ s ∈ Ioc 0 T, ∀ ω, Finance.simpleHolding (γ k) (N k) (c k) s ω =
      if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then
        Finance.simpleHolding (τ₀ (m k)) (n (m k)) (a (m k)) s ω else 0)
    (hm_hold : ∀ k : ℕ, P {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ ∫⁻ s,
      ‖Finance.simpleHolding (τ₀ (m k)) (n (m k)) (a (m k)) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure T} < ((k : ℝ≥0∞) + 1)⁻¹)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s,
      ‖Finance.simpleHolding (γ k) (N k) (c k) s ω -
        if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2
      ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  have he₁ (δ : ℝ≥0∞) (hδ : 0 < δ) : Tendsto (fun k ↦ P {ω | δ ≤ ∫⁻ s,
      ‖Finance.simpleHolding (γ k) (N k) (c k) s ω -
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0‖ₑ ^ 2
      ∂Probability.timeMeasure T}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_add_one
      (.of_forall fun _ ↦ zero_le) ((tendsto_inv_add_one.eventually_lt_const hδ).mono fun k hk ↦
        (measure_mono fun ω hω ↦ (hk.le.trans hω).trans <| lintegral_mono_ae
          ((Probability.ae_mem_Ioc_timeMeasure T).mono fun s hs ↦ by
            rw [hhold k s hs ω]; split_ifs <;> simp)).trans (hm_hold k).le)
  simpa only [Function.comp_apply, id_eq, Pi.sub_apply, Function.uncurry_apply_pair,
      sub_add_sub_cancel] using MeasureTheory.tendsto_measure_lintegral_enorm_add_sq
    (.of_forall fun k ω ↦ ((((Finance.isStronglyPredictable_simpleHolding (hcm k)).sub
      (hH.ite_le (hσ.dyadicCeilTime k)).isStronglyPredictable).mono
        ℱ.predictable_le_prod).measurable.comp
          (measurable_id.prodMk measurable_const) |>.eNorm.pow_const 2).aemeasurable)
    he₁ (tendsto_measure_lintegral_ite_le_dyadicCeilTime_sub_sq hH hσ T) hε

/-- **Optional stopping for the continuous Brownian Itô integral**: stopping `I` at a stopping time
`σ` yields an Itô integral of `H · 1_{[0, σ]}`, without path continuity of `W` or moment bounds. -/
theorem stoppedProcess (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hσ : IsStoppingTime ℱ σ) (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I σ) where
  isStronglyPredictable := (hI.locallyBrownianIntegrable.ite_le hσ).isStronglyPredictable
  ae_continuous := hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess
  exists_seq_approx T := by
    let := (hW.hasLaw_eval 0).isProbabilityMeasure
    obtain ⟨n, τ₀, a, hτ₀, ha, hba, henergy, -⟩ := hI.exists_seq_approx T
    have hstep (k : ℕ) :=
      tendstoInMeasure_stoppedProcess_simpleGains_dyadicCeilTime (σ := σ) hW hI k hτ₀ ha henergy
    have hr (k : ℕ) : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.mpr (by simp [ENNReal.natCast_ne_top])
    choose m hm_hold hm_gain using fun k ↦
      (((henergy _ (hr k)).eventually (gt_mem_nhds (hr k))).and
        ((hstep k _ (hr k)).eventually (gt_mem_nhds (hr k)))).exists
    choose N γ c _ hγ hcm hcb hhold hgains using fun k ↦
      Finance.exists_simpleHolding_simpleGains_dyadicCeilTime hσ k T (hτ₀ (m k)) (ha (m k))
    refine ⟨N, γ, c, fun k ↦ (hγ k).monotoneOn, hcm, fun k j hj ↦ ?_,
      tendsto_measure_lintegral_stoppedProcess_diag hI.locallyBrownianIntegrable hσ hcm hhold
        hm_hold,
      tendstoInMeasure_stoppedProcess_diag hW hσ hI hstep hτ₀ ha
        (fun k ω ↦ hgains k W le_rfl ω) hm_gain⟩
    choose C hC using fun (i : Fin (n (m k))) ↦ hba (m k) i.1 i.2
    refine ⟨⌈T * 2 ^ k⌉₊ * ∑ i : Fin (n (m k)), C i, fun ω ↦ (hcb k j hj ω).trans ?_⟩
    rw [← Fin.sum_univ_eq_sum_range]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _ ↦ hC i ω) (Nat.cast_nonneg _)

/-- Stopping an Itô integral `I` at `σ` is indistinguishable from any Itô integral `J` of
`H · 1_{[0, σ]}`, without assuming path continuity of `W`. -/
theorem stoppedProcess_indist (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hσ : IsStoppingTime ℱ σ) (hI : IsItoIntegral ℱ P W H I)
    (hJ : IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0) J) :
    MeasureTheory.stoppedProcess I σ ≡ᵐ[P] J :=
  (hI.stoppedProcess hW hσ).indist hW hJ

end IsItoIntegral

private def energyStage (H : ℝ≥0 → Ω → ℝ) (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then
    nnvolume.finiteEnergyCutoff H t ω else 0

/-- Every strongly progressive continuous Itô integral against a filtered pre-Brownian motion `W`
is a native local martingale on the raw filtration, without path continuity of `W` or moment
bounds. -/
theorem IsItoIntegral.locally_martingale
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hprog : IsStronglyProgressive ℱ I) :
    Locally (fun X ↦ Martingale X ℱ P) ℱ I P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ (k : ℕ) := nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  have hτ_loc : IsLocalizingSequence ℱ τ P :=
    hI.locallyBrownianIntegrable.isLocalizingSequence_energyLocalizer
  have hHs (k : ℕ) : BrownianIntegrable ℱ P (energyStage H k) :=
    hI.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((k : ℝ≥0) + 1)
  have hmart (k : ℕ) : Martingale (MeasureTheory.stoppedProcess I (τ k)) ℱ P :=
    ((hI.stoppedProcess hW (hτ_loc.isStoppingTime k)).congr_integrand
      (hHs k).isStronglyPredictable fun T ↦ by
        filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := Probability.timeMeasure T)
            (ν := P)).ae (Probability.ae_mem_Ioc_timeMeasure T),
          (Measure.quasiMeasurePreserving_snd (μ := Probability.timeMeasure T)
            (ν := P)).ae hI.locallyBrownianIntegrable.ae_accumulatedEnergy_lt_top] with p hpT hfin
        dsimp only [Function.uncurry, energyStage, τ]
        have hcut : nnvolume.finiteEnergyCutoff H p.1 p.2 = H p.1 p.2 :=
          nnvolume.finiteEnergyCutoff_eqOn (hfin T) hpT.2
        rw [hcut]).martingale hW (hHs k)
      (hprog.stoppedProcess (hτ_loc.isStoppingTime k)).stronglyAdapted
  refine hprog.locally_martingale_of_ae_stopped_eq hτ_loc hmart fun k _ ↦ .of_forall fun ω ↦ by
    simp only [MeasureTheory.stoppedProcess]; rw [indicator_of_mem]
    simpa only [Set.mem_ofPred_eq, ← WithTop.coe_bot, NNReal.bot_eq_zero, WithTop.coe_zero] using
      nnvolume.energyLocalizer_pos H (by positivity) ω

/-! ### Localized existence -/

private theorem tendsto_measure_lintegral_of_ae_eventually_eqOn [IsFiniteMeasure P]
    {L H_stage : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hL : ∀ k, IsStronglyPredictable ℱ (L k))
    (hHs : ∀ k, IsStronglyPredictable ℱ (H_stage k))
    (hH : IsStronglyPredictable ℱ H)
    (hstage : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖L k s ω - H_stage k s ω‖ₑ ^ 2 ∂Probability.timeMeasure T}) atTop (𝓝 0))
    (heq : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, EqOn (H_stage k · ω) (H · ω) (Iic T))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖L k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  let Es (k : ℕ) (ω : Ω) := ∫⁻ s, ‖L k s ω - H_stage k s ω‖ₑ ^ 2 ∂Probability.timeMeasure T
  let E (k : ℕ) (ω : Ω) := ∫⁻ s, ‖L k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T
  have hm {g : ℝ≥0 → Ω → ℝ} (hg : IsStronglyPredictable ℱ g) (k : ℕ) :
      Measurable (fun ω ↦ ∫⁻ s, ‖L k s ω - g s ω‖ₑ ^ 2 ∂Probability.timeMeasure T) :=
    ((((hL k).sub hg).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2).lintegral_prod_left'
  let B (k : ℕ) : Set Ω := {ω | ε ≤ E k ω} \ {ω | ε ≤ Es k ω}
  have hB_lim : Tendsto (fun k ↦ P (B k)) atTop (𝓝 0) := by
    simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (As := B)
      atTop MeasurableSet.empty
      (fun k ↦ (measurableSet_le measurable_const (hm hH k)).diff
        (measurableSet_le measurable_const (hm (hHs k) k)))
      (heq.mono fun ω hω ↦ hω.mono fun k hk ↦ by
        have hEq : E k ω = Es k ω := lintegral_congr_ae
          ((Probability.ae_mem_Ioc_timeMeasure T).mono fun s hs ↦ by
            have hEqs : H_stage k s ω = H s ω := hk hs.2; dsimp only; rw [hEqs])
        simp [B, hEq])
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (hstage ε hε).add hB_lim) (fun _ ↦ zero_le) fun k ↦
    (measure_mono fun _ hω ↦ by simp only [B, Set.mem_union, Set.mem_sdiff]; tauto).trans
      (measure_union_le _ _)

private theorem eLpNorm_simpleGains_sub_eq_of_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hHs : BrownianIntegrable ℱ P K) (hU : IsItoIntegral ℱ P W K J)
    {n : ℕ} {γ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ} (hγ : MonotoneOn γ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (γ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    eLpNorm (Finance.simpleGains γ n a W T - J T) 2 P =
      eLpNorm (fun p ↦ Finance.simpleHolding γ n a p.1 p.2 - K p.1 p.2) 2
        ((Probability.timeMeasure T).prod P) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  rw [← Lp.edist_toLp_toLp _ _ (hW.memLp_simpleGains hγ ha ha₂ T) (hU.memLp hW hHs T),
    ← hW.l2Integral_toLp_simpleHolding hγ ha ha₂ T, hU.toLp_eq_l2Integral hW hHs T,
    (hW.l2Integral T).isometry.edist_eq, Lp.edist_toLp_toLp, ℱ.predictableMeasure_def,
    eLpNorm_trim ℱ.predictable_le_prod
      ((Finance.isStronglyPredictable_simpleHolding ha).sub hHs.isStronglyPredictable)]
  rfl

private theorem isItoIntegral_of_stopped_stages
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : IsStronglyPredictable ℱ H) (hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    {τ : ℕ → Ω → WithTop ℝ≥0} {H_stage U : ℕ → ℝ≥0 → Ω → ℝ}
    (hτ_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hHs : ∀ k, BrownianIntegrable ℱ P (H_stage k))
    (hU : ∀ k, IsItoIntegral ℱ P W (H_stage k) (U k))
    (hI_stop : ∀ k T, MeasureTheory.stoppedProcess I (τ k) T =ᵐ[P] U k T)
    (heq : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ k in atTop, EqOn (H_stage k · ω) (H · ω) (Iic T)) :
    IsItoIntegral ℱ P W H I where
  isStronglyPredictable := hH
  ae_continuous := hI_cont
  exists_seq_approx T := by
    let := (hW.hasLaw_eval 0).isProbabilityMeasure
    choose n γ a C _ hγ ha hb herr using fun k : ℕ ↦
      ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P T (hHs k).isStronglyPredictable
        ((hHs k).memLp_timeMeasure T) (ENNReal.inv_pos.mpr (by simp [ENNReal.natCast_ne_top] :
          ((k : ℝ≥0∞) + 1) ≠ ∞))
    have hl2_hold : Tendsto (fun k ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (γ k) (n k) (a k) p.1 p.2 - H_stage k p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds IsItoIntegral.tendsto_inv_add_one
        (fun _ ↦ zero_le) fun k ↦ (herr k).le
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k) (.of_forall (hb k j hj))
    have hl2_gain : Tendsto (fun k ↦ eLpNorm
        ((Finance.simpleGains (γ k) (n k) (a k) W T - U k T) - 0) 2 P) atTop (𝓝 0) :=
      hl2_hold.congr fun k ↦ by
        rw [sub_zero, ← eLpNorm_simpleGains_sub_eq_of_isItoIntegral hW (hHs k) (hU k)
          (hγ k).monotoneOn (ha k) (ha₂ k) T]
    refine ⟨n, γ, a, fun k ↦ (hγ k).monotoneOn, ha, fun k j hj ↦ ⟨C k, hb k j hj⟩,
      tendsto_measure_lintegral_of_ae_eventually_eqOn
        (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k))
        (fun k ↦ (hHs k).isStronglyPredictable) hH (fun _ hε ↦
          MeasureTheory.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
            (.of_forall fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
              (hHs k).isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
            hl2_hold hε)
        (heq.mono fun _ hω ↦ hω T),
      ((tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hl2_gain).add
        (MeasureTheory.tendstoInMeasure_of_stoppedProcess_ae_eq hτ_top
          (fun k ↦ ((hU k).memLp hW (hHs k) T).aestronglyMeasurable) (fun k ↦ hI_stop k T))).congr
        (fun _ ↦ .of_forall fun _ ↦ sub_add_cancel _ _) (.of_forall fun _ ↦ zero_add _)⟩

/-- **Existence of the localized continuous Brownian Itô integral**: every
`LocallyBrownianIntegrable` integrand against an a.s. continuous filtered pre-Brownian motion `W`
admits a strongly progressive continuous local-martingale Itô integral on the raw filtration. -/
theorem LocallyBrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun X ↦ Martingale X ℱ P) ℱ I P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ (k : ℕ) := nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  have hτ_loc : IsLocalizingSequence ℱ τ P := hH.isLocalizingSequence_energyLocalizer
  have hHs (k : ℕ) : BrownianIntegrable ℱ P (energyStage H k) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((k : ℝ≥0) + 1)
  choose U hU_ito hU_pred _ using fun k ↦ (hHs k).exists_isItoIntegral hW hcont
  have hcompat (k m : ℕ) (hkm : k ≤ m) : MeasureTheory.stoppedProcess (U m) (τ k) ≡ᵐ[P] U k := by
    have hcut : (fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ τ k ω then energyStage H m t ω else 0) =
        energyStage H k := by
      ext t ω; dsimp only [energyStage, τ]
      have hmono := nnvolume.monotone_energyLocalizer H ω
        (add_le_add (Nat.cast_le.mpr hkm) (le_rfl : (1 : ℝ≥0) ≤ 1))
      split_ifs with h1 h2
      · rfl
      · exact (h2 (h1.trans hmono)).elim
      · rfl
    exact (hU_ito m).stoppedProcess_indist hW (hτ_loc.isStoppingTime k) (hcut ▸ hU_ito k)
  obtain ⟨I, hI_prog, hI_cont, hI_stop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hτ_loc.tendsto_top (fun k ↦ (hU_pred k).isStronglyProgressive)
    (fun k ↦ (hU_ito k).ae_continuous) hcompat
  have hI_ito := isItoIntegral_of_stopped_stages hW hH.isStronglyPredictable hI_cont
    hτ_loc.tendsto_top hHs hU_ito (fun k T ↦ (hI_stop k).mono fun _ hω ↦ hω T)
    hH.ae_eventually_ite_le_energyLocalizer_eqOn
  exact ⟨I, hI_ito, hI_prog, hI_ito.locally_martingale hW hI_prog⟩

end TauCeti
