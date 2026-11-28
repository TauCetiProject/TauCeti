/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Order.Interval.Set.Piecewise
import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
import TauCeti.Probability.Process.StochasticInterval
import TauCeti.Probability.Process.StoppedValue
import TauCeti.Probability.Process.Stopping
import TauCeti.Topology.Instances.ENNReal

/-!
# Optional stopping and stochastic-interval restriction for the Brownian Itô integral

For any continuous Itô integral `I` of `H` against a filtered pre-Brownian motion `W` on a raw
filtration, stopping `I` at a stopping time `σ` gives a continuous Itô integral of
`H · 1_{[0, σ]}` (`TauCeti.Probability.IsItoIntegral.stoppedProcess`), without path continuity of
`W` or moment bounds. As a consequence, `stoppedProcess I σ` is indistinguishable from any Itô
integral of `H · 1_{[0, σ]}` (`TauCeti.Probability.IsItoIntegral.stoppedProcess_indist`), and for
stopping times `σ ≤ τ`, `stoppedProcess I τ - stoppedProcess I σ` is an Itô integral of
`H · 1_{(σ, τ]}` (`TauCeti.Probability.IsItoIntegral.ite_Ioc`). Adjacent stochastic intervals
`(σ, τ]` and `(τ, ρ]` concatenate to `(σ, ρ]` (`TauCeti.Probability.IsItoIntegral.ite_Ioc_add`,
`TauCeti.Probability.IsFilteredPreBrownianReal.indist_ite_Ioc_add_stoppedProcess_sub`).
Stopping along any sequence of measurable random times tending almost surely to `⊤` characterizes
the Itô integral without requiring monotonicity or the stopping-time property
(`TauCeti.Probability.IsItoIntegral.of_stoppedProcess`).

## Main results

* `TauCeti.Probability.IsItoIntegral.stoppedProcess`,
  `TauCeti.Probability.IsItoIntegral.stoppedProcess_indist`: stopping a continuous Itô integral at a
  stopping time `σ` integrates `H · 1_{[0, σ]}`.
* `TauCeti.Probability.IsItoIntegral.ite_Ioc`: restricting an integrand to `(σ, τ]` for stopping
  times `σ ≤ τ` integrates to `stoppedProcess I τ - stoppedProcess I σ`.
* `TauCeti.Probability.IsItoIntegral.ite_Ioc_add` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.indist_ite_Ioc_add_stoppedProcess_sub`:
  adjacent stochastic-interval concatenation for Itô integrals and stopped integrals.
* `TauCeti.Probability.IsItoIntegral.of_stoppedProcess`: stability of `IsItoIntegral` under
  localization by measurable random times tending almost surely to `⊤`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H I J : ℝ≥0 → Ω → ℝ}

namespace IsItoIntegral

section

variable {σ : Ω → WithTop ℝ≥0}

private theorem tendstoInMeasure_stoppedProcess_simpleGains_dyadicCeilTime
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {T : ℝ≥0} (k : ℕ)
    {n : ℕ → ℕ} {τ₀ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ₀ : ∀ m, MonotoneOn (τ₀ m) (Iic (n m)))
    (ha : ∀ m i, i < n m → StronglyMeasurable[ℱ (τ₀ m i)] (a m i))
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ₀ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure T}) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun m ↦ MeasureTheory.stoppedProcess (Finance.simpleGains (τ₀ m) (n m) (a m) W)
        (fun ω ↦ dyadicCeilTime k (σ ω)) T)
      atTop (MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (σ ω)) T) := by
  let hfin := finite_range_untopA_min_dyadicCeilTime σ k T
  let S : Finset ℝ≥0 := hfin.toFinset
  have hsT {s : ℝ≥0} (hs : s ∈ S) : s ≤ T := by
    obtain ⟨ω, rfl⟩ := hfin.mem_toFinset.mp hs
    exact WithTop.untopA_le (min_le_left _ _)
  have hrange (ω : Ω) : (min (T : WithTop ℝ≥0) (dyadicCeilTime k (σ ω))).untopA ∈ S :=
    hfin.mem_toFinset.mpr ⟨ω, rfl⟩
  have hgains_s {s : ℝ≥0} (hs : s ∈ S) :
      TendstoInMeasure P (fun m ↦ Finance.simpleGains (τ₀ m) (n m) (a m) W s) atTop (I s) :=
    hI.tendstoInMeasure_simpleGains hW hτ₀ ha fun ε hε ↦
      MeasureTheory.tendsto_measure_lintegral_mono (timeMeasure_mono (hsT hs)) henergy hε
  exact fun ε hε ↦ tendsto_measure_of_subset_biUnion_finset S (fun s hs ↦ hgains_s hs ε hε)
    fun m ω hω ↦ by
      let s := (min (T : WithTop ℝ≥0) (dyadicCeilTime k (σ ω))).untopA
      have hs : s ∈ S := hrange ω
      dsimp only at hω
      rw [Set.mem_ofPred_eq, MeasureTheory.stoppedProcess_apply,
        MeasureTheory.stoppedProcess_apply] at hω
      exact mem_biUnion hs hω

private theorem tendstoInMeasure_stoppedProcess_diag
    (hW : IsFilteredPreBrownianReal ℱ W P)
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
    tendstoInMeasure_of_tendsto_measure_rate_lt_edist
      (ENNReal.tendsto_inv_natCast_add_nhds_zero 1) <|
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_inv_natCast_add_nhds_zero 1)
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
        ∂timeMeasure T} < ((k : ℝ≥0∞) + 1)⁻¹)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s,
      ‖Finance.simpleHolding (γ k) (N k) (c k) s ω -
        if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2
      ∂timeMeasure T}) atTop (𝓝 0) := by
  have he₁ (δ : ℝ≥0∞) (hδ : 0 < δ) : Tendsto (fun k ↦ P {ω | δ ≤ ∫⁻ s,
      ‖Finance.simpleHolding (γ k) (N k) (c k) s ω -
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0‖ₑ ^ 2
      ∂timeMeasure T}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (ENNReal.tendsto_inv_natCast_add_nhds_zero 1) (.of_forall fun _ ↦ zero_le)
      (((ENNReal.tendsto_inv_natCast_add_nhds_zero 1).eventually_lt_const hδ).mono fun k hk ↦
        (measure_mono fun ω hω ↦ (hk.le.trans hω).trans <| lintegral_mono_ae
          ((ae_mem_Ioc_timeMeasure T).mono fun s hs ↦ by
            rw [hhold k s hs ω]; split_ifs <;> simp)).trans (hm_hold k).le)
  simpa only [Function.comp_apply, id_eq, Pi.sub_apply, Function.uncurry_apply_pair,
      sub_add_sub_cancel] using MeasureTheory.tendsto_measure_lintegral_enorm_add_sq
    (.of_forall fun k ω ↦
      (IsStronglyPredictable.measurable_enorm_sq_path
        (H := fun s ω ↦ Finance.simpleHolding (γ k) (N k) (c k) s ω -
          if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0)
        ((Finance.isStronglyPredictable_simpleHolding (hcm k)).sub
          (hH.ite_le (hσ.dyadicCeilTime k)).isStronglyPredictable)).aemeasurable)
    he₁ (hH.tendsto_measure_lintegral_ite_le_dyadicCeilTime_sub_sq hσ T) hε

/-- **Optional stopping for the continuous Brownian Itô integral**: stopping `I` at a stopping time
`σ` yields an Itô integral of `H · 1_{[0, σ]}`, without path continuity of `W` or moment bounds. -/
theorem stoppedProcess (hW : IsFilteredPreBrownianReal ℱ W P)
    (hσ : IsStoppingTime ℱ σ) (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I σ) where
  isStronglyPredictable := (hI.locallyBrownianIntegrable.ite_le hσ).isStronglyPredictable
  ae_continuous := hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess
  exists_approx T := by
    let := (hW.hasLaw_eval 0).isProbabilityMeasure
    obtain ⟨n, τ₀, a, hτ₀, ha, henergy, -⟩ := hI.exists_approx T
    have hstep (k : ℕ) :=
      tendstoInMeasure_stoppedProcess_simpleGains_dyadicCeilTime (σ := σ) hW hI k hτ₀ ha henergy
    have hr (k : ℕ) : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.mpr (by simp [ENNReal.natCast_ne_top])
    choose m hm_hold hm_gain using fun k ↦
      (((henergy _ (hr k)).eventually (gt_mem_nhds (hr k))).and
        ((hstep k _ (hr k)).eventually (gt_mem_nhds (hr k)))).exists
    choose N γ c _ hγ hcm _ hhold hgains using fun k ↦
      Finance.exists_simpleHolding_simpleGains_dyadicCeilTime hσ k T (hτ₀ (m k)) (ha (m k))
    exact ⟨N, γ, c, fun k ↦ (hγ k).monotoneOn, hcm,
      tendsto_measure_lintegral_stoppedProcess_diag hI.locallyBrownianIntegrable hσ hcm hhold
        hm_hold,
      tendstoInMeasure_stoppedProcess_diag hW hσ hI hstep hτ₀ ha
        (fun k ω ↦ hgains k W le_rfl ω) hm_gain⟩

/-- Stopping an Itô integral `I` at `σ` is indistinguishable from any Itô integral `J` of
`H · 1_{[0, σ]}`, without assuming path continuity of `W`. -/
theorem stoppedProcess_indist (hW : IsFilteredPreBrownianReal ℱ W P)
    (hσ : IsStoppingTime ℱ σ) (hI : IsItoIntegral ℱ P W H I)
    (hJ : IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0) J) :
    MeasureTheory.stoppedProcess I σ ≡ᵐ[P] J :=
  isItoIntegral_unique hW (hI.stoppedProcess hW hσ) hJ

end

/-- **Stochastic-interval restriction for the continuous Brownian Itô integral**: for stopping
times `σ ≤ τ`, restricting `H` to `(σ, τ]` yields an Itô integral equal to
`stoppedProcess I τ - stoppedProcess I σ`, without path continuity of `W` or moment bounds. -/
theorem ite_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I τ - MeasureTheory.stoppedProcess I σ) := by
  rw [TauCeti.ite_Ioc_fun_eq_sub_ite_le hστ (fun t : ℝ≥0 ↦ (t : WithTop ℝ≥0)) H]
  exact (hI.stoppedProcess hW hτ).sub (hI.stoppedProcess hW hσ)

/-- **Adjacent stochastic-interval concatenation for Itô integrals.** For ordered random times
`σ ≤ τ ≤ ρ`, summing Itô integrals of the restrictions `1_{(σ, τ]} H` and `1_{(τ, ρ]} H` yields
an Itô integral of `1_{(σ, ρ]} H`. Neither stopping-time properties nor path continuity of `W` is
needed. -/
theorem ite_Ioc_add {σ τ ρ : Ω → WithTop ℝ≥0} (hστ : σ ≤ τ) (hτρ : τ ≤ ρ)
    {J₁ J₂ : ℝ≥0 → Ω → ℝ}
    (hJ₁ : IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J₁)
    (hJ₂ : IsItoIntegral ℱ P W
      (fun t ω ↦ if τ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0) J₂) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0)
      (fun t ω ↦ J₁ t ω + J₂ t ω) := by
  rw [TauCeti.ite_Ioc_fun_eq_add_ite_Ioc hστ hτρ]
  exact hJ₁.add hJ₂

end IsItoIntegral

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
  refine ⟨hG_meas, MeasureTheory.tendsto_measure_compl_of_ae_eventually_mem hG_meas ?_⟩
  filter_upwards [hτ, hHeq] with ω hτω hHω
  obtain ⟨m, hm⟩ := eventually_atTop.mp
    ((hτω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).and (hHω t))
  exact eventually_atTop.mpr ⟨m, fun j hj ↦ ⟨(hm j hj).1,
    (TauCeti.ae_eq_iff_lintegral_enorm_sub_sq_eq_zero
      (((hHseq_meas j).comp measurable_prodMk_right).eNorm.pow_const 2).aemeasurable).mp
      ((ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ (hm j hj).2 hs.2)⟩⟩

private theorem exists_simpleHolding_stage_approx
    {Hseq U : ℕ → ℝ≥0 → Ω → ℝ}
    (hU : ∀ n, IsItoIntegral ℱ P W (Hseq n) (U n)) {t : ℝ≥0}
    {G : ℕ → Set Ω} (hG_lim : Tendsto (fun m ↦ P (G m)ᶜ) atTop (𝓝 0)) (k : ℕ) :
    ∃ m n σ a,
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
    (hstop : ∀ n, MeasureTheory.stoppedProcess I (τ n) ≡ᵐ[P] U n)
    (hHeq : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, EqOn (Hseq n · ω) (H · ω) (Iic T)) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hH, hIcont, fun t ↦ ?_⟩
  have hdiff_meas (m : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ Hseq m p.1 p.2 - H p.1 p.2) :=
    (((hU m).isStronglyPredictable.sub hH).mono ℱ.predictable_le_prod).measurable
  let G (m : ℕ) : Set Ω := {ω | (t : WithTop ℝ≥0) < τ m ω} ∩
    {ω | ∫⁻ s, ‖Hseq m s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t = 0}
  obtain ⟨-, hG_lim⟩ := tendsto_measure_compl_goodEvent hτ_meas hdiff_meas hτ hHeq t
  choose m n σ a hσ ha hGm hEk hMk using exists_simpleHolding_stage_approx hU hG_lim
  have hinv : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_natCast_add_nhds_zero 1
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
    dsimp only [Set.mem_ofPred_eq] at hω ⊢
    exact hk.le.trans (hlint ▸ hω)
  · let N : Set Ω := {ω | ¬ ∀ j, MeasureTheory.stoppedProcess I (τ j) t ω = U j t ω}
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
          rwa [MeasureTheory.stoppedProcess_eq_of_le hGω.1.le] at h1
        dsimp only [Set.mem_ofPred_eq] at hω ⊢
        exact hk.le.trans (hIU ▸ hω)
      · exact Or.inr (Or.inl hGω)

/-- **Adjacent stochastic-interval concatenation for stopped Itô integrals.** For ordered random
times `σ ≤ τ ≤ ρ` where `σ` and `ρ` are stopping times, summing Itô integrals of `1_{(σ, τ]} H` and
`1_{(τ, ρ]} H` is indistinguishable from `stoppedProcess I ρ - stoppedProcess I σ`. -/
theorem IsFilteredPreBrownianReal.indist_ite_Ioc_add_stoppedProcess_sub
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {σ τ ρ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hρ : IsStoppingTime ℱ ρ)
    (hστ : σ ≤ τ) (hτρ : τ ≤ ρ) {J₁ J₂ : ℝ≥0 → Ω → ℝ}
    (hJ₁ : IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J₁)
    (hJ₂ : IsItoIntegral ℱ P W
      (fun t ω ↦ if τ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ ρ ω then H t ω else 0) J₂) :
    (fun t ω ↦ J₁ t ω + J₂ t ω) ≡ᵐ[P]
      fun t ω ↦ MeasureTheory.stoppedProcess I ρ t ω - MeasureTheory.stoppedProcess I σ t ω :=
  isItoIntegral_unique hW (hJ₁.ite_Ioc_add hστ hτρ hJ₂)
    (hI.ite_Ioc hW hσ hρ (hστ.trans hτρ))

end TauCeti.Probability
