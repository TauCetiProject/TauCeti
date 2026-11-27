/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
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
`H · 1_{(σ, τ]}` (`TauCeti.Probability.IsItoIntegral.ite_Ioc`).

## Main results

* `TauCeti.Probability.IsItoIntegral.stoppedProcess`,
  `TauCeti.Probability.IsItoIntegral.stoppedProcess_indist`: stopping a continuous Itô integral at a
  stopping time `σ` integrates `H · 1_{[0, σ]}`.
* `TauCeti.Probability.IsItoIntegral.ite_Ioc`: restricting an integrand to `(σ, τ]` for stopping
  times `σ ≤ τ` integrates to `stoppedProcess I τ - stoppedProcess I σ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsItoIntegral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H I J : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0}

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
  have hstop (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
      MeasureTheory.stoppedProcess X (fun ω ↦ dyadicCeilTime k (σ ω)) T ω =
        X (min (T : WithTop ℝ≥0) (dyadicCeilTime k (σ ω))).untopA ω := by
    unfold MeasureTheory.stoppedProcess; rfl
  exact fun ε hε ↦ tendsto_measure_of_subset_biUnion_finset S (fun s hs ↦ hgains_s hs ε hε)
    fun m ω hω ↦ by
      let s := (min (T : WithTop ℝ≥0) (dyadicCeilTime k (σ ω))).untopA
      have hs : s ∈ S := hrange ω
      dsimp only at hω
      rw [Set.mem_ofPred_eq, hstop _ ω, hstop _ ω] at hω
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

/-- **Stochastic-interval restriction for the continuous Brownian Itô integral**: for stopping
times `σ ≤ τ`, restricting `H` to `(σ, τ]` yields an Itô integral equal to
`stoppedProcess I τ - stoppedProcess I σ`, without path continuity of `W` or moment bounds. -/
theorem ite_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I τ - MeasureTheory.stoppedProcess I σ) := by
  have heq : (fun (t : ℝ≥0) ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) =
      fun (t : ℝ≥0) ω ↦ (if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) -
        if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0 := by
    ext t ω
    have hle := hστ ω
    split_ifs <;> simp_all <;> grind
  rw [heq]
  exact (hI.stoppedProcess hW hτ).sub (hI.stoppedProcess hW hσ)

end TauCeti.Probability.IsItoIntegral
