/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
import Mathlib.MeasureTheory.Integral.Indicator
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Patching

/-!
# Localization and the pathwise-energy Brownian Itô integral

For a predictable integrand `H` in `TauCeti.LocallyBrownianIntegrable ℱ P H`, this module extends
the continuous Brownian Itô integral beyond the expected square-energy domain by closed-level
energy localization on the raw filtration.

At each integer energy level `k + 1`, the finite-energy cutoff of `H` stopped at
`TauCeti.nnvolume.energyLocalizer H (k + 1)` belongs to `BrownianIntegrable ℱ P` and admits a
predictable continuous martingale Itô integral `U k`. Optional stopping on the `L²` domain makes
the stages `U k` compatible under stopping at earlier localizers, so
`TauCeti.exists_isStronglyProgressive_patch_stoppedProcess` patches them into a strongly
progressive, almost-surely continuous process `I` on the raw filtration without usual conditions.

## Main results

* `TauCeti.LocallyBrownianIntegrable.exists_isItoIntegral`: every `LocallyBrownianIntegrable`
  integrand against a filtered pre-Brownian motion with almost-surely continuous paths admits a
  strongly progressive continuous local-martingale Itô integral.
* `TauCeti.IsItoIntegral.locally_martingale`: every strongly progressive continuous Itô integral of
  a `LocallyBrownianIntegrable` integrand is a native local martingale.
* `TauCeti.IsItoIntegral.stoppedProcess_of_locallyBrownianIntegrable`,
  `TauCeti.IsItoIntegral.stoppedProcess_indist_of_locallyBrownianIntegrable`: optional stopping of
  continuous Itô integrals on the pathwise square-energy domain.

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

/-! ### Localization helpers -/

private def energyStage (H : ℝ≥0 → Ω → ℝ) (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω then
    nnvolume.finiteEnergyCutoff H t ω else 0

private theorem brownianIntegrable_simpleHolding [IsFiniteMeasure P]
    {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ} {C : ℝ}
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) :
    BrownianIntegrable ℱ P (Finance.simpleHolding τ n a) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  memLp T := by
    rw [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
    refine (memLp_const (n * C : ℝ)).mono'
      ((Finance.isStronglyPredictable_simpleHolding ha).mono
        ℱ.predictable_le_prod).aestronglyMeasurable (.of_forall fun p ↦ ?_)
    dsimp only [Function.uncurry]
    rw [Finance.simpleHolding_def]
    refine (norm_sum_le _ _).trans ?_
    calc
      (∑ j ∈ range n, ‖(Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1‖)
          ≤ ∑ j ∈ range n, ‖a j p.2‖ :=
        sum_le_sum fun j _ ↦ norm_indicator_le_norm_self _ _
      _ ≤ n * C := by
        simpa using sum_le_card_nsmul (range n) (fun j ↦ ‖a j p.2‖) C
          (fun j hj ↦ hb j (Finset.mem_range.mp hj) p.2)

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
  let Es (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖L k s ω - H_stage k s ω‖ₑ ^ 2 ∂Probability.timeMeasure T
  let E (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖L k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T
  have hEs_m (k : ℕ) : Measurable (Es k) :=
    ((((hL k).sub (hHs k)).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2)
      |>.lintegral_prod_left'
  have hE_m (k : ℕ) : Measurable (E k) :=
    ((((hL k).sub hH).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2)
      |>.lintegral_prod_left'
  let B (k : ℕ) : Set Ω := {ω | ε ≤ E k ω} \ {ω | ε ≤ Es k ω}
  have hBm (k : ℕ) : MeasurableSet (B k) :=
    (measurableSet_le measurable_const (hE_m k)).diff
      (measurableSet_le measurable_const (hEs_m k))
  have hB_lim : Tendsto (fun k ↦ P (B k)) atTop (𝓝 0) := by
    have hmem : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∈ B k ↔ ω ∈ (∅ : Set Ω) := by
      filter_upwards [heq] with ω hω
      filter_upwards [hω] with k hk
      have hEq : E k ω = Es k ω := lintegral_congr_ae
        ((Probability.ae_mem_Ioc_timeMeasure T).mono fun s hs ↦ by
          have hEqs : H_stage k s ω = H s ω := hk hs.2
          dsimp only
          rw [hEqs])
      simp [B, hEq]
    simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      atTop MeasurableSet.empty hBm hmem
  have hbound (k : ℕ) : P {ω | ε ≤ E k ω} ≤ P {ω | ε ≤ Es k ω} + P (B k) :=
    (measure_mono (fun _ hω ↦ by simp only [B, Set.mem_union, Set.mem_sdiff]; tauto)).trans
      (measure_union_le _ _)
  have hsum := (hstage ε hε).add hB_lim
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) hbound

private theorem tendstoInMeasure_of_stoppedProcess_ae_eq [IsFiniteMeasure P]
    {τ : ℕ → Ω → WithTop ℝ≥0} {U : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hτ_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤))
    (hUm : ∀ k, AEStronglyMeasurable (U k T) P)
    (hI_stop : ∀ k, MeasureTheory.stoppedProcess I (τ k) T =ᵐ[P] U k T) :
    TendstoInMeasure P (fun k ↦ U k T) atTop (I T) := by
  have hsm (k : ℕ) : AEStronglyMeasurable (MeasureTheory.stoppedProcess I (τ k) T) P :=
    (hUm k).congr (hI_stop k).symm
  have hs_ae : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ MeasureTheory.stoppedProcess I (τ k) T ω) atTop (𝓝 (I T ω)) := by
    filter_upwards [hτ_top] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hω T] with k hk
    exact (stoppedProcess_eq_of_le (τ := τ k) hk.le).symm
  exact (tendstoInMeasure_of_tendsto_ae hsm hs_ae).congr_left hI_stop

private theorem isItoIntegral_of_stopped_stages
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : IsStronglyPredictable ℱ H)
    (hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
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
    have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
    have hpos (k : ℕ) : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.mpr (by simp [ENNReal.natCast_ne_top])
    choose n γ a C _hγ0 hγ ha hb herr using fun k ↦
      ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P T (hHs k).isStronglyPredictable
        ((hHs k).memLp_timeMeasure T) (hpos k)
    have hinv : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hl2_hold : Tendsto (fun k ↦ eLpNorm
        (fun p ↦ (Finance.simpleHolding (γ k) (n k) (a k) - H_stage k) p.1 p.2 -
          (0 : ℝ≥0 → Ω → ℝ) p.1 p.2) 2 ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
        (fun _ ↦ zero_le) fun k ↦ by simpa only [Pi.zero_apply, sub_zero, Pi.sub_apply]
          using (herr k).le
    have hsub_bi (k : ℕ) :
        BrownianIntegrable ℱ P (Finance.simpleHolding (γ k) (n k) (a k) - H_stage k) := by
      simpa only [Pi.sub_def, neg_one_mul, ← sub_eq_add_neg] using
        (brownianIntegrable_simpleHolding (P := P) (ha k) (hb k)).add ((hHs k).const_mul (-1))
    have hl2_gain : Tendsto (fun k ↦ eLpNorm
        ((Finance.simpleGains (γ k) (n k) (a k) W T - U k T) - 0) 2 P) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
        (fun _ ↦ zero_le) fun k ↦ ?_
      rw [sub_zero]
      have hL_ito := IsItoIntegral.simpleHolding (W := W) hcont (hγ k).monotoneOn (ha k)
        (fun j hj ↦ ⟨C k, hb k j hj⟩)
      exact ((hL_ito.sub (hU k)).eLpNorm_eq hW (hsub_bi k) T).le.trans (herr k).le
    have hU_lim := tendstoInMeasure_of_stoppedProcess_ae_eq hτ_top
      (fun k ↦ ((hU k).memLp hW (hHs k) T).aestronglyMeasurable) (fun k ↦ hI_stop k T)
    refine ⟨n, γ, a, fun k ↦ (hγ k).monotoneOn, ha, fun k j hj ↦ ⟨C k, hb k j hj⟩, ?_, ?_⟩
    · refine tendsto_measure_lintegral_of_ae_eventually_eqOn
        (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k))
        (fun k ↦ (hHs k).isStronglyPredictable) hH (fun ε hε ↦ ?_)
        (heq.mono fun _ hω ↦ hω T)
      simpa only [Pi.zero_apply, sub_zero, Pi.sub_apply] using
        tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
          (fun k ↦ (hsub_bi k).isStronglyPredictable)
          (IsItoIntegral.zero (ℱ := ℱ) (P := P) (W := W)).isStronglyPredictable hl2_hold ε hε
    · have hsum := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hl2_gain).add hU_lim
      refine hsum.congr (fun k ↦ .of_forall fun _ ↦ sub_add_cancel _ _)
        (.of_forall fun _ ↦ zero_add _)

private theorem exists_patched_stages
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ (I : ℝ≥0 → Ω → ℝ) (U : ℕ → ℝ≥0 → Ω → ℝ),
      IsItoIntegral ℱ P W H I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun X ↦ Martingale X ℱ P) ℱ I P ∧
      (∀ k, IsItoIntegral ℱ P W (energyStage H k) (U k)) ∧
      ∀ k : ℕ, MeasureTheory.stoppedProcess I
        (nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)) ≡ᵐ[P] U k := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ (k : ℕ) := nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  have hτ_loc : IsLocalizingSequence ℱ τ P := hH.isLocalizingSequence_energyLocalizer
  have hHs (k : ℕ) : BrownianIntegrable ℱ P (energyStage H k) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((k : ℝ≥0) + 1)
  choose U hU_ito hU_pred hU_mart using fun k ↦ (hHs k).exists_isItoIntegral hW hcont
  have hcompat (k m : ℕ) (hkm : k ≤ m) : MeasureTheory.stoppedProcess (U m) (τ k) ≡ᵐ[P] U k := by
    have hcut : (fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ τ k ω then energyStage H m t ω else 0) =
        energyStage H k := by
      ext t ω
      dsimp only [energyStage, τ]
      have hmono : nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω ≤
          nnvolume.energyLocalizer H ((m : ℝ≥0) + 1) ω :=
        nnvolume.monotone_energyLocalizer H ω (add_le_add (Nat.cast_le.mpr hkm) le_rfl)
      by_cases hle : (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((k : ℝ≥0) + 1) ω
      · rw [ite_eq_left hle, ite_eq_left (hle.trans hmono), ite_eq_left hle]
      · rw [ite_eq_right hle, ite_eq_right hle]
    exact (hU_ito m).stoppedProcess_indist hW (hHs m) (hτ_loc.isStoppingTime k) (hcut ▸ hU_ito k)
  obtain ⟨I, hI_prog, hI_cont, hI_stop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hτ_loc.tendsto_top (fun k ↦ (hU_pred k).isStronglyProgressive)
    (fun k ↦ (hU_ito k).ae_continuous) hcompat
  have hI_ito : IsItoIntegral ℱ P W H I :=
    isItoIntegral_of_stopped_stages hW hcont hH.isStronglyPredictable hI_cont
      hτ_loc.tendsto_top hHs hU_ito (fun k T ↦ (hI_stop k).mono fun _ hω ↦ hω T)
      hH.ae_eventually_ite_le_energyLocalizer_eqOn
  have hI_loc : Locally (fun X ↦ Martingale X ℱ P) ℱ I P := by
    refine hI_prog.locally_martingale_of_ae_stopped_eq hτ_loc hU_mart fun k t ↦ ?_
    have hind : (fun s ↦ {ω | (⊥ : WithTop ℝ≥0) < τ k ω}.indicator (I s)) = I := by
      ext s ω
      have hpos : (⊥ : WithTop ℝ≥0) < τ k ω := by
        rw [← WithTop.coe_bot, NNReal.bot_eq_zero, WithTop.coe_zero]
        exact nnvolume.energyLocalizer_pos H (by positivity) ω
      exact indicator_of_mem hpos _
    rw [hind]
    exact (hI_stop k).symm.mono fun _ hω ↦ hω t
  exact ⟨I, U, hI_ito, hI_prog, hI_loc, hU_ito, hI_stop⟩

/-! ### Main theorems -/

/-- **Existence of the localized continuous Brownian Itô integral**: every
`LocallyBrownianIntegrable` integrand against a filtered pre-Brownian motion with almost-surely
continuous paths admits a strongly progressive continuous Itô integral that is a native local
martingale on the raw filtration. -/
theorem LocallyBrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun X ↦ Martingale X ℱ P) ℱ I P := by
  obtain ⟨I, -, hI_ito, hI_prog, hI_loc, -, -⟩ := exists_patched_stages hW hcont hH
  exact ⟨I, hI_ito, hI_prog, hI_loc⟩

namespace IsItoIntegral

/-- Every strongly progressive continuous Itô integral of a `LocallyBrownianIntegrable` integrand
against a filtered pre-Brownian motion with almost-surely continuous paths is a native local
martingale on the raw filtration. -/
theorem locally_martingale
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    (hprog : IsStronglyProgressive ℱ I) :
    Locally (fun X ↦ Martingale X ℱ P) ℱ I P := by
  obtain ⟨J, hJ_ito, -, hJ_loc⟩ := hH.exists_isItoIntegral hW hcont
  exact hprog.locally_martingale_of_indist hJ_loc (hJ_ito.indist hW hI)

/-- **Optional stopping for the localized continuous Brownian Itô integral**: stopping a continuous
Itô integral `I` of a `LocallyBrownianIntegrable` integrand `H` at any stopping time `σ` yields a
continuous Itô integral of the cutoff integrand `H · 1_{[0, σ]}`. -/
theorem stoppedProcess_of_locallyBrownianIntegrable
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ)
    (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I σ) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨J, U, hJ_ito, -, -, hU_ito, hJ_stop⟩ := exists_patched_stages hW hcont hH
  have hIJ : I ≡ᵐ[P] J := hI.indist hW hJ_ito
  let τ (k : ℕ) := nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  have hHs (k : ℕ) : BrownianIntegrable ℱ P (energyStage H k) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((k : ℝ≥0) + 1)
  refine isItoIntegral_of_stopped_stages hW hcont (hH.ite_le hσ).isStronglyPredictable
    (hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess)
    hH.isLocalizingSequence_energyLocalizer.tendsto_top
    (fun k ↦ (hHs k).ite_le hσ)
    (fun k ↦ (hU_ito k).stoppedProcess hW (hHs k) hσ)
    (fun k T ↦ ?_) ?_
  · have hcomm : MeasureTheory.stoppedProcess (MeasureTheory.stoppedProcess I σ) (τ k) =
        MeasureTheory.stoppedProcess (MeasureTheory.stoppedProcess I (τ k)) σ := by
      simp only [stoppedProcess_stoppedProcess, inf_comm]
    rw [hcomm]
    filter_upwards [hIJ, hJ_stop k] with ω hIJω hJω
    have h1 : MeasureTheory.stoppedProcess I (τ k) (min (T : WithTop ℝ≥0) (σ ω)).untopA ω =
        MeasureTheory.stoppedProcess J (τ k) (min (T : WithTop ℝ≥0) (σ ω)).untopA ω :=
      hIJω _
    exact h1.trans (hJω _)
  · filter_upwards [hH.ae_eventually_ite_le_energyLocalizer_eqOn] with ω hω T
    filter_upwards [hω T] with k hk t ht
    dsimp only
    by_cases hle : (t : WithTop ℝ≥0) ≤ σ ω
    · rw [ite_eq_left hle, ite_eq_left hle]
      exact hk ht
    · rw [ite_eq_right hle, ite_eq_right hle]

/-- Stopping a continuous Itô integral `I` of a `LocallyBrownianIntegrable` integrand `H` at a
stopping time `σ` gives a process indistinguishable from any continuous Itô integral `J` of
`H · 1_{[0, σ]}`. -/
theorem stoppedProcess_indist_of_locallyBrownianIntegrable
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ)
    (hI : IsItoIntegral ℱ P W H I)
    (hJ : IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0) J) :
    MeasureTheory.stoppedProcess I σ ≡ᵐ[P] J :=
  (hI.stoppedProcess_of_locallyBrownianIntegrable hW hcont hH hσ).indist hW hJ

end IsItoIntegral

end TauCeti
