/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.StochasticInterval
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Stopping compatibility of L² Brownian Itô integrals

Against an almost surely continuous filtered pre-Brownian motion `W`, stopping the Itô integral
process of a `BrownianIntegrable` integrand `H` at any stopping time `τ` on a raw filtration
agrees almost surely at every deterministic horizon `T` with `hW.l2Integral T` evaluated on the
cutoff integrand `1_{[0, τ]} · H` (`stoppedProcess_ae_eq_l2Integral`). Adjacent interval
integrals concatenate (`IsItoIntegral.add_Ioc_stopping`, `IsItoIntegral.add_Ioc`,
`IsItoIntegral.add_le_Ioc`, using `TauCeti.ite_le_eq_add_ite_Ioc`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–D.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- For a `BrownianIntegrable` integrand against an almost surely continuous filtered pre-Brownian
motion `W`, stopping its Itô integral at any stopping time `τ` agrees almost surely at every
horizon `T` with the L² Brownian integral of the cutoff integrand `1_{[0, τ]} · H`. -/
theorem stoppedProcess_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) :
    stoppedProcess I τ T =ᵐ[P]
      hW.l2Integral T (((hH.ite_le hτ).memLp_predictableMeasure T).toLp
        (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim, hunif⟩ :=
    hW.exists_seq_elementaryIntegrand_tendstoUniformlyOn hcont hH hI
  choose C hC using fun m ↦ (K m).exists_bound_positions
  -- Step 1: prove the identity for every dyadic approximation `σ k := dyadicCeilTime k ∘ τ`.
  have hdyad (k : ℕ) :
      stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T =ᵐ[P]
        hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T).toLp
          (Function.uncurry fun t ω ↦
            if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0)) := by
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
    have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime k
    choose N' p' ζ' C' hp' hζ' hC' hK'P hK'I using fun m ↦
      Finance.exists_simpleHolding_simpleGains_dyadicCeilTime
        ((K m).monotone_dates.monotoneOn _) (K m).measurable_positions
        (fun j _ ω ↦ hC m j ω) hτ k T
    have hlim_ae : TendstoInMeasure P (fun m ↦ Finance.simpleGains (p' m) (N' m) (ζ' m) W T)
        atTop (stoppedProcess I σ T) := tendstoInMeasure_of_tendsto_ae (fun m ↦
      ((Finance.stronglyAdapted_simpleGains (hp' m) (hζ' m) hW.adapted.stronglyAdapted T).mono
        (ℱ.le T)).aestronglyMeasurable) <| hunif.mono fun ω hω ↦ by
      simpa only [hK'I, stoppedProcess, ElementaryIntegrand.integral_eq_simpleGains] using
        (hω T).tendsto_at (Set.mem_Iic.mpr (WithTop.untopA_le (min_le_left _ _)))
    let Hσ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0
    have hlim_L2 : Tendsto (fun m ↦ eLpNorm (fun ω ↦
        Finance.simpleGains (p' m) (N' m) (ζ' m) W T ω -
        hW.l2Integral T (((hH.ite_le hσ).memLp_predictableMeasure T).toLp (Function.uncurry Hσ)) ω)
        2 P) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hKlim T) (fun _ ↦ zero_le)
        fun m ↦ by
          rw [hW.eLpNorm_simpleGains_sub_l2Integral (hp' m) (hζ' m)
            (fun j hj ↦ MemLp.of_bound ((hζ' m j hj).mono (ℱ.le _)).aestronglyMeasurable
              (C' m) (.of_forall (hC' m j hj))) T
            (hH.ite_le hσ).isStronglyPredictable ((hH.ite_le hσ).memLp_timeMeasure T)]
          refine eLpNorm_mono_ae ((((Finance.isStronglyPredictable_simpleHolding (hζ' m)).sub
            (hH.ite_le hσ).isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
            ?_
          filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
            ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2)] with ⟨u, ω⟩ hu
          dsimp only [Hσ]
          rw [hK'P m u hu ω, ← ElementaryIntegrand.toProcess_eq_simpleHolding]
          split_ifs <;> simp
    exact tendstoInMeasure_ae_unique hlim_ae
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hlim_L2)
  -- Step 2: let `k → ∞` using path continuity of `I` on the left and dominated convergence
  -- on the right.
  have hLHS : TendstoInMeasure P
      (fun k ↦ stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T) atTop (stoppedProcess I τ T) :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (Lp.aestronglyMeasurable _).congr (hdyad k).symm)
      (hI.ae_continuous.mono fun ω hω ↦
        tendsto_stoppedProcess_dyadicCeilTime I τ T ω hω.continuousAt.continuousWithinAt)
  have hRHS_eLp : Tendsto (fun k ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦
        (if (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2) then H p.1 p.2 else 0) -
        (if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0))
      2 ((timeMeasure T).prod P)) atTop (𝓝 0) := by
    rw [timeMeasure_def, ← NNReal.comap_volume_restrict_Ioc]
    refine hH.tendsto_eLpNorm_ite_le_sub_ite_le hτ.dyadicCeilTime τ (.of_forall fun ω t ↦ ?_) T
    by_cases ht : (t : WithTop ℝ≥0) ≤ τ ω
    · exact .of_forall fun k ↦ ⟨fun _ ↦ ht, fun _ ↦ ht.trans (le_dyadicCeilTime k (τ ω))⟩
    · exact ((tendsto_dyadicCeilTime (τ ω)).eventually
        (eventually_lt_nhds (lt_of_not_ge ht))).mono fun k hk ↦
        ⟨fun hle ↦ absurd hle hk.not_ge, fun hle ↦ absurd hle ht⟩
  exact tendstoInMeasure_ae_unique hLHS <| (tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
    (by norm_num) (hRHS_eLp.congr fun k ↦
      (hW.eLpNorm_l2Integral_sub T (hH.ite_le (hτ.dyadicCeilTime k)).isStronglyPredictable
        (hH.ite_le hτ).isStronglyPredictable
        ((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T)
        ((hH.ite_le hτ).memLp_predictableMeasure T)).symm)).congr_left fun k ↦ (hdyad k).symm

/-- **Concatenation of Itô integrals on adjacent stochastic intervals.** If `ρ ≤ σ ≤ τ`, the sum
of Itô integrals of `1_{(ρ, σ]} · H` and `1_{(σ, τ]} · H` is an Itô integral of
`1_{(ρ, τ]} · H`. -/
theorem _root_.TauCeti.Probability.IsItoIntegral.add_Ioc_stopping {ρ σ τ : Ω → WithTop ℝ≥0}
    (hρσ : ρ ≤ σ) (hστ : σ ≤ τ) {H I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hI₁ : IsItoIntegral ℱ P W
      (fun u ω ↦ if ρ ω < u ∧ (u : WithTop ℝ≥0) ≤ σ ω then H u ω else 0) I₁)
    (hI₂ : IsItoIntegral ℱ P W
      (fun u ω ↦ if σ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) I₂) :
    IsItoIntegral ℱ P W
      (fun u ω ↦ if ρ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) (I₁ + I₂) := by
  rw [TauCeti.ite_Ioc_eq_add_ite_Ioc hρσ hστ H]
  exact hI₁.add hI₂

/-- **Concatenation of Itô integrals on adjacent deterministic intervals.** If `r ≤ s ≤ t`, the
sum of Itô integrals of `1_{(r, s]} · H` and `1_{(s, t]} · H` is an Itô integral of
`1_{(r, t]} · H`. -/
theorem _root_.TauCeti.Probability.IsItoIntegral.add_Ioc {r s t : ℝ≥0} (hrs : r ≤ s)
    (hst : s ≤ t) {H I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hI₁ : IsItoIntegral ℱ P W (fun u ω ↦ if r < u ∧ u ≤ s then H u ω else 0) I₁)
    (hI₂ : IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then H u ω else 0) I₂) :
    IsItoIntegral ℱ P W (fun u ω ↦ if r < u ∧ u ≤ t then H u ω else 0) (I₁ + I₂) := by
  have hadd := IsItoIntegral.add_Ioc_stopping
    (fun _ ↦ WithTop.coe_le_coe.mpr hrs) (fun _ ↦ WithTop.coe_le_coe.mpr hst)
    (by simpa only [WithTop.coe_lt_coe, WithTop.coe_le_coe] using hI₁)
    (by simpa only [WithTop.coe_lt_coe, WithTop.coe_le_coe] using hI₂)
  simpa only [WithTop.coe_lt_coe, WithTop.coe_le_coe] using hadd

/-- **Concatenation of an initial-interval Itô integral and a subsequent interval integral.**
If `σ ≤ τ`, the sum of Itô integrals of `1_{[0, σ]} · H` and `1_{(σ, τ]} · H` is an Itô
integral of `1_{[0, τ]} · H`. -/
theorem _root_.TauCeti.Probability.IsItoIntegral.add_le_Ioc {σ τ : Ω → WithTop ℝ≥0} (hστ : σ ≤ τ)
    {H I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hI₁ : IsItoIntegral ℱ P W (fun u ω ↦ if (u : WithTop ℝ≥0) ≤ σ ω then H u ω else 0) I₁)
    (hI₂ : IsItoIntegral ℱ P W
      (fun u ω ↦ if σ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) I₂) :
    IsItoIntegral ℱ P W (fun u ω ↦ if (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) (I₁ + I₂) := by
  rw [TauCeti.ite_le_eq_add_ite_Ioc hστ H]
  exact hI₁.add hI₂

end TauCeti.Probability.IsFilteredPreBrownianReal
