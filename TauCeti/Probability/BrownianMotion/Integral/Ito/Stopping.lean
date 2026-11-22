/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Stopping compatibility of L² Brownian Itô integrals

Against an almost surely continuous filtered pre-Brownian motion `W`, stopping the Itô integral
process of a `BrownianIntegrable` integrand `H` at any stopping time `τ` on a raw filtration
produces an Itô integral of the cutoff integrand `1_{[0, τ]} · H`
(`isItoIntegral_stoppedProcess_of_brownianIntegrable`), and at every deterministic horizon `T` the
stopped integral agrees almost surely with `hW.l2Integral T` evaluated on `1_{[0, τ]} · H`
(`stoppedProcess_ae_eq_l2Integral`). Adjacent interval integrals concatenate
(`IsItoIntegral.add_Ioc_stopping`, `IsItoIntegral.add_Ioc`, `IsItoIntegral.add_le_Ioc`).

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
  obtain ⟨n, s, a, C, hs, ha, hb, hKlim, hunif⟩ :=
    hW.exists_seq_simpleHolding_tendstoUniformlyOn hcont hH hI
  -- Step 1: prove the identity for every dyadic approximation `σ k := dyadicCeilTime k ∘ τ`.
  have hdyad (k : ℕ) :
      stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T =ᵐ[P]
        hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T).toLp
          (Function.uncurry fun t ω ↦
            if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0)) := by
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
    have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime k
    choose N' p' ζ' C' hp' hζ' hC' hK'P hK'I using fun m ↦
      Finance.exists_simpleHolding_simpleGains_dyadicCeilTime (hs m) (ha m) (hb m) hτ k T
    have hlim_ae : TendstoInMeasure P (fun m ↦ Finance.simpleGains (p' m) (N' m) (ζ' m) W T)
        atTop (stoppedProcess I σ T) := tendstoInMeasure_of_tendsto_ae (fun m ↦
      ((Finance.stronglyAdapted_simpleGains (hp' m) (hζ' m) hW.adapted.stronglyAdapted T).mono
        (ℱ.le T)).aestronglyMeasurable) <| hunif.mono fun ω hω ↦ by
      simpa only [hK'I, stoppedProcess] using
        (hω T).tendsto_at (Set.mem_Iic.mpr (WithTop.untopA_le (min_le_left _ _)))
    let Hσ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0
    have hlim_L2 : Tendsto (fun m ↦ eLpNorm (fun ω ↦
        Finance.simpleGains (p' m) (N' m) (ζ' m) W T ω -
        hW.l2Integral T (((hH.ite_le hσ).memLp_predictableMeasure T).toLp (Function.uncurry Hσ)) ω)
        2 P) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hKlim T) (fun _ ↦ zero_le)
        fun m ↦ by
          rw [hW.eLpNorm_simpleGains_sub_l2Integral (hp' m) (hζ' m)
            (Finance.memLp_of_bound_stronglyMeasurable (hζ' m) (hC' m)) (hH.ite_le hσ) T]
          refine eLpNorm_mono_ae ((((Finance.isStronglyPredictable_simpleHolding (hζ' m)).sub
            (hH.ite_le hσ).isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
            ?_
          filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
            ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2)] with ⟨u, ω⟩ hu
          dsimp only [Hσ]; rw [hK'P m u hu ω]; split_ifs <;> simp
    exact tendstoInMeasure_ae_unique hlim_ae
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hlim_L2)
  -- Step 2: let `k → ∞` using path continuity of `I` on the left and dominated convergence
  -- on the right.
  let Hk (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0
  let Hτ (t : ℝ≥0) (ω : Ω) : ℝ := if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0
  have hLHS : TendstoInMeasure P
      (fun k ↦ stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T) atTop (stoppedProcess I τ T) :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (Lp.aestronglyMeasurable _).congr (hdyad k).symm)
      (hI.ae_continuous.mono fun ω hω ↦
        tendsto_stoppedProcess_dyadicCeilTime I τ T ω hω.continuousAt.continuousWithinAt)
  have hRHS_eLp : Tendsto (fun k ↦ eLpNorm
      (Function.uncurry (Hk k) - Function.uncurry Hτ) 2 ((timeMeasure T).prod P)) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (.of_forall fun k ↦
        ((hH.ite_le (hτ.dyadicCeilTime k)).memLp_timeMeasure T).aestronglyMeasurable)
      (hH.memLp_timeMeasure T)
      (.of_forall fun k ↦ .of_forall fun p ↦ by
        dsimp only [Hk, Hτ, Function.uncurry]; split_ifs <;> simp) (.of_forall fun p ↦ ?_)
    dsimp only [Hk, Hτ, Function.uncurry]
    by_cases hp : (p.1 : WithTop ℝ≥0) ≤ τ p.2
    · exact tendsto_const_nhds.congr fun k ↦ by
        simp only [hp, hp.trans (le_dyadicCeilTime k (τ p.2)), ite_true]
    · exact tendsto_const_nhds.congr' <|
        ((tendsto_dyadicCeilTime (τ p.2)).eventually (eventually_lt_nhds (lt_of_not_ge hp))).mono
          fun k hk ↦ by simp only [hp, not_le.mpr hk, ite_false]
  exact tendstoInMeasure_ae_unique hLHS <| (tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
    (by norm_num) (hRHS_eLp.congr fun k ↦
      (hW.eLpNorm_l2Integral_sub T (hH.ite_le (hτ.dyadicCeilTime k)).isStronglyPredictable
        (hH.ite_le hτ).isStronglyPredictable
        ((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T)
        ((hH.ite_le hτ).memLp_predictableMeasure T)).symm)).congr_left fun k ↦ (hdyad k).symm

/-- **Stopping compatibility for L² Brownian Itô integrals.** Against an almost surely continuous
filtered pre-Brownian motion `W`, stopping an Itô integral of a `BrownianIntegrable` integrand at
any stopping time `τ` produces an Itô integral of the cutoff integrand `1_{[0, τ]} · H`. No usual
filtration conditions are required. -/
theorem isItoIntegral_stoppedProcess_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (stoppedProcess I τ) := by
  obtain ⟨J, hJito, -, -⟩ := (hH.ite_le hτ).exists_isItoIntegral hW hcont
  exact hJito.congr (TauCeti.indist_of_ae_continuous
    (hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess) hJito.ae_continuous fun T ↦
      (hW.stoppedProcess_ae_eq_l2Integral hcont hH hI hτ T).trans
        (hW.ae_eq_l2Integral_of_isItoIntegral (hH.ite_le hτ) hJito T).symm).symm

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
  have hH_eq : (fun (u : ℝ≥0) ω ↦ if ρ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) =
      fun (u : ℝ≥0) ω ↦ (if ρ ω < u ∧ (u : WithTop ℝ≥0) ≤ σ ω then H u ω else 0) +
        (if σ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) := by
    ext u ω
    have hdisj : Disjoint (Set.Ioc (ρ ω) (σ ω)) (Set.Ioc (σ ω) (τ ω)) :=
      Set.Ioc_disjoint_Ioc_of_le le_rfl
    have hmem :=
      congr_fun (Set.indicator_union_of_disjoint hdisj (fun _ ↦ H u ω)) (u : WithTop ℝ≥0)
    rw [Set.Ioc_union_Ioc_eq_Ioc (hρσ ω) (hστ ω)] at hmem
    simpa only [Set.indicator_apply, Set.mem_Ioc] using hmem
  rw [hH_eq]
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
  have hH_eq : (fun (u : ℝ≥0) ω ↦ if (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) =
      fun (u : ℝ≥0) ω ↦ (if (u : WithTop ℝ≥0) ≤ σ ω then H u ω else 0) +
        (if σ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) := by
    ext u ω
    have hdisj : Disjoint (Set.Iic (σ ω)) (Set.Ioc (σ ω) (τ ω)) :=
      Set.Iic_disjoint_Ioc le_rfl
    have hmem :=
      congr_fun (Set.indicator_union_of_disjoint hdisj (fun _ ↦ H u ω)) (u : WithTop ℝ≥0)
    rw [Set.Iic_union_Ioc_eq_Iic (hστ ω)] at hmem
    simpa only [Set.indicator_apply, Set.mem_Iic, Set.mem_Ioc] using hmem
  rw [hH_eq]
  exact hI₁.add hI₂

end TauCeti.Probability.IsFilteredPreBrownianReal
