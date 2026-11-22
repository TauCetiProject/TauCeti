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
(`stoppedProcess_ae_eq_l2Integral`).

Interval differences `stoppedProcess I τ - stoppedProcess I σ` for `σ ≤ τ` (and deterministic
differences `u ↦ I (min u t) - I (min u s)` for `s ≤ t`) yield Itô integrals of the `(σ, τ]` and
`(s, t]` restrictions (`isItoIntegral_stoppedProcess_Ioc_of_brownianIntegrable`,
`isItoIntegral_stoppedProcess_sub_of_brownianIntegrable`), adjacent interval integrals concatenate
(`IsItoIntegral.add_Ioc`, `IsItoIntegral.add_Ioc_stopping`, `IsItoIntegral.add_le_Ioc`), and a
bounded `ℱ s`-measurable multiplier factors out of the `(s, t]` interval integral
(`isItoIntegral_ite_Ioc_mul_of_brownianIntegrable`,
`IsItoIntegral.mul_ite_Ioc_of_brownianIntegrable`).

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

/-- **Stochastic-interval restriction for L² Brownian Itô integrals.** For stopping times `σ ≤ τ`,
the difference `stoppedProcess I τ - stoppedProcess I σ` is an Itô integral of the `(σ, τ]`
restriction `1_{(σ, τ]} · H`. -/
theorem isItoIntegral_stoppedProcess_Ioc_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) :
    IsItoIntegral ℱ P W
      (fun u ω ↦ if σ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0)
      (stoppedProcess I τ - stoppedProcess I σ) := by
  have hH_eq : (fun (u : ℝ≥0) ω ↦ if σ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) =
      fun (u : ℝ≥0) ω ↦ (if (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) -
        (if (u : WithTop ℝ≥0) ≤ σ ω then H u ω else 0) := by
    ext u ω
    by_cases h1 : (u : WithTop ℝ≥0) ≤ σ ω <;> by_cases h2 : (u : WithTop ℝ≥0) ≤ τ ω
    · rw [ite_eq_right (fun h ↦ h1.not_gt h.1), ite_eq_left h2, ite_eq_left h1, sub_self]
    · exact absurd (h1.trans (hστ ω)) h2
    · rw [ite_eq_left ⟨lt_of_not_ge h1, h2⟩, ite_eq_left h2, ite_eq_right h1, sub_zero]
    · rw [ite_eq_right (fun h ↦ h2 h.2), ite_eq_right h2, ite_eq_right h1, sub_self]
  rw [hH_eq]
  exact (hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont hH hI hτ).sub
    (hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont hH hI hσ)

/-- **Deterministic-interval restriction for L² Brownian Itô integrals.** For `s ≤ t`, the
difference of stopped integrals `u ↦ I (min u t) - I (min u s)` is an Itô integral of the
`(s, t]` restriction `1_{(s, t]} · H`. -/
theorem isItoIntegral_stoppedProcess_sub_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {s t : ℝ≥0} (hst : s ≤ t) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then H u ω else 0)
      (fun u ω ↦ I (min u t) ω - I (min u s) ω) := by
  have hH_eq : (fun (u : ℝ≥0) ω ↦ if s < u ∧ u ≤ t then H u ω else 0) =
      fun (u : ℝ≥0) ω ↦ if (s : WithTop ℝ≥0) < u ∧ (u : WithTop ℝ≥0) ≤ t then H u ω else 0 := by
    ext u ω
    simp only [WithTop.coe_lt_coe, WithTop.coe_le_coe]
  rw [hH_eq]
  exact (hW.isItoIntegral_stoppedProcess_Ioc_of_brownianIntegrable hcont hH hI
    (isStoppingTime_const ℱ s) (isStoppingTime_const ℱ t)
    fun _ ↦ WithTop.coe_le_coe.mpr hst).congr (.of_forall fun ω u ↦ by
      simp only [Pi.sub_apply, stoppedProcess, ← WithTop.coe_min]
      rfl)

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
    by_cases h1 : ρ ω < u <;> by_cases h2 : (u : WithTop ℝ≥0) ≤ σ ω <;>
      by_cases h3 : (u : WithTop ℝ≥0) ≤ τ ω
    · rw [ite_eq_left ⟨h1, h3⟩, ite_eq_left ⟨h1, h2⟩,
        ite_eq_right (fun h ↦ h2.not_gt h.1), add_zero]
    · exact absurd (h2.trans (hστ ω)) h3
    · rw [ite_eq_left ⟨h1, h3⟩, ite_eq_right (fun h ↦ h2 h.2),
        ite_eq_left ⟨lt_of_not_ge h2, h3⟩, zero_add]
    · rw [ite_eq_right (fun h ↦ h3 h.2), ite_eq_right (fun h ↦ h2 h.2),
        ite_eq_right (fun h ↦ h3 h.2), add_zero]
    · have hns : ¬ σ ω < u := not_lt_of_ge ((le_of_not_gt h1).trans (hρσ ω))
      rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 h.1),
        ite_eq_right (fun h ↦ hns h.1), add_zero]
    · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 h.1),
        ite_eq_right (fun h ↦ h3 h.2), add_zero]
    · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 h.1),
        ite_eq_right (fun h ↦ ((le_of_not_gt h1).trans (hρσ ω)).not_gt h.1), add_zero]
    · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 h.1),
        ite_eq_right (fun h ↦ h3 h.2), add_zero]
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
    by_cases h1 : (u : WithTop ℝ≥0) ≤ σ ω <;> by_cases h2 : (u : WithTop ℝ≥0) ≤ τ ω
    · rw [ite_eq_left h2, ite_eq_left h1, ite_eq_right (fun h ↦ h1.not_gt h.1), add_zero]
    · exact absurd (h1.trans (hστ ω)) h2
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left ⟨lt_of_not_ge h1, h2⟩, zero_add]
    · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (fun h ↦ h2 h.2), add_zero]
  rw [hH_eq]
  exact hI₁.add hI₂

/-- Clipping a simple holding `(τ, n, a)` to `(s, t]` and multiplying by an `ℱ s`-measurable
function `ξ` yields another simple holding whose gains factor `ξ` out of the `(s, t]` difference
of gains. -/
private theorem simpleHolding_clip_Ioc_mul {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} {C : ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) {s t : ℝ≥0} (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ) :
    let σ (j : ℕ) : ℝ≥0 := min t (max s (τ j))
    let b (j : ℕ) (ω : Ω) : ℝ := if τ j ≤ t then ξ ω * a j ω else 0
    MonotoneOn σ (Set.Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (σ j)] (b j)) ∧
      (∀ j < n, ∀ ω, ‖b j ω‖ ≤ max Cξ 0 * max C 0) ∧
      (∀ u ω, Finance.simpleHolding σ n b u ω =
        if s < u ∧ u ≤ t then ξ ω * Finance.simpleHolding τ n a u ω else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω), Finance.simpleGains σ n b X T ω =
        ξ ω * (Finance.simpleGains τ n a X (min T t) ω -
          Finance.simpleGains τ n a X (min T s) ω) := by
  intro σ b
  have hσ : MonotoneOn σ (Set.Iic n) := fun i hi j hj hij ↦
    min_le_min_left t (max_le_max_left s (hτ hi hj hij))
  refine ⟨hσ, fun j hj ↦ ?_, fun j hj ω ↦ ?_, fun u ω ↦ ?_, fun X T ω ↦ ?_⟩
  · dsimp only [b]
    by_cases hjt : τ j ≤ t
    · simp only [hjt, ite_true]
      have hsσ : s ≤ σ j := le_min hst (le_max_left _ _)
      have hτσ : τ j ≤ σ j := le_min hjt (le_max_right _ _)
      exact (hξ.mono (ℱ.mono hsσ)).mul ((ha j hj).mono (ℱ.mono hτσ))
    · simp only [hjt, ite_false]
      exact stronglyMeasurable_zero
  · dsimp only [b]
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul ((hCξ ω).trans (le_max_left _ _)) ((hb j hj ω).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)
    · rw [norm_zero]
      exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
  · rw [Finance.simpleHolding_def, Finance.simpleHolding_def]
    split_ifs with hu
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj' : j < n := Finset.mem_range.mp hj
      by_cases hjt : τ j ≤ t
      · have hσj : σ j = max s (τ j) := min_eq_right (max_le hst hjt)
        have hiff : u ∈ Set.Ioc (σ j) (σ (j + 1)) ↔ u ∈ Set.Ioc (τ j) (τ (j + 1)) := by
          simp only [Set.mem_Ioc, σ, hσj, max_lt_iff, le_min_iff, le_max_iff, hu.1,
            hu.2, true_and, not_le.mpr hu.1, false_or]
        by_cases hmem : u ∈ Set.Ioc (τ j) (τ (j + 1))
        · simp [b, hjt, hiff.mpr hmem, hmem]
        · simp [hmem, mt hiff.mp hmem]
      · have htj : t < τ j := lt_of_not_ge hjt
        have htj1 : t < τ (j + 1) :=
          htj.trans_le (hτ (by simp; omega) (by simp; omega) (by omega))
        have hσj : σ j = t := min_eq_left (le_max_of_le_right htj.le)
        have hσj1 : σ (j + 1) = t := min_eq_left (le_max_of_le_right htj1.le)
        have hmem1 : u ∉ Set.Ioc (σ j) (σ (j + 1)) := by
          rw [hσj, hσj1, Set.Ioc_self]; exact Set.notMem_empty u
        have hmem2 : u ∉ Set.Ioc (τ j) (τ (j + 1)) := fun h ↦
          not_lt_of_ge (hu.2.trans htj.le) h.1
        simp [hmem1, hmem2]
    · refine Finset.sum_eq_zero fun j hj ↦ ?_
      have _hj' : j < n := Finset.mem_range.mp hj
      have hnot : u ∉ Set.Ioc (σ j) (σ (j + 1)) := fun h ↦
        hu ⟨(le_min hst (le_max_left _ _)).trans_lt h.1, h.2.trans (min_le_left _ _)⟩
      simp [hnot]
  · rw [Finance.simpleGains_def, Finance.simpleGains_def, Finance.simpleGains_def,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j < n := Finset.mem_range.mp hj
    have hτj : τ j ≤ τ (j + 1) := hτ (by simp; omega) (by simp; omega) (by omega)
    rcases le_total T s with hTs | hsT
    · have hsj : T ≤ σ j := hTs.trans (le_min hst (le_max_left _ _))
      have hsj1 : T ≤ σ (j + 1) := hTs.trans (le_min hst (le_max_left _ _))
      rw [min_eq_right hsj, min_eq_right hsj1, min_eq_left (hTs.trans hst), min_eq_left hTs,
        sub_self, mul_zero, sub_self, mul_zero]
    · by_cases hjt : τ j ≤ t
      · simp only [b, hjt, ite_true]
        have hσj_eq : min (σ j) T = max s (min (τ j) (min T t)) := by
          rw [show σ j = max s (τ j) from min_eq_right (max_le hst hjt), min_max_distrib_right,
            min_eq_left hsT]
          rcases le_total T t with hTt | htT
          · rw [min_eq_left hTt]
          · rw [min_eq_right htT, min_eq_left (hjt.trans htT), min_eq_left hjt]
        have hσj1_eq : min (σ (j + 1)) T = max s (min (τ (j + 1)) (min T t)) := by
          dsimp only [σ]
          rw [min_right_comm, min_comm t T, min_max_distrib_left, min_eq_right (le_min hsT hst),
            min_comm (min T t)]
        rw [hσj_eq, hσj1_eq, min_eq_right hsT]
        have hring :
            ξ ω * (a j ω * (X (min (τ (j + 1)) (min T t)) ω - X (min (τ j) (min T t)) ω) -
              a j ω * (X (min (τ (j + 1)) s) ω - X (min (τ j) s) ω)) =
            (ξ ω * a j ω) *
              ((X (min (τ (j + 1)) (min T t)) ω - X (min (τ j) (min T t)) ω) -
                (X (min (τ (j + 1)) s) ω - X (min (τ j) s) ω)) := by ring
        rw [hring]
        congr 1
        have hsu : s ≤ min T t := le_min hsT hst
        rcases le_total (τ j) s with hj_s | hs_j <;>
          rcases le_total (τ (j + 1)) s with hj1_s | hs_j1
        · simp [hj_s, hj1_s, hj_s.trans hsu, hj1_s.trans hsu]
        · rw [max_eq_right (le_min hs_j1 hsu), max_eq_left (min_le_of_left_le hj_s),
            min_eq_left (hj_s.trans hsu), min_eq_right hs_j1, min_eq_left hj_s]
          ring
        · have h1 : τ j = s := (hτj.trans hj1_s).antisymm hs_j
          have h2 : τ (j + 1) = s := hj1_s.antisymm (hs_j.trans hτj)
          simp [h1, h2, hsu]
        · rw [max_eq_right (le_min hs_j hsu), max_eq_right (le_min hs_j1 hsu),
            min_eq_right hs_j, min_eq_right hs_j1]
          ring
      · have htj : t < τ j := lt_of_not_ge hjt
        have htj1 : t < τ (j + 1) := htj.trans_le hτj
        simp only [b, hjt, ite_false, zero_mul]
        have h1 : min T t ≤ τ j := (min_le_right T t).trans htj.le
        have h2 : min T t ≤ τ (j + 1) := (min_le_right T t).trans htj1.le
        have h3 : min T s ≤ τ j := (min_le_right T s).trans (hst.trans htj.le)
        have h4 : min T s ≤ τ (j + 1) := (min_le_right T s).trans (hst.trans htj1.le)
        rw [min_eq_right h1, min_eq_right h2, min_eq_right h3, min_eq_right h4,
          sub_self, mul_zero, sub_self, mul_zero, sub_self, mul_zero]

/-- **Bounded left-measurable multiplier rule for `L²` interval integrals.** For `s ≤ t`, a
bounded `ℱ s`-measurable random variable `ξ` factors out of the `(s, t]` Itô integral:
`u ↦ ξ · (I (min u t) - I (min u s))` is an Itô integral of `1_{(s, t]} · ξ · H`. -/
theorem isItoIntegral_ite_Ioc_mul_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0)
      (fun u ω ↦ ξ ω * (I (min u t) ω - I (min u s) ω)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hξ_pred : IsStronglyPredictable ℱ (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0) := by
    change StronglyMeasurable[ℱ.predictable]
      (Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0)
    rw [show (Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0) =
        (fun p : ℝ≥0 × Ω ↦ (Set.Ioc s t).indicator (fun _ ↦ ξ p.2) p.1) from by
      ext ⟨u, ω⟩; simp [Set.indicator_apply]]
    exact ℱ.stronglyMeasurable_indicator_Ioc_predictable s t hξ
  have hpred : IsStronglyPredictable ℱ (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0) := by
    convert hξ_pred.mul hH.isStronglyPredictable using 2 with u ω
    split_ifs <;> simp
  have hcont_mul : ∀ᵐ ω ∂P, Continuous fun u ↦ ξ ω * (I (min u t) ω - I (min u s) ω) :=
    hI.ae_continuous.mono fun ω hω ↦ continuous_const.mul
      ((hω.comp (continuous_id.min continuous_const)).sub
        (hω.comp (continuous_id.min continuous_const)))
  refine ⟨hpred, hcont_mul, fun T ↦ ?_⟩
  obtain ⟨n, τ, a, C, hτ, ha, hb, hKlim, hunif⟩ :=
    hW.exists_seq_simpleHolding_tendstoUniformlyOn hcont hH hI
  choose hσ hb_meas _ hb_hold hb_gain using fun k ↦
    simpleHolding_clip_Ioc_mul (hτ k) (ha k) (hb k) hst hξ hCξ
  let σ (k j : ℕ) : ℝ≥0 := min t (max s (τ k j))
  let b (k j : ℕ) (ω : Ω) : ℝ := if τ k j ≤ t then ξ ω * a k j ω else 0
  have hL2 : Tendsto (fun k ↦ eLpNorm
      (Function.uncurry (Finance.simpleHolding (σ k) (n k) (b k)) -
        Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0) 2
      ((timeMeasure T).prod P)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun k ↦ ENNReal.ofReal (max Cξ 0) * eLpNorm
        (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P)) atTop (𝓝 (ENNReal.ofReal (max Cξ 0) * 0)) :=
      ENNReal.Tendsto.const_mul (hKlim T) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hconst
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconst (fun _ ↦ zero_le)
      fun k ↦ ?_
    have hfm : AEStronglyMeasurable
        (Function.uncurry (Finance.simpleHolding (σ k) (n k) (b k)) -
          Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0)
        ((timeMeasure T).prod P) :=
      (((Finance.isStronglyPredictable_simpleHolding (hb_meas k)).sub hpred).mono
        ℱ.predictable_le_prod).aestronglyMeasurable
    calc eLpNorm (Function.uncurry (Finance.simpleHolding (σ k) (n k) (b k)) -
          Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0) 2
          ((timeMeasure T).prod P)
        ≤ eLpNorm (max Cξ 0 •
            (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)) 2
            ((timeMeasure T).prod P) := by
          refine eLpNorm_mono_eNorm hfm fun ⟨u, ω⟩ ↦ ?_
          dsimp only [σ, b]
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.uncurry_apply_pair,
            hb_hold k u ω, eNorm_mul, Real.eNorm_eq_ofReal_abs, abs_of_nonneg (le_max_right Cξ 0)]
          split_ifs
          · rw [← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
            exact mul_le_mul_of_nonneg_right
              (ENNReal.ofReal_le_ofReal ((hCξ ω).trans (le_max_left _ _))) (by positivity)
          · simp only [sub_self, abs_zero, ENNReal.ofReal_zero, zero_le]
      _ = ENNReal.ofReal (max Cξ 0) * eLpNorm
            (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2
            ((timeMeasure T).prod P) := by
          rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal_abs, abs_of_nonneg (le_max_right Cξ 0)]
  refine ⟨n, σ, b, hσ, hb_meas,
    tendsto_measure_le_lintegral_enorm_sq_sub
      (fun k ↦ Finance.isStronglyPredictable_simpleHolding (hb_meas k)) (fun _ ↦ hpred) hL2,
    tendstoInMeasure_of_tendsto_ae (fun k ↦
      ((Finance.stronglyAdapted_simpleGains (hσ k) (hb_meas k)
        hW.adapted.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable)
      (hunif.mono fun ω hω ↦ ?_)⟩
  have h1 := (hω (max (min T t) (min T s))).tendsto_at
    (Set.mem_Iic.mpr (le_max_left _ _))
  have h2 := (hω (max (min T t) (min T s))).tendsto_at
    (Set.mem_Iic.mpr (le_max_right _ _))
  dsimp only [σ, b]
  simpa only [fun k ↦ hb_gain k W T ω] using (tendsto_const_nhds (x := ξ ω)).mul (h1.sub h2)

/-- **Bounded left-measurable multiplier rule for `L²` interval integrals** stated directly for
any Itô integral `J` of the `(s, t]` cutoff `1_{(s, t]} · H`. -/
theorem _root_.TauCeti.Probability.IsItoIntegral.mul_ite_Ioc_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H J : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) {s t : ℝ≥0} (hst : s ≤ t)
    (hJ : IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then H u ω else 0) J)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0)
      (fun u ω ↦ ξ ω * J u ω) := by
  obtain ⟨I, hI, -, -⟩ := hH.exists_isItoIntegral hW hcont
  have hI_sub := hW.isItoIntegral_stoppedProcess_sub_of_brownianIntegrable hcont hH hI hst
  have hmul := hW.isItoIntegral_ite_Ioc_mul_of_brownianIntegrable hcont hH hI hst hξ hCξ
  exact hmul.congr ((isItoIntegral_unique hW hI_sub hJ).mono fun ω hω u ↦ by
    simp only [hω u])

end TauCeti.Probability.IsFilteredPreBrownianReal
