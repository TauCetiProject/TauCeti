/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Stopping the Brownian Itô integral process

This file proves stability of `TauCeti.Probability.IsItoIntegral` under stopping at raw-filtration
stopping times (`stoppedProcess`, `ite_Ioc`, `ite_le`, `ite_Ioc_mul`) and local congruence on
`[0, τ]` (`stoppedProcess_indist_of_ae_eq`), without assuming path continuity of `W`, adaptation
of `I`, or any `L²` construction of the integral.

Stopping is proved by dyadic upward approximation `dyadicCeilTime d ∘ τ`, representing stopped
simple holdings on the clipped grid `dyadicGrid d T` and passing to the sequential limit via
`TauCeti.Probability.IsItoIntegral.of_seq`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open Set hiding mem_range
open Finset hiding Iic mem_Iic min_zero
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

private theorem stoppedProcess_dyadicCeilTime
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : Probability.IsItoIntegral ℱ P W H I) (hτ : IsStoppingTime ℱ τ) (d : ℕ) :
    Probability.IsItoIntegral ℱ P W
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H t ω else 0)
      (stoppedProcess I (fun ω ↦ dyadicCeilTime d (τ ω))) := by
  refine ⟨hI.isStronglyPredictable.ite_le (hτ.dyadicCeilTime d),
    hI.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess, fun T ↦ ?_⟩
  obtain ⟨n, g, a, hg, ha, hE, _⟩ := hI.exists_approx T
  choose N r b _ hr hb _ hhold hgains using fun m ↦
    Finance.exists_simpleHolding_simpleGains_stoppedProcess_dyadicCeilTime hτ d T (hg m) (ha m)
  refine ⟨N, r, b, fun m ↦ (hr m).monotoneOn, hb, fun ε hε ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE ε hε) (fun _ ↦ zero_le)
      fun m ↦ measure_mono fun ω (hω : ε ≤ _) ↦ hω.trans <| lintegral_mono_ae <|
        (Probability.ae_mem_Ioc_timeMeasure T).mono fun s hs ↦ by
          rw [hhold m s hs.2 ω]; split_ifs <;> simp, fun ε hε ↦ ?_⟩
  let S : Finset ℝ≥0 := (range (dyadicCount d T + 1)).image (dyadicGrid d T)
  have hsum : Tendsto (fun m ↦ ∑ v ∈ S,
      P {ω | ε ≤ edist (Finance.simpleGains (g m) (n m) (a m) W v ω) (I v ω)}) atTop (𝓝 0) := by
    rw [← sum_const_zero (s := S)]
    exact tendsto_finsetSum S fun v hv ↦ let ⟨k, _, hk⟩ := mem_image.1 hv
      hk ▸ hI.tendstoInMeasure_simpleGains_of_le hW (dyadicGrid_le d T k) hg ha hE ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le) fun m ↦
    (measure_mono fun ω hω ↦ mem_biUnion
      (mem_image.2 ⟨dyadicStopIndex d T (τ ω),
        mem_range.2 (Nat.lt_succ_of_le (dyadicStopIndex_le d T (τ ω))), rfl⟩) <| by
          simpa only [mem_ofPred_eq, eval_dyadicGrid_dyadicStopIndex,
            hgains m W T le_rfl ω] using hω).trans (measure_biUnion_finset_le S _)

namespace Probability.IsItoIntegral

/-- **Stopping an Itô integral.** Against a filtered pre-Brownian motion, stopping an Itô integral
at a stopping time `τ` on the raw filtration yields an Itô integral of `H · 1_{[0, τ]}`. -/
theorem stoppedProcess (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I τ) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine of_seq (hI.isStronglyPredictable.ite_le hτ)
    (hI.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess) (stoppedProcess_dyadicCeilTime hW hI hτ)
    (fun T _ hε ↦ hI.locallyBrownianIntegrable.tendsto_measure_lintegral_dyadicCeilTime hτ T hε)
    fun T ↦ tendstoInMeasure_of_tendsto_ae
      (fun d ↦ (stoppedProcess_dyadicCeilTime hW hI hτ d).aestronglyMeasurable
        (fun _ ↦ hW.adapted.measurable.aestronglyMeasurable) T)
      (hI.ae_continuous.mono fun ω hω ↦
        tendsto_stoppedProcess_dyadicCeilTime I τ T ω hω.continuousAt.continuousWithinAt)

/-- **Restricting an Itô integral to `(σ, τ]`.** Against a filtered pre-Brownian motion, restricting
an integrand `H` to `(σ, τ]` yields `stoppedProcess I τ - stoppedProcess I (σ ⊓ τ)`. -/
theorem ite_Ioc {σ : Ω → WithTop ℝ≥0} (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I τ - MeasureTheory.stoppedProcess I (σ ⊓ τ)) := by
  convert (hI.stoppedProcess hW hτ).sub (hI.stoppedProcess hW (hσ.min hτ)) using 1
  ext t ω; simp only [Pi.sub_apply, le_inf_iff, ← not_le (a := (t : WithTop ℝ≥0))]
  split_ifs <;> simp_all

/-- **Concatenating Itô integrals at a stopping time.** Against a filtered pre-Brownian motion,
switching from integrand `H` on `[0, τ]` to `K` after a stopping time `τ` yields
`stoppedProcess I τ + J - stoppedProcess J τ`. -/
theorem ite_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else K t ω)
      (MeasureTheory.stoppedProcess I τ + J - MeasureTheory.stoppedProcess J τ) := by
  convert (hI.stoppedProcess hW hτ).add (hJ.sub (hJ.stoppedProcess hW hτ)) using 1
  · ext t ω; simp only [Pi.add_apply, Pi.sub_apply]; split_ifs <;> simp
  · ext t ω; dsimp only [Pi.add_apply, Pi.sub_apply]; ring

/-- **Predictable `ℱ s`-multiplier rule on `(s, τ]`.** Against a filtered pre-Brownian motion,
multiplying `H` on `(s, τ]` by an `ℱ s`-measurable `ξ` yields the Itô integral
`t ↦ ξ * (stoppedProcess I τ t - stoppedProcess I τ (min s t))`. -/
theorem ite_Ioc_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (s : ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if s < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then ξ ω * H t ω else 0)
      (fun t ω ↦ ξ ω * (MeasureTheory.stoppedProcess I τ t ω -
        MeasureTheory.stoppedProcess I τ (min s t) ω)) := by
  convert (hI.ite_lt_mul hW s hξ).stoppedProcess hW hτ using 1
  · ext t ω; split_ifs <;> simp_all
  · ext t ω; rw [← congr_fun₂ (MeasureTheory.stoppedProcess_const_min I τ s) t ω]
    simp only [MeasureTheory.stoppedProcess]

/-- **Local congruence of Itô integrals.** Against a filtered pre-Brownian motion and at a stopping
time `τ`, two Itô integrals whose integrands agree `(timeMeasure T).prod P`-almost everywhere on
`[0, τ]` for every finite horizon `T` have indistinguishable stopped processes. -/
theorem stoppedProcess_indist_of_ae_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (hτ : IsStoppingTime ℱ τ)
    (hHK : ∀ T : ℝ≥0, ∀ᵐ p ∂(timeMeasure T).prod P,
      (p.1 : WithTop ℝ≥0) ≤ τ p.2 → H p.1 p.2 = K p.1 p.2) :
    MeasureTheory.stoppedProcess I τ ≡ᵐ[P] MeasureTheory.stoppedProcess J τ :=
  (hI.stoppedProcess hW hτ).indist_of_ae_eq_prod hW (hJ.stoppedProcess hW hτ) fun T ↦
    (hHK T).mono fun _ hp ↦ by dsimp only [Function.uncurry]; split_ifs with h <;> [exact hp h; rfl]

end Probability.IsItoIntegral

end TauCeti
