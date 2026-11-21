/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.StochasticInterval
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Stopping Brownian integrands

The predictable-set restriction lemmas for the expected and pathwise square-energy domains
specialize to `[0,τ]` and `(σ,τ]` for stopping times on a raw filtration. These are
cutoff integrands, zero after the stopping time, not stopped processes retaining their last
value. Neither completeness nor right continuity of the filtration is required.

Along stopping times tending almost surely to infinity, the cutoffs recover an integrand in
expected square-energy norm on every finite horizon. These facts allow approximation and
localization of stochastic-integral inputs. The pathwise-domain closure results impose no
moment assumptions. No stochastic integral is constructed here.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0}

/-- Killing an integrand after a stopping time preserves finite expected square energy.
The value at the stopping time is retained. -/
theorem BrownianIntegrable.ite_le (hH : BrownianIntegrable ℱ P H)
    (hτ : IsStoppingTime ℱ τ) :
    BrownianIntegrable ℱ P (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator hτ.measurableSet_predictable_ge

/-- Killing an integrand after a stopping time preserves finite pathwise square energy.
The value at the stopping time is retained. -/
theorem LocallyBrownianIntegrable.ite_le (hH : LocallyBrownianIntegrable ℱ P H)
    (hτ : IsStoppingTime ℱ τ) :
    LocallyBrownianIntegrable ℱ P
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator hτ.measurableSet_predictable_ge

/-- Restriction to `(σ,τ]` preserves finite expected square energy. No ordering of the
stopping times is required. -/
theorem BrownianIntegrable.ite_Ioc (hH : BrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    BrownianIntegrable ℱ P
      (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator (hσ.measurableSet_predictable_Ioc hτ)

/-- Restriction to `(σ,τ]` preserves finite pathwise square energy. No ordering of the
stopping times is required. -/
theorem LocallyBrownianIntegrable.ite_Ioc (hH : LocallyBrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    LocallyBrownianIntegrable ℱ P
      (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator (hσ.measurableSet_predictable_Ioc hτ)

/-- Cutoffs along stopping times tending almost surely to infinity converge on each finite
horizon in expected square-energy norm. Monotonicity of the times is unnecessary. -/
theorem BrownianIntegrable.tendsto_eLpNorm_ite_le_sub
    (hH : BrownianIntegrable ℱ P H) {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime ℱ (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)) (T : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ (if (p.1 : WithTop ℝ≥0) ≤ τ n p.2 then H p.1 p.2 else 0) -
        H p.1 p.2) 2
      (((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P))
      atTop (𝓝 0) := by
  apply tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
    (Eventually.of_forall fun n ↦ ((hH.ite_le (hτ n)).memLp T).aestronglyMeasurable)
    (hH.memLp T)
  · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun p ↦ by
      dsimp only [Function.uncurry]
      split_ifs <;> simp
  · have hprod := (Measure.quasiMeasurePreserving_snd
        (μ := (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ))
        (ν := P)).ae hlim
    filter_upwards [hprod] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [hp.eventually (eventually_gt_nhds (WithTop.coe_lt_top p.1))] with n hn
    exact (ite_eq_left hn.le).symm

end TauCeti
