/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Independence of an almost sure limit

Independence from a fixed sigma-algebra is preserved under almost sure sequential limits.
The bounded-continuous-test characterization makes this applicable without integrability
assumptions on the random variables. In particular, it allows increments of a continuous
process to remain independent after right-continuation of its filtration.
-/

public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction

namespace ProbabilityTheory

variable {Ω E : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [HasOuterApproxClosed E] {X : ℕ → Ω → E} {Y : Ω → E}

/-- An almost sure limit of random variables independent of a fixed sigma-algebra is
independent of that sigma-algebra. No moments of the random variables are required. -/
theorem indep_comap_of_ae_tendsto (hm : m ≤ mΩ)
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hind : ∀ n, Indep m (.comap (X n) inferInstance) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (nhds (Y ω))) :
    Indep m (.comap Y inferInstance) P := by
  refine indep_comap_of_bcf hm hY fun A hA f => ?_
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ω => f (X n ω)) P :=
    (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, ‖f (X n ω)‖ ≤ ‖f‖ :=
    Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => f (X n ω)) atTop (nhds (f (Y ω))) :=
    hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω
  have hall := tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    hmeas (integrable_const _) hbound hconv
  have hset := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (fun _ => ‖f‖) (fun n => (hmeas n).restrict) (integrable_const _)
    (fun n => ae_restrict_of_ae (hbound n)) (ae_restrict_of_ae hconv)
  have heq (n : ℕ) : ∫ ω in A, f (X n ω) ∂P =
      P.real A * ∫ ω, f (X n ω) ∂P :=
    (hind n).setIntegral_eq_mul hm (hX n) hA f.continuous.measurable.aestronglyMeasurable
  exact tendsto_nhds_unique hset ((tendsto_const_nhds.mul hall).congr fun n => (heq n).symm)

end ProbabilityTheory
