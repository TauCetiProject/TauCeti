/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Continuous multipliers of locally Brownian-integrable processes

Finite pathwise square energy is preserved by multiplication by a predictable process whose
paths are bounded on compact time intervals. In particular, continuous predictable processes
can multiply Brownian integrands; a nonvanishing continuous process can also divide them.
These facts verify the diffusion-integrand domain for linear stochastic equations and their
inverse integrating factors without imposing moment bounds on the state or its initial value.

A predictable process with almost-surely continuous paths is itself locally Brownian-integrable.
For a merely adapted process with almost-surely continuous paths, we instead construct an
indistinguishable predictable process in that domain. No completeness or right continuity of
the filtration is assumed, so literal predictability is not asserted for the original version.
None of these results asserts finite expected square energy or constructs a stochastic integral.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H X : ℝ≥0 → Ω → ℝ}

/-- A predictable multiplier bounded on each compact time interval along almost every path
preserves finite pathwise square energy. The bound may depend on the path and the horizon;
no integrability of the bound is required. -/
theorem LocallyBrownianIntegrable.mul_of_locally_bounded
    (hH : LocallyBrownianIntegrable ℱ P H) (hX : IsStronglyPredictable ℱ X)
    (hb : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t ≤ T, ‖X t ω‖ ≤ C) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ H t ω * X t ω) := by
  refine ⟨hH.isStronglyPredictable.mul hX, ?_⟩
  -- Predictability is strong measurability of the uncurried process for ℱ.predictable.
  have hm : StronglyMeasurable (Function.uncurry X) :=
    hX.mono ℱ.predictable_le_prod
  filter_upwards [hH.ae_memLp, hb] with ω hω hbω
  intro T
  obtain ⟨C, hC⟩ := hbω T
  have hXm : StronglyMeasurable (fun t ↦ X t ω) := hm.comp_measurable measurable_prodMk_right
  refine (hω T).of_le_mul (c := C)
    ((hω T).aestronglyMeasurable.mul hXm.aestronglyMeasurable) ?_
  rw [NNReal.comap_volume_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  calc
    ‖H t ω * X t ω‖ = ‖H t ω‖ * ‖X t ω‖ := norm_mul _ _
    _ ≤ ‖H t ω‖ * C := mul_le_mul_of_nonneg_left (hC t ht.2) (norm_nonneg _)
    _ = C * ‖H t ω‖ := mul_comm _ _

/-- A predictable process with almost-surely continuous paths can multiply a locally
Brownian-integrable process, even when its compact-path bounds have no finite moments. -/
theorem LocallyBrownianIntegrable.mul_of_ae_continuous
    (hH : LocallyBrownianIntegrable ℱ P H) (hX : IsStronglyPredictable ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ H t ω * X t ω) := by
  apply hH.mul_of_locally_bounded hX
  filter_upwards [hc] with ω hω
  intro T
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hω.continuousOn (s := Icc 0 T))
  exact ⟨C, fun t ht ↦ hC t ⟨bot_le, ht⟩⟩

/-- A continuous, nonvanishing predictable process can divide a locally Brownian-integrable
process. Nonvanishing is required along whole paths outside one common null set, not merely
almost surely at each fixed time. -/
theorem LocallyBrownianIntegrable.div_of_ae_continuous
    (hH : LocallyBrownianIntegrable ℱ P H) (hX : IsStronglyPredictable ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hne : ∀ᵐ ω ∂P, ∀ t, X t ω ≠ 0) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ H t ω / X t ω) := by
  have hi : IsStronglyPredictable ℱ (fun t ω ↦ (X t ω)⁻¹) :=
    hX.inv₀
  have hic : ∀ᵐ ω ∂P, Continuous (fun t ↦ (X t ω)⁻¹) := by
    filter_upwards [hc, hne] with ω hω hnω
    exact hω.inv₀ hnω
  simpa only [div_eq_mul_inv] using hH.mul_of_ae_continuous hi hic

end TauCeti

namespace MeasureTheory.IsStronglyPredictable

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

/-- A predictable process with almost-surely continuous paths has finite pathwise square
energy on every finite horizon, without any moment assumption. -/
theorem locallyBrownianIntegrable_of_ae_continuous (hX : IsStronglyPredictable ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) :
    LocallyBrownianIntegrable ℱ P X := by
  have hone : LocallyBrownianIntegrable ℱ P (fun _ _ ↦ (1 : ℝ)) :=
    locallyBrownianIntegrable_const_iff.2 stronglyMeasurable_const
  simpa only [one_mul] using hone.mul_of_ae_continuous hX hc

end MeasureTheory.IsStronglyPredictable

namespace MeasureTheory.StronglyAdapted

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

/-- An adapted process with continuous paths belongs to the local Brownian integrand domain.
Continuity is pointwise here, so the original process is literally predictable. -/
theorem locallyBrownianIntegrable_of_continuous (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t ↦ X t ω)) : LocallyBrownianIntegrable ℱ P X :=
  (hX.isStronglyPredictable_of_continuous hc).locallyBrownianIntegrable_of_ae_continuous
    (.of_forall hc)

/-- An adapted process with almost-surely continuous paths has an indistinguishable locally
Brownian-integrable version on the same raw filtration. This does not impose any moment
condition or assert literal predictability of the original process. -/
theorem exists_locallyBrownianIntegrable_indist_of_ae_continuous (hX : StronglyAdapted ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, LocallyBrownianIntegrable ℱ P Y ∧ Y ≡ᵐ[P] X := by
  obtain ⟨Y, hY, heq⟩ := hX.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
    (hc.mono fun _ hω ↦ hω.isLeftContinuous)
  refine ⟨Y, hY.locallyBrownianIntegrable_of_ae_continuous ?_, heq⟩
  filter_upwards [hc, heq] with ω hω heqω
  exact hω.congr fun t ↦ (heqω t).symm

end MeasureTheory.StronglyAdapted
