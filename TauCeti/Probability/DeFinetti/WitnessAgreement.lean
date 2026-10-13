/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the statement compares these two canonical witnesses under a contractable path law.
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic
public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw
public import TauCeti.Probability.Process.PathLaw.InvariantConditionalLaw
-- Non-public: the default route's named witness theorem,
-- `conditionallyIIDWith_of_contractable_pathSpace`.
import TauCeti.Probability.DeFinetti.JointRectangle
-- Non-public: the Koopman route's named witness theorem,
-- `ContractableLaw.conditionallyIIDWith_invariantConditionalProbabilityMeasure`.
import TauCeti.Probability.DeFinetti.ViaKoopman.Theorem
-- Non-public: `conditionallyIID_ae_unique` identifies the two witnesses.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Unique

/-!
# Agreement of the canonical de Finetti witnesses

For the coordinate process on path space, two routes to de Finetti's theorem produce two canonical
directing measures. The default and `L²` routes use the tail-conditioned witness
`directingProbabilityMeasure`; the Koopman route uses `invariantConditionalProbabilityMeasure`,
which conditions on the shift-invariant σ-algebra instead. This file shows that, under a
contractable finite path law, the two random probability measures agree almost everywhere, so
results stated for one witness transfer to the other.

The underlying σ-algebras are not identified: the invariant and tail measurable spaces can differ,
already over `Bool` (`invariants_shift_lt_pathTail`). Nor are the witnesses equal pointwise. The
agreement is the a.e. uniqueness of directing measures, `conditionallyIID_ae_unique`.

## Main results

* `ContractableLaw.invariantConditionalProbabilityMeasure_ae_eq_directingProbabilityMeasure` — the
  Koopman and tail-conditioned witnesses of a contractable finite path law agree almost
  everywhere.

Exchangeable path laws are covered through `ExchangeableLaw.contractableLaw`. The `L²` witness
theorem `Contractable.conditionallyIIDWith_directingProbabilityMeasure` names the same
tail-conditioned witness, so it needs no separate comparison.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

/-- **The Koopman and tail-conditioned witnesses agree.** For a contractable finite path law on a
standard Borel state space, the conditional law of the first coordinate given the shift-invariant
σ-algebra agrees almost everywhere with the canonical tail-conditioned directing measure of the
coordinate process. -/
theorem ContractableLaw.invariantConditionalProbabilityMeasure_ae_eq_directingProbabilityMeasure
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : ContractableLaw ρ) :
    invariantConditionalProbabilityMeasure ρ =ᵐ[ρ]
      directingProbabilityMeasure ρ (fun n (x : ℕ → α) ↦ x n) := by
  -- Both are `ConditionallyIIDWith` witnesses for the coordinate process, whose path law is `ρ`.
  have hpath : pathLaw ρ (fun n (x : ℕ → α) => x n) = ρ := by simp [pathLaw_def]
  have hX : Contractable ρ fun n (x : ℕ → α) => x n :=
    contractable_of_contractableLaw_pathLaw (fun n => (measurable_pi_apply n).aemeasurable)
      (hpath.symm ▸ hρ)
  exact conditionallyIID_ae_unique hρ.conditionallyIIDWith_invariantConditionalProbabilityMeasure
    (conditionallyIIDWith_of_contractable_pathSpace hX)

end Probability

end TauCeti
