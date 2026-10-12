/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.ExchangeableSigma
public import TauCeti.Probability.DeFinetti.ViaKoopman.Theorem
public import TauCeti.Probability.DeFinetti.ViaL2.ConditionallyIID
-- Non-public: the generic comparison of conditional expectations on σ-algebras that agree up to
-- null sets is used only inside proofs.
import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# The exchangeable, tail and shift-invariant σ-algebras agree up to null sets

On path space the shift-invariant, tail and exchangeable σ-algebras form a strictly increasing chain

`invariants (shift α) < pathTail α < exchangeableSigma α`

(`invariants_shift_lt_pathTail`, `pathTail_lt_exchangeableSigma`). Under a contractable — in
particular an exchangeable — law the chain collapses modulo null sets: every exchangeable event
agrees almost everywhere with a shift-invariant event, hence with a tail event.

This is a consequence of de Finetti's theorem. A contractable law is conditionally i.i.d. with a
directing measure that is measurable for the shift-invariant σ-algebra (the Koopman witness
`invariantConditionalProbabilityMeasure`), and for the process-level tail σ-algebra (the
tail witness `directingProbabilityMeasure`). Since exchangeable events of a conditionally i.i.d.
process are events of its directing measure up to null sets
(`ConditionallyIIDWith.exists_measurableSet_ae_eq`), they are invariant, respectively tail, events
up to null sets.

Consequently conditioning on any of the three σ-algebras gives the same result almost everywhere:
under a contractable law, conditional expectations given the exchangeable σ-algebra can be computed
from the tail or from the shift-invariant σ-algebra, and conversely.

## Main results

* `TauCeti.Probability.Contractable.exists_measurableSet_tailProcess_ae_eq` — for a contractable
  process `X`, the event that the path of `X` lies in an exchangeable set agrees almost everywhere
  with an event of `tailProcess X`.
* `TauCeti.Probability.ContractableLaw.exists_measurableSet_invariants_ae_eq` — under a contractable
  path law, every exchangeable event agrees almost everywhere with a shift-invariant event.
* `TauCeti.Probability.ContractableLaw.exists_measurableSet_pathTail_ae_eq` — the same with a tail
  event.
* `TauCeti.Probability.ContractableLaw.condExp_exchangeableSigma_ae_eq_invariants`,
  `TauCeti.Probability.ContractableLaw.condExp_exchangeableSigma_ae_eq_pathTail`,
  `TauCeti.Probability.ContractableLaw.condExp_pathTail_ae_eq_invariants` — under a contractable
  path law, conditional expectations given the exchangeable, tail and shift-invariant σ-algebras
  agree almost everywhere.

Exchangeable processes and laws are covered through `Exchangeable.contractable` and
`ExchangeableLaw.contractableLaw`.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1,
  where the directing measure, the tail σ-field and the exchangeable σ-field are shown to agree
  almost surely.

No material is adapted from `cameronfreer/exchangeability`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [StandardBorelSpace α]

/-- **Exchangeable events of a contractable process are tail events up to null sets.** For a
contractable process `X` with measurable coordinates in a standard Borel space, the event that the
path of `X` lies in an exchangeable set agrees almost everywhere with an event of the tail
σ-algebra `tailProcess X`. -/
theorem Contractable.exists_measurableSet_tailProcess_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {s : Set (ℕ → α)} (hs : MeasurableSet[exchangeableSigma α] s) :
    ∃ t : Set Ω, MeasurableSet[tailProcess X] t ∧ (fun ω i => X i ω) ⁻¹' s =ᵐ[μ] t := by
  rcases isEmpty_or_nonempty α with _ | _
  · -- With an empty state space there are no sample points, so every event is empty.
    have : IsEmpty Ω := (X 0).isEmpty
    exact ⟨∅, (tailProcess X).measurableSet_empty, by simp [Set.eq_empty_of_isEmpty]⟩
  · exact (hX.conditionallyIIDWith_directingProbabilityMeasure hX_meas).exists_measurableSet_ae_eq
      measurable_tailProcess_directingProbabilityMeasure hs

/-- **Exchangeable events are shift-invariant events up to null sets.** Under a contractable law
`ρ` on paths in a standard Borel space, every exchangeable event agrees `ρ`-almost everywhere with
an event of the shift-invariant σ-algebra. -/
theorem ContractableLaw.exists_measurableSet_invariants_ae_eq {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ) {s : Set (ℕ → α)}
    (hs : MeasurableSet[exchangeableSigma α] s) :
    ∃ t : Set (ℕ → α), MeasurableSet[MeasurableSpace.invariants (shift α)] t ∧ s =ᵐ[ρ] t := by
  rcases isEmpty_or_nonempty α with _ | _
  · -- With an empty state space there are no paths, so every event is empty.
    exact ⟨∅, (MeasurableSpace.invariants (shift α)).measurableSet_empty,
      by simp [Set.eq_empty_of_isEmpty]⟩
  · exact hρ.conditionallyIIDWith_invariantConditionalProbabilityMeasure.exists_measurableSet_ae_eq
      measurable_invariants_invariantConditionalProbabilityMeasure hs

/-- **Exchangeable events are tail events up to null sets.** Under a contractable law `ρ` on paths
in a standard Borel space, every exchangeable event agrees `ρ`-almost everywhere with a tail
event. -/
theorem ContractableLaw.exists_measurableSet_pathTail_ae_eq {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ) {s : Set (ℕ → α)}
    (hs : MeasurableSet[exchangeableSigma α] s) :
    ∃ t : Set (ℕ → α), MeasurableSet[pathTail α] t ∧ s =ᵐ[ρ] t :=
  let ⟨t, ht, hst⟩ := hρ.exists_measurableSet_invariants_ae_eq hs
  ⟨t, invariants_shift_le_pathTail t ht, hst⟩

section CondExp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]

/-- **Conditioning on exchangeable events is conditioning on shift-invariant events.** Under a
contractable law `ρ` on paths in a standard Borel space, the conditional expectation of any
observable given the exchangeable σ-algebra agrees `ρ`-almost everywhere with its conditional
expectation given the shift-invariant σ-algebra. -/
theorem ContractableLaw.condExp_exchangeableSigma_ae_eq_invariants (hρ : ContractableLaw ρ)
    (f : (ℕ → α) → E) :
    ρ[f | exchangeableSigma α] =ᵐ[ρ] ρ[f | MeasurableSpace.invariants (shift α)] :=
  TauCeti.MeasureTheory.condExp_ae_eq_of_forall_exists_ae_eq
    invariants_shift_le_exchangeableSigma exchangeableSigma_le
    fun _ hs => hρ.exists_measurableSet_invariants_ae_eq hs

/-- **Conditioning on exchangeable events is conditioning on tail events.** Under a contractable
law `ρ` on paths in a standard Borel space, the conditional expectation of any observable given the
exchangeable σ-algebra agrees `ρ`-almost everywhere with its conditional expectation given the
tail σ-algebra. -/
theorem ContractableLaw.condExp_exchangeableSigma_ae_eq_pathTail (hρ : ContractableLaw ρ)
    (f : (ℕ → α) → E) :
    ρ[f | exchangeableSigma α] =ᵐ[ρ] ρ[f | pathTail α] :=
  TauCeti.MeasureTheory.condExp_ae_eq_of_forall_exists_ae_eq
    pathTail_le_exchangeableSigma exchangeableSigma_le
    fun _ hs => hρ.exists_measurableSet_pathTail_ae_eq hs

/-- **Conditioning on tail events is conditioning on shift-invariant events.** Under a contractable
law `ρ` on paths in a standard Borel space, the conditional expectation of any observable given the
tail σ-algebra agrees `ρ`-almost everywhere with its conditional expectation given the
shift-invariant σ-algebra. -/
theorem ContractableLaw.condExp_pathTail_ae_eq_invariants (hρ : ContractableLaw ρ)
    (f : (ℕ → α) → E) :
    ρ[f | pathTail α] =ᵐ[ρ] ρ[f | MeasurableSpace.invariants (shift α)] :=
  TauCeti.MeasureTheory.condExp_ae_eq_of_le_of_le invariants_shift_le_pathTail
    pathTail_le_exchangeableSigma exchangeableSigma_le
    (hρ.condExp_exchangeableSigma_ae_eq_invariants f)

end CondExp

end Probability

end TauCeti
