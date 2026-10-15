/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.ExchangeableSigma.Basic
public import TauCeti.Probability.Process.Tail.Comap
-- Non-public: the generic comparison of conditional expectations is used only in proofs.
import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# Process tails and pullbacks of the exchangeable σ-algebra

The tail σ-algebra of a process is contained in the pullback of the exchangeable σ-algebra
along its path map. For a contractable process under a finite measure, with measurable
coordinates in a standard Borel state space, these σ-algebras agree modulo ambient null sets.
Their conditional expectations therefore agree almost everywhere for every Banach-valued
observable on the original sample space.

The equality uses Mathlib's `eventuallyMeasurableSpace` to adjoin the same ambient null sets
to both σ-algebras. It does not assert equality of the unaugmented σ-algebras or of the
separate completions of their trimmed measures. Exchangeable processes are covered through
`Exchangeable.contractable`.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, for the almost-sure agreement of the tail and exchangeable σ-fields.

The event representatives come from `ExchangeableSigma.Basic`, and the exact tail pullback
identity comes from `Process.Tail.Comap`. No formalization is copied or vendored here.
-/

public section

noncomputable section

open MeasureTheory Filter

namespace TauCeti.Probability

variable {Ω α : Type*} [MeasurableSpace α]

/-- The tail σ-algebra of any process is contained in the pullback of the exchangeable
σ-algebra along its path map. No measurability or distributional assumptions are needed. -/
theorem tailProcess_le_comap_exchangeableSigma (X : ℕ → Ω → α) :
    tailProcess X ≤ MeasurableSpace.comap (fun ω i => X i ω) (exchangeableSigma α) := by
  rw [tailProcess_eq_comap_pathTail]
  exact MeasurableSpace.comap_mono pathTail_le_exchangeableSigma

variable [MeasurableSpace Ω] [StandardBorelSpace α]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}

/-- Under a finite measure, every event in the pullback exchangeable σ-algebra of a
contractable process agrees almost everywhere with an event in its tail σ-algebra. -/
theorem Contractable.exists_measurableSet_tailProcess_ae_eq_of_comap_exchangeableSigma
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {s : Set Ω}
    (hs : MeasurableSet[MeasurableSpace.comap (fun ω i => X i ω) (exchangeableSigma α)] s) :
    ∃ t : Set Ω, MeasurableSet[tailProcess X] t ∧ s =ᵐ[μ] t := by
  obtain ⟨u, hu, rfl⟩ := hs
  exact hX.exists_measurableSet_tailProcess_ae_eq hX_meas hu

/-- The pullback exchangeable σ-algebra and the process tail become equal after adjoining
all ambient `μ`-null sets, for a contractable process with measurable coordinates under a
finite measure. -/
theorem Contractable.eventuallyMeasurableSpace_comap_exchangeableSigma_eq_tailProcess
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    eventuallyMeasurableSpace
        (MeasurableSpace.comap (fun ω i => X i ω) (exchangeableSigma α)) (ae μ) =
      eventuallyMeasurableSpace (tailProcess X) (ae μ) := by
  apply le_antisymm
  · rintro s ⟨t, ht, hst⟩
    obtain ⟨u, hu, htu⟩ :=
      hX.exists_measurableSet_tailProcess_ae_eq_of_comap_exchangeableSigma hX_meas ht
    exact ⟨u, hu, hst.trans htu⟩
  · rintro s ⟨t, ht, hst⟩
    exact ⟨t, tailProcess_le_comap_exchangeableSigma X t ht, hst⟩

/-- Conditioning an observable on the pullback exchangeable σ-algebra agrees almost
everywhere with conditioning on the process tail, for a contractable process with measurable
coordinates under a finite measure. No integrability assumption on the observable is needed. -/
theorem Contractable.condExp_comap_exchangeableSigma_ae_eq_tailProcess
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) (f : Ω → E) :
    μ[f | MeasurableSpace.comap (fun ω i => X i ω) (exchangeableSigma α)] =ᵐ[μ]
      μ[f | tailProcess X] :=
  TauCeti.MeasureTheory.condExp_ae_eq_of_forall_exists_ae_eq
    (tailProcess_le_comap_exchangeableSigma X)
    ((MeasurableSpace.comap_mono exchangeableSigma_le).trans
      (Measurable.of_eval hX_meas).comap_le)
    fun _ hs => hX.exists_measurableSet_tailProcess_ae_eq_of_comap_exchangeableSigma hX_meas hs

end TauCeti.Probability
