/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.ExchangeableSigma.Basic

/-!
# Null augmentation of the exchangeable σ-algebra

Under a finite contractable law on standard Borel paths, the exchangeable, tail and
shift-invariant σ-algebras have the same events modulo ambient null sets. This file states that
relationship as equality of σ-algebras augmented by those null sets.

We use Mathlib's `eventuallyMeasurableSpace m (ae ρ)`: its events agree `ρ`-almost everywhere with
events of `m`. Thus all three σ-algebras are augmented by the same ambient null sets. This is
different from separately completing the trimmed measures, which can have fewer null sets.
The unaugmented σ-algebras need not be equal.

The equalities let a caller transport measurable sets and functions between the three augmented
σ-algebras by rewriting, without choosing a new event representative for each use.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1,
  for the almost-sure agreement of the exchangeable, tail and invariant σ-fields.

The event representatives are supplied by `ExchangeableSigma.Basic`; the augmentation is
Mathlib's `eventuallyMeasurableSpace`. No formalization is copied or vendored here.
-/

public section

noncomputable section

open MeasureTheory Filter

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]

/-- The exchangeable and shift-invariant σ-algebras become equal after adjoining all ambient
`ρ`-null sets, under a finite contractable path law. -/
theorem ContractableLaw.eventuallyMeasurableSpace_exchangeableSigma_eq_invariants
    (hρ : ContractableLaw ρ) :
    eventuallyMeasurableSpace (exchangeableSigma α) (ae ρ) =
      eventuallyMeasurableSpace (MeasurableSpace.invariants (shift α)) (ae ρ) := by
  apply le_antisymm
  · rintro s ⟨t, ht, hst⟩
    obtain ⟨u, hu, htu⟩ := hρ.exists_measurableSet_invariants_ae_eq ht
    exact ⟨u, hu, hst.trans htu⟩
  · rintro s ⟨t, ht, hst⟩
    exact ⟨t, pathTail_le_exchangeableSigma t (invariants_shift_le_pathTail t ht), hst⟩

/-- The path tail and shift-invariant σ-algebras become equal after adjoining all ambient
`ρ`-null sets, under a finite contractable path law. -/
theorem ContractableLaw.eventuallyMeasurableSpace_pathTail_eq_invariants
    (hρ : ContractableLaw ρ) :
    eventuallyMeasurableSpace (pathTail α) (ae ρ) =
      eventuallyMeasurableSpace (MeasurableSpace.invariants (shift α)) (ae ρ) := by
  apply le_antisymm
  · rintro s ⟨t, ht, hst⟩
    obtain ⟨u, hu, htu⟩ :=
      hρ.exists_measurableSet_invariants_ae_eq (pathTail_le_exchangeableSigma t ht)
    exact ⟨u, hu, hst.trans htu⟩
  · rintro s ⟨t, ht, hst⟩
    exact ⟨t, invariants_shift_le_pathTail t ht, hst⟩

end TauCeti.Probability
