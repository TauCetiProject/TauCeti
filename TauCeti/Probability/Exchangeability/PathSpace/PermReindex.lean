module

public import TauCeti.Probability.Exchangeability.FullyExchangeable
public import TauCeti.Probability.Exchangeability.PathSpace.Reindex

/-!
# Permutation reindexing of path laws

This file records the path-law bridge for full exchangeability: reindexing paths by a
permutation of time preserves the path law exactly when the original process is fully
exchangeable.  This is part of the Layer 0 Exchangeability roadmap item asking for
process-level/path-law bridges.

The proofs are Tau Ceti adapters around the existing `pathLaw`, `FullyExchangeable`, and
general reindexing API. No external formalization is ported here.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Full exchangeability is exactly invariance of the path law under every time permutation. -/
theorem fullyExchangeable_iff_forall_map_permReindex_pathLaw
    (μ : Measure Ω) {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ) :
    FullyExchangeable μ X ↔
      ∀ π : Equiv.Perm ℕ,
        (pathLaw μ X).map (permReindex (α := α) π) = pathLaw μ X := by
  constructor
  · intro h π
    rw [map_permReindex_pathLaw μ hX π]
    exact h.permute π
  · intro h π
    have hπ := h π
    rwa [map_permReindex_pathLaw μ hX π] at hπ

/-- A fully exchangeable process has path law invariant under any time permutation. -/
theorem FullyExchangeable.map_permReindex_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) (hX : ∀ i, AEMeasurable (X i) μ)
    (π : Equiv.Perm ℕ) :
    (pathLaw μ X).map (permReindex (α := α) π) = pathLaw μ X :=
  (fullyExchangeable_iff_forall_map_permReindex_pathLaw μ hX).mp h π

/-- Reindexing path space by any time permutation preserves the path law of a fully
exchangeable process. -/
theorem FullyExchangeable.measurePreserving_permReindex {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) (hX : ∀ i, AEMeasurable (X i) μ) (π : Equiv.Perm ℕ) :
    MeasurePreserving (permReindex (α := α) π) (pathLaw μ X) (pathLaw μ X) :=
  ⟨measurable_permReindex π, h.map_permReindex_pathLaw hX π⟩

/-- Full exchangeability is exactly preservation of the path law by every time-permutation
reindexing map. -/
theorem fullyExchangeable_iff_forall_measurePreserving_permReindex
    (μ : Measure Ω) {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ) :
    FullyExchangeable μ X ↔
      ∀ π : Equiv.Perm ℕ,
        MeasurePreserving (permReindex (α := α) π) (pathLaw μ X) (pathLaw μ X) := by
  rw [fullyExchangeable_iff_forall_map_permReindex_pathLaw μ hX]
  constructor
  · intro h π
    exact ⟨measurable_permReindex π, h π⟩
  · intro h π
    exact (h π).map_eq

/-- If every time permutation preserves the path law, then the process is fully exchangeable. -/
theorem fullyExchangeable_of_forall_map_permReindex_pathLaw
    {μ : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ)
    (h : ∀ π : Equiv.Perm ℕ,
      (pathLaw μ X).map (permReindex (α := α) π) = pathLaw μ X) :
    FullyExchangeable μ X :=
  (fullyExchangeable_iff_forall_map_permReindex_pathLaw μ hX).mpr h

/-- A measure-preserving form of the path-law bridge: if every time permutation preserves the
path law, then the process is fully exchangeable. -/
theorem fullyExchangeable_of_forall_measurePreserving_permReindex
    {μ : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ)
    (h : ∀ π : Equiv.Perm ℕ,
      MeasurePreserving (permReindex (α := α) π) (pathLaw μ X) (pathLaw μ X)) :
    FullyExchangeable μ X :=
  (fullyExchangeable_iff_forall_measurePreserving_permReindex μ hX).mpr h

end Probability

end TauCeti
