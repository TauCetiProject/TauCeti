/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.Baire.Basic
public import TauCeti.MeasureTheory.Measure.Regular

/-!
# Baire representatives for regular measures

For an outer regular measure finite on compact sets on a locally compact Hausdorff space,
every σ-compact set has a σ-compact Baire-measurable hull with null excess. If the measure is
also σ-finite and inner regular on finite-measure sets, every null measurable set has a
Baire-measurable representative modulo almost-everywhere equality. In particular, this applies
to Borel sets for regular Haar measure on a σ-compact locally compact Hausdorff group, without
second countability.

The representative theorem uses compact inner approximation and Baire hulls of compact sets.
It does not assert that the exceptional null set has a Baire-measurable null envelope, or that
the original set belongs to the completion of the Baire σ-algebra. The distinction matters
when comparing Borel and Baire measure theory without countability assumptions.

## References

* D. H. Fremlin, *Measure Theory*, §443, for the Baire and Borel comparison for Haar measures.
-/

public section

open Set MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
  [μ.OuterRegular] [IsFiniteMeasureOnCompacts μ]

/-- A σ-compact set has a σ-compact Baire-measurable hull with null excess, inside any
prescribed open neighbourhood. No σ-finiteness assumption on the measure is needed. -/
theorem IsSigmaCompact.exists_baire_hull {s U : Set X} (hs : IsSigmaCompact s)
    (hU : IsOpen U) (hsU : s ⊆ U) :
    ∃ B : Set X, s ⊆ B ∧ B ⊆ U ∧ IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire X] B ∧
      μ (B \ s) = 0 := by
  obtain ⟨K, hK, rfl⟩ := hs
  have hhull (n : ℕ) := (hK n).exists_baire_hull (μ := μ) (hK n).measure_ne_top hU
    ((subset_iUnion K n).trans hsU)
  choose B hKB hBU hBc hBm hBμ using hhull
  refine ⟨⋃ n, B n, iUnion_mono hKB, iUnion_subset hBU,
    isSigmaCompact_iUnion_of_isCompact B hBc, MeasurableSet.iUnion hBm, ?_⟩
  refine measure_mono_null ?_ (measure_iUnion_null hBμ)
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx.1
  exact mem_iUnion.2 ⟨n, hn, fun hxn => hx.2 (mem_iUnion.2 ⟨n, hxn⟩)⟩

namespace MeasureTheory

/-- For a σ-finite measure finite on compact sets, outer regular and inner regular on
finite-measure sets, every null measurable set has a σ-compact Baire-measurable representative
modulo almost-everywhere equality. This does not supply a Baire null envelope for the error. -/
theorem NullMeasurableSet.exists_baire_ae_eq [SigmaFinite μ] [μ.InnerRegularCompactLTTop]
    {s : Set X} (hs : NullMeasurableSet s μ) :
    ∃ B : Set X, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire X] B ∧ B =ᵐ[μ] s := by
  obtain ⟨t, -, ht, hts⟩ := hs.exists_isSigmaCompact_subset_ae_eq
  obtain ⟨B, htB, -, hB, hBm, hBμ⟩ := ht.exists_baire_hull (μ := μ) isOpen_univ (subset_univ t)
  refine ⟨B, hB, hBm, (ae_eq_set.2 ⟨hBμ, ?_⟩).trans hts⟩
  simp [sdiff_eq_empty.2 htB]

end MeasureTheory
