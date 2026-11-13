/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import TauCeti.MeasureTheory.Constructions.Baire.Basic
public import TauCeti.MeasureTheory.Measure.Regular

/-!
# Baire representatives for regular measures

For an outer regular measure finite on compact sets on a locally compact Hausdorff space,
every σ-compact set has a σ-compact Baire-measurable hull with null excess. If the measure is
also σ-finite and inner regular on finite-measure sets, every null measurable set has a
Baire-measurable representative modulo almost-everywhere equality, and consequently every simple
function agrees almost everywhere with a simple function measurable for the Baire σ-algebra. In
particular, this applies to Borel sets and simple functions for regular Haar measure on a
σ-compact locally compact Hausdorff group, without second countability.

The representative theorems use compact inner approximation and Baire hulls of compact sets.
They do not assert that the exceptional null set has a Baire-measurable null envelope, or that
the original set belongs to the completion of the Baire σ-algebra. The distinction matters
when comparing Borel and Baire measure theory without countability assumptions.

## Main results

* `MeasureTheory.NullMeasurableSet.exists_baire_ae_eq`: every null measurable set has a σ-compact
  Baire-measurable representative modulo almost-everywhere equality.
* `MeasureTheory.SimpleFunc.exists_baire_ae_eq`: every simple function agrees almost everywhere with
  a simple function measurable for `TauCeti.baire X`.

## References

* D. H. Fremlin, *Measure Theory*, §443, for the Baire and Borel comparison for Haar measures.
-/

public section

open Filter Set MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

namespace MeasureTheory

/-- For a σ-finite measure finite on compact sets, outer regular and inner regular on
finite-measure sets, every null measurable set has a σ-compact Baire-measurable representative
modulo almost-everywhere equality. This does not supply a Baire null envelope for the error. -/
theorem NullMeasurableSet.exists_baire_ae_eq {μ : Measure X} [μ.OuterRegular]
    [IsFiniteMeasureOnCompacts μ] [SigmaFinite μ] [μ.InnerRegularCompactLTTop]
    {s : Set X} (hs : NullMeasurableSet s μ) :
    ∃ B : Set X, IsSigmaCompact B ∧ MeasurableSet[TauCeti.baire X] B ∧ B =ᵐ[μ] s := by
  obtain ⟨t, -, ht, hts⟩ := hs.exists_isSigmaCompact_subset_ae_eq
  obtain ⟨B, htB, -, hB, hBm, hBμ⟩ := ht.exists_baire_hull (μ := μ) isOpen_univ (subset_univ t)
  refine ⟨B, hB, hBm, (ae_eq_set.2 ⟨hBμ, ?_⟩).trans hts⟩
  simp [sdiff_eq_empty.2 htB]

/-- For a σ-finite measure finite on compact sets, outer regular and inner regular on
finite-measure sets, every simple function agrees almost everywhere with a simple function
measurable for `TauCeti.baire X`. -/
theorem SimpleFunc.exists_baire_ae_eq {β : Type*} (s : SimpleFunc X β) (μ : Measure X)
    [μ.OuterRegular] [IsFiniteMeasureOnCompacts μ] [SigmaFinite μ]
    [μ.InnerRegularCompactLTTop] :
    ∃ s' : @SimpleFunc X (TauCeti.baire X) β, (s' : X → β) =ᵐ[μ] s := by
  rcases isEmpty_or_nonempty X with _ | ⟨⟨x₀⟩⟩
  · exact ⟨@SimpleFunc.ofIsEmpty X β (TauCeti.baire X) _, Eventually.of_forall isEmptyElim⟩
  have : Nonempty β := ⟨s x₀⟩
  induction s with
  | const c =>
    refine ⟨@SimpleFunc.const X β (TauCeti.baire X) c, ?_⟩
    rw [@SimpleFunc.coe_const X β (TauCeti.baire X), SimpleFunc.coe_const]
  | @pcw f g t ht hf hg =>
    classical
    obtain ⟨f', hf'⟩ := hf
    obtain ⟨g', hg'⟩ := hg
    obtain ⟨B, -, hBb, hBt⟩ := ht.nullMeasurableSet.exists_baire_ae_eq (μ := μ)
    refine ⟨@SimpleFunc.piecewise X β (TauCeti.baire X) B hBb f' g', ?_⟩
    rw [@SimpleFunc.coe_piecewise X β (TauCeti.baire X) B hBb, SimpleFunc.coe_piecewise]
    refine (piecewise_ae_eq_of_ae_eq_set hBt).trans ?_
    filter_upwards [hf', hg'] with x hfx hgx
    by_cases hxt : x ∈ t <;> simp [Set.piecewise, hxt, hfx, hgx]

end MeasureTheory
