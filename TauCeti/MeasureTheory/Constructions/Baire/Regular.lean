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
  · refine ⟨@SimpleFunc.mk X (TauCeti.baire X) β s (fun y => ?_) s.finite_range,
      Eventually.of_forall isEmptyElim⟩
    rw [eq_empty_of_isEmpty (s ⁻¹' {y})]
    exact @MeasurableSet.empty X (TauCeti.baire X)
  classical
  have hfib (y : β) := (s.measurableSet_fiber y).nullMeasurableSet.exists_baire_ae_eq (μ := μ)
  choose B _ hBb hBae using hfib
  let build : List β → @SimpleFunc X (TauCeti.baire X) β := fun L =>
    L.foldr (fun y acc => @SimpleFunc.piecewise X β (TauCeti.baire X) (B y) (hBb y)
      (@SimpleFunc.const X β (TauCeti.baire X) y) acc)
      (@SimpleFunc.const X β (TauCeti.baire X) (s x₀))
  have hbuild_eq : ∀ (L : List β) (x : X),
      (∀ y ∈ L, x ∈ B y ↔ s x = y) → s x ∈ L → build L x = s x := by
    let _ : MeasurableSpace X := TauCeti.baire X
    intro L
    induction L with
    | nil => simp
    | cons y L ih =>
      intro x hxB hxL
      dsimp only [build] at ih ⊢
      rw [List.foldr_cons, SimpleFunc.piecewise_apply]
      by_cases hxy : s x = y
      · have hxBy : x ∈ B y := (hxB y List.mem_cons_self).2 hxy
        simp [hxBy, hxy]
      · have hxBy : x ∉ B y := fun hm => hxy ((hxB y List.mem_cons_self).1 hm)
        have hxL' : s x ∈ L := (List.mem_cons.1 hxL).resolve_left hxy
        simp only [hxBy, ↓reduceIte]
        exact ih x (fun z hz => hxB z (List.mem_cons_of_mem y hz)) hxL'
  refine ⟨build s.range.toList, ?_⟩
  have hae : ∀ᵐ x ∂μ, ∀ y ∈ (s.range : Set β), x ∈ B y ↔ s x = y := by
    refine (eventually_all_finite s.range.finite_toSet).2 fun y _ => ?_
    filter_upwards [hBae y] with x hx
    simpa [eq_comm] using hx
  filter_upwards [hae] with x hx
  exact hbuild_eq s.range.toList x (fun y hy => hx y (Finset.mem_coe.2 (Finset.mem_toList.1 hy)))
    (Finset.mem_toList.2 (s.mem_range_self x))

end MeasureTheory
