/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.LocallyCompact

/-!
# Amenability by finitely additive probabilities on Borel sets

Let `μ` be a regular left Haar measure on a locally compact group `G`. Then `G` is amenable
exactly when its Borel sets carry a left-invariant finitely additive probability annihilating
`μ`-null sets. The probability is an `AddContent`, not a countably additive `Measure`.
There is no countability, σ-compactness or separation assumption on `G`.

The same criterion holds on the `μ`-null-measurable sets, that is, the measurable sets of the
completion of `μ`. Extension across null sets and restriction to Borel sets preserve both
normalization and invariance. The assertions impose no conditions on the values of a content
outside its specified algebra of sets; such values do not affect the characterization.

The Borel criterion combines the Haar `L∞` characterization
`TauCeti.amenable_iff_exists_lpTop_invariant_of_regular` with the indicator/integration
correspondence
`MeasureTheory.exists_invariant_positiveLinearMap_lpTop_iff_exists_invariantContent`.
Completion uses `MeasureTheory.AddContent.completion`.

## Main results

* `TauCeti.amenable_iff_exists_invariantContent_of_regular`: the Borel criterion.
* `TauCeti.amenable_iff_exists_invariantContent_completion_of_regular`: the completed criterion.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.3.1, for invariant
  means on Haar `L∞` and finitely additive probabilities. Here `L∞` uses global
  almost-everywhere equality, and nullity refers to `μ`, not local nullity.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- A locally compact group is amenable exactly when its Borel sets carry a left-invariant
finitely additive probability vanishing on null sets of a regular left Haar measure `μ`.
Only Borel sets are tested; values of the content on other sets are irrelevant. -/
theorem amenable_iff_exists_invariantContent_of_regular :
    Amenable G ↔
      ∃ ν : AddContent ℝ≥0∞ {s : Set G | MeasurableSet s}, ν univ = 1 ∧
        (∀ s, MeasurableSet s → μ s = 0 → ν s = 0) ∧
        ∀ (g : G) s, MeasurableSet s → ν (g • s) = ν s :=
  (amenable_iff_exists_lpTop_invariant_of_regular μ).trans
    exists_invariant_positiveLinearMap_lpTop_iff_exists_invariantContent

/-- The finitely additive probability criterion for amenability also holds on the measurable
sets of the completion of a regular left Haar measure `μ`. Null annihilation is required even
for non-Borel null sets. No values outside the null-measurable sets are tested. -/
theorem amenable_iff_exists_invariantContent_completion_of_regular :
    Amenable G ↔
      ∃ ν : AddContent ℝ≥0∞ {s : Set G | NullMeasurableSet s μ}, ν univ = 1 ∧
        (∀ s, μ s = 0 → ν s = 0) ∧
        ∀ (g : G) s, NullMeasurableSet s μ → ν (g • s) = ν s := by
  rw [amenable_iff_exists_invariantContent_of_regular μ]
  constructor
  · rintro ⟨ν, hν₁, hνμ, hν⟩
    exact ⟨ν.completion μ hνμ, by simpa using hν₁,
      fun s hs => ν.completion_of_measure_eq_zero hs,
      fun g s _ => ν.completion_smul hν g s⟩
  · rintro ⟨ν, hν₁, hνμ, hν⟩
    refine ⟨ν.map id (fun _ hs => hs.nullMeasurableSet), by simpa using hν₁,
      fun s _ hs => ?_, fun g s hs => ?_⟩
    · simpa using hνμ s hs
    · simpa using hν g s hs.nullMeasurableSet

end TauCeti
