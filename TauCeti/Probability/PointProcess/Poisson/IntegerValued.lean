/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.MeasurableSpace.CountablyGenerated
public import TauCeti.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Poisson random measures have integer-valued realizations

A Poisson count on any fixed finite-intensity set is almost surely a natural number.
On a countably generated measurable space, these individual assertions imply that the
whole random measure is almost surely integer-valued. The exceptional event is independent
of the tested measurable set. A countable generating π-system and a finite-intensity cover
allow the finite-measure integrality criterion to be applied on each piece.

Sigma-finite intensity also implies sigma-finiteness of almost every realization, without
any countable-generation assumption. On a locally compact sigma-compact Hausdorff space,
intensity finite on compact sets implies almost-sure local finiteness. These statements
justify passing from the independent-count definition to point-measure realizations; they
do not assert simplicity, since atomic intensities allow multiple occurrences.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 2–3 (integer-valued realizations of Poisson random measures).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X}

/-- A Poisson random measure with sigma-finite intensity is almost surely sigma-finite.
No topology or countable-generation assumption on the location space is required. -/
theorem IsPoissonRandomMeasure.ae_sigmaFinite (h : IsPoissonRandomMeasure P N Λ)
    [SigmaFinite Λ] : ∀ᵐ ω ∂P, SigmaFinite (N ω) := by
  have hfinite (n : ℕ) : ∀ᵐ ω ∂P, N ω (spanningSets Λ n) < ∞ :=
    h.ae_lt_top (measurableSet_spanningSets Λ n) (measure_spanningSets_lt_top Λ n)
  filter_upwards [ae_all_iff.2 hfinite] with ω hω
  exact ⟨⟨⟨spanningSets Λ, fun _ => mem_univ _, hω, iUnion_spanningSets Λ⟩⟩⟩

/-- On a countably generated measurable space, a Poisson random measure with sigma-finite
intensity is almost surely integer-valued, simultaneously on all measurable sets. -/
theorem IsPoissonRandomMeasure.ae_isIntegerValued (h : IsPoissonRandomMeasure P N Λ)
    [MeasurableSpace.CountablyGenerated X] [SigmaFinite Λ] :
    ∀ᵐ ω ∂P, (N ω).IsIntegerValued := by
  classical
  obtain ⟨C, hcount, hpi, huniv, hgen⟩ :=
    MeasurableSpace.exists_countable_isPiSystem_generateFrom (α := X)
  have hmeas : ∀ A ∈ C, MeasurableSet A := fun A hA => by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hA
  -- Restrict to finite-intensity pieces before taking the countable intersection of
  -- full-measure events. Integrality on a generating π-system then controls all sets.
  have hpiece (n : ℕ) : ∀ᵐ ω ∂P, ((N ω).restrict (spanningSets Λ n)).IsIntegerValued := by
    have hcounts : ∀ A ∈ C, ∀ᵐ ω ∂P, ∃ k : ℕ, N ω (A ∩ spanningSets Λ n) = k := by
      intro A hA
      exact h.ae_exists_eq_natCast ((hmeas A hA).inter (measurableSet_spanningSets Λ n))
        ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top Λ n))
    filter_upwards [(ae_ball_iff hcount).2 hcounts] with ω hω
    apply Measure.isIntegerValued_of_isPiSystem hgen hpi
    · intro A hA
      simpa only [Measure.restrict_apply (hmeas A hA)] using hω A hA
    · simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hω univ huniv
  filter_upwards [ae_all_iff.2 hpiece] with ω hω
  exact Measure.isIntegerValued_of_restrict (iUnion_spanningSets Λ) hω

/-- If the intensity is finite on compact sets, almost every realization of a Poisson
random measure is locally finite. The assertion holds simultaneously at every location. -/
theorem IsPoissonRandomMeasure.ae_isLocallyFiniteMeasure
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    [IsFiniteMeasureOnCompacts Λ] (h : IsPoissonRandomMeasure P N Λ) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) := by
  let K := CompactExhaustion.choice X
  have hfinite (n : ℕ) : ∀ᵐ ω ∂P, N ω (K n) < ∞ :=
    h.ae_lt_top (K.isCompact n).measurableSet (K.isCompact n).measure_lt_top
  filter_upwards [ae_all_iff.2 hfinite] with ω hω
  exact (K.isLocallyFiniteMeasure_iff (N ω)).2 hω

end TauCeti.Probability
