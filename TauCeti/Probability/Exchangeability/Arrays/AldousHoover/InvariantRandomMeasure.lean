/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the row directing measure and its invariant law occur in the conclusion and proof.
public import TauCeti.Probability.Exchangeability.Arrays.DeFinetti
-- Public: the coded marginal process and its conditional factorization occur in the conclusion.
public import TauCeti.Probability.Exchangeability.RandomMeasure
-- Non-public: measurability of pushforward on probability measures is used in the proof.
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Coded coordinate marginals of an invariant random row law

For a separately exchangeable array, de Finetti supplies a random probability measure `ν` on row
paths. Its law is invariant under permuting the column coordinates, although `ν` itself is not
generally exchangeable almost surely. The invariant-random-measure API turns the one-coordinate
marginals of `ν` into an exchangeable measure-valued sequence.

Because the Giry measurable space on `ProbabilityMeasure α` is not available as a standard Borel
space, the sequence is represented by the measurable injective evaluation code from
`MeasureTheory.Measure.ProbabilityMeasure.Coding`. De Finetti then shows that, conditionally on one
global random law, the coded coordinate marginals are i.i.d. This retains every one-coordinate
marginal of the random row law.

The one-coordinate marginals do not in general recover the row law, since they omit its higher
finite-dimensional marginals.

## Main result

* `TauCeti.Probability.SeparatelyExchangeable.exists_directing_arrayRow_codedCoordinateMarginals`
  -- choose a row directing measure whose coded coordinate marginals are conditionally i.i.d.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
arrays.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The coded coordinate marginals of a row directing measure admit a conditional de Finetti
factorization.** A separately exchangeable array has a row directing measure `ν` such that, under
the law of `ν`, the measurable injective codes of its one-coordinate marginals are conditionally
i.i.d. The conditional directing law is the global parameter at the first level of the
Aldous--Hoover factorization. -/
theorem SeparatelyExchangeable.exists_directing_arrayRow_codedCoordinateMarginals
    [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃ ν : Ω → ProbabilityMeasure (ℕ → α),
      ConditionallyIIDWith μ (arrayRow X) ν ∧
        ConditionallyIID (μ.map ν) fun i P => codedCoordinateMarginals P i := by
  obtain ⟨ν, hν, hinv⟩ := h.exists_directing_arrayRow_mixingLaw_invariant hX
  have hinv' : ∀ τ : Equiv.Perm ℕ,
      (μ.map ν).map (fun P => P.map (permReindex τ)) = μ.map ν := by
    intro τ
    have hpush : Measurable fun P : ProbabilityMeasure (ℕ → α) => P.map (permReindex τ) :=
      TauCeti.MeasureTheory.measurable_probabilityMeasure_map (measurable_reindex τ)
    rw [Measure.map_map hpush hν.measurable_directing]
    have hcomp : (fun P : ProbabilityMeasure (ℕ → α) => P.map (permReindex τ)) ∘ ν =
        fun ω => (ν ω).map (fun x : ℕ → α => fun k => x (τ k)) := by
      funext ω
      congr 1
    rw [hcomp]
    exact hinv τ
  exact ⟨ν, hν, conditionallyIID_codedCoordinateMarginals_of_invariant (μ.map ν) hinv'⟩

end Probability

end TauCeti

end
