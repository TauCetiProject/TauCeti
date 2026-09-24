/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Empirical
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Compact
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Every exchangeable graph law is a graphon mixture

Every exchangeable graph law is the mixture law of some probability measure on the graphon space
over the unit interval (`exists_mixtureExchangeableLaw_eq`). This is the existence half of the
Diaconis–Janson correspondence between exchangeable graph laws and graphon mixtures, obtained from
graphon-space compactness with no array-level input. It asserts only that a mixing measure exists:
it makes no claim of uniqueness and picks no canonical one.

Compactness enters through the space of mixing measures. Since `GraphonSpaceI` is a compact metric
space, so is `ProbabilityMeasure GraphonSpaceI` with the topology of weak convergence, and every
sequence of mixing measures has a weakly convergent subsequence
(`exists_subseq_tendsto_probabilityMeasure`). Applied to the empirical mixing measures of a law,
the limit of such a subsequence represents the law by
`mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing`.

## Main results

* `TauCeti.DenseGraphLimits.exists_subseq_tendsto_probabilityMeasure` — every sequence of
  probability measures on `GraphonSpaceI` has a weakly convergent subsequence.
* `TauCeti.DenseGraphLimits.exists_mixtureExchangeableLaw_eq` — **every exchangeable graph law is
  the mixture law of a probability measure on `GraphonSpaceI`.**

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Section 11.3.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/MixtureExistence.lean`. The
  existence argument follows its extraction from the empirical mixing measures.
-/

public section

noncomputable section

open MeasureTheory Filter Topology

namespace TauCeti

namespace DenseGraphLimits

/-- **Compactness extraction.** Every sequence of probability measures on `GraphonSpaceI` has a
weakly convergent subsequence: the graphon space is a compact metric space, so its space of
probability measures is compact and metrizable (the compact-space direction of Prokhorov's
theorem, with no tightness argument). -/
theorem exists_subseq_tendsto_probabilityMeasure (Ps : ℕ → ProbabilityMeasure GraphonSpaceI) :
    ∃ (P : ProbabilityMeasure GraphonSpaceI) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (Ps ∘ φ) atTop (𝓝 P) :=
  CompactSpace.tendsto_subseq Ps

/-- **Every exchangeable graph law is a graphon mixture.** For every exchangeable graph law `L`
there is a probability measure `P` on `GraphonSpaceI` whose mixture law is `L`: any weak limit of a
subsequence of the empirical mixing measures of `L` is one. -/
theorem exists_mixtureExchangeableLaw_eq (L : ExchangeableGraphLaw) :
    ∃ P : ProbabilityMeasure GraphonSpaceI, mixtureExchangeableLaw P = L := by
  obtain ⟨P, φ, hφ, hconv⟩ := exists_subseq_tendsto_probabilityMeasure (empiricalMixing L)
  exact ⟨P, mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing L hφ.tendsto_atTop hconv⟩

end DenseGraphLimits

end TauCeti
