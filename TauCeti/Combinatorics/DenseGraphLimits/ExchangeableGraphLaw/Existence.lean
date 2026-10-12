/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Empirical
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Compact

/-!
# Every exchangeable graph law is a graphon mixture

Every exchangeable graph law is the mixture law of some probability measure on the graphon space
over the unit interval (`exists_mixtureExchangeableLaw_eq`). This is the existence half of the
Diaconis–Janson correspondence between exchangeable graph laws and graphon mixtures, obtained from
graphon-space compactness with no array-level input. It asserts only that a mixing measure exists:
it makes no claim of uniqueness and picks no canonical one.

Compactness enters through the space of mixing measures: every sequence of probability measures
on the compact graphon space has a weakly convergent subsequence
(`exists_subseq_tendsto_probabilityMeasure`). Applied to the empirical mixing measures of a law,
the limit of such a subsequence represents the law by
`mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing`.

## Main results

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

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

/-- **Every exchangeable graph law is a graphon mixture.** For every exchangeable graph law `L`
there is a probability measure `P` on `GraphonSpaceI` whose mixture law is `L`: any weak limit of a
subsequence of the empirical mixing measures of `L` is one. -/
theorem exists_mixtureExchangeableLaw_eq (L : ExchangeableGraphLaw) :
    ∃ P : ProbabilityMeasure GraphonSpaceI, mixtureExchangeableLaw P = L := by
  obtain ⟨P, φ, hφ, hconv⟩ := exists_subseq_tendsto_probabilityMeasure (empiricalMixing L)
  exact ⟨P, mixtureExchangeableLaw_eq_of_tendsto_empiricalMixing L hφ.tendsto_atTop hconv⟩

end DenseGraphLimits

end TauCeti
