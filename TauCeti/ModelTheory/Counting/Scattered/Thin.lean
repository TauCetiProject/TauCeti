/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.RelationalConfiguration.Separation

/-!
# Thinness of back-and-forth scattered sets

A back-and-forth scattered set `K` of relational configurations on `ℕ` meets only countably many
classes at every countable level `α < ω₁` (`TauCeti.BFScattered`). By uniform back-and-forth
separation (`TauCeti.RelationalConfiguration.exists_uniform_bfSeparation`), `K` carries no Cantor
antichain for isomorphism (`TauCeti.BFScattered.not_hasCantorAntichainOn`): the off-diagonal of a
putative Cantor copy is analytic and disjoint from isomorphism, so some countable level separates
the copy and would embed Cantor space into a countable level quotient. No definability or
invariance of `K`, and no countability hypothesis on the relational language `L`, is needed.

When `L` has countably many relation symbols of each arity, `RelationalConfiguration L ℕ` is Polish,
so perfect antichains and Cantor antichains exist together and every back-and-forth scattered set is
thin (`TauCeti.BFScattered.isThinOn`).

## Main results

* `TauCeti.BFScattered.not_hasCantorAntichainOn`: a scattered set on `ℕ` carries no Cantor antichain
  for isomorphism, unconditionally on the language and the set.
* `TauCeti.BFScattered.isThinOn`: in a countable relational vocabulary, every scattered set on `ℕ`
  is thin for isomorphism.
* `TauCeti.bfScattered_modelsOf_iff_isThinOnNatModels`: a sentence with countable branching is
  thin on `ℕ` exactly when its model class on `ℕ` is back-and-forth scattered.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the
  chapter on Vaught counterexamples (scattered sentences).
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.1 (scattered sentences and perfect sets).
* Adapted from `InfinitaryLogic/Descriptive/BFScattered.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0), generalized here to arbitrary relational languages without countability hypotheses in
  `BFScattered.not_hasCantorAntichainOn`.
-/

public section

universe u v

open FirstOrder

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {K : Set (RelationalConfiguration L ℕ)}

/-- **Scattered sets carry no Cantor antichains.** If `K` is back-and-forth scattered, then `K`
admits no Cantor antichain for isomorphism. No definability or invariance of `K`, and no
countability hypothesis on `L`, is assumed. -/
theorem BFScattered.not_hasCantorAntichainOn (hK : BFScattered K) :
    ¬ (isoSetoid L ℕ).HasCantorAntichainOn K :=
  not_hasCantorAntichainOn_of_countable_bfEquivSetoid (bfScattered_iff.mp hK)

/-- **Scattered sets are thin** in a countable relational vocabulary, with no definability or
invariance hypothesis on `K`. -/
theorem BFScattered.isThinOn [∀ n, Countable (L.Relations n)] (hK : BFScattered K) :
    (isoSetoid L ℕ).IsThinOn K :=
  isThinOn_of_countable_bfEquivSetoid (bfScattered_iff.mp hK)

/-- **Thin sentences are exactly the scattered ones.** For an infinitary sentence with countable
branching in a countable relational vocabulary, absence of a perfect set of pairwise
non-isomorphic models on `ℕ` is equivalent to countability of every countable back-and-forth
level quotient on its models on `ℕ`. -/
theorem bfScattered_modelsOf_iff_isThinOnNatModels {ι : Type*} [Countable ι]
    [∀ n, Countable (L.Relations n)] {φ : L.SentenceInf ι} :
    BFScattered (modelsOf (V := ℕ) φ) ↔ IsThinOnNatModels φ :=
  ⟨fun h => isThinOnNatModels_iff_isThinOn.2 h.isThinOn,
    IsThinOnNatModels.bfScattered_modelsOf⟩

end TauCeti
