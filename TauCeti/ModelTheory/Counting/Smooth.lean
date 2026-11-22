/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.RelationalConfiguration.Smooth

/-!
# Countable model classes from thinness and smoothness

In a countable relational vocabulary, a countable-branching infinitary sentence `φ` has countably
many models on `ℕ` up to isomorphism if and only if `φ` is thin on `ℕ` (`IsThinOnNatModels φ`) and
restricted isomorphism on its models on `ℕ` (`isoSetoidOn ℕ φ`) is smooth
(`countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth`).

## Main results

* `TauCeti.countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth`: a
  countable-branching sentence has countably many models on `ℕ` up to isomorphism iff it is thin on
  `ℕ` and has smooth isomorphism.

## References

* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapters 5 and 11.
-/

public section

universe u v uκ

open FirstOrder FirstOrder.Language

namespace TauCeti

open RelationalConfiguration

/-- An infinitary sentence `φ` with countable branching has countably many models on `ℕ` up to
isomorphism if and only if `φ` is thin on `ℕ` and `isoSetoidOn ℕ φ` is smooth. -/
theorem countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth
    {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
    {κ : Type uκ} [Countable κ] {φ : L.SentenceInf κ} :
    Countable (Quotient (isoSetoidOn ℕ φ)) ↔
      IsThinOnNatModels φ ∧ (isoSetoidOn ℕ φ).IsSmooth := by
  rw [isoSetoidOn, countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth
    (measurableSet_modelsOf φ), isThinOnNatModels_iff_isThinOn]

end TauCeti
