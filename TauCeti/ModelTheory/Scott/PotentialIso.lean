/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Presentation
public import TauCeti.ModelTheory.Scott.Sentence

/-!
# Models of Scott sentences are potentially isomorphic

The tuple system supplied by a Scott sentence yields a back-and-forth system of finitely
generated partial equivalences. This conclusion applies to models of arbitrary cardinality,
not just countable models. It is the potential-isomorphism step in Dana Scott's
*Logic with denumerably long formulas and finite strings of quantifiers* (1965).
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language
open scoped Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ k, L.Relations k)]
variable (M : Type w) [L.Structure M] [Countable M]
variable {N : Type w'} [L.Structure N]

/-- Every model of the Scott sentence at a countable level is potentially isomorphic to the
original structure. Neither internal stabilization nor countability of the model is needed. -/
theorem potentialIso_of_realize_scottSentenceAt {α : Ordinal.{o}} (hα : α < ω₁)
    (h : SentenceInf.Realize (scottSentenceAt (L := L) M α) N) :
    PotentialIso (L := L) M N :=
  (isTupleBFSystem_of_realize_scottSentenceAt M hα h).potentialIso

/-- Every model of the canonical Scott sentence is potentially isomorphic to the original
structure, even when the model is uncountable. -/
theorem potentialIso_of_realize_scottSentence
    (h : SentenceInf.Realize (scottSentence (L := L) M) N) :
    PotentialIso (L := L) M N := by
  rw [scottSentence_def] at h
  exact potentialIso_of_realize_scottSentenceAt M (selfStabilizationOrdinal_lt_omega_one M) h

end TauCeti
