/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Karp
public import TauCeti.ModelTheory.Scott.ExtensionPair
public import TauCeti.ModelTheory.Scott.PotentialIso
public import Mathlib.ModelTheory.Order

/-!
# Scott analysis of dense linear orders

Dense linear orders without endpoints, the models of Mathlib's first-order theory
`Language.order.dlo`, are the basic example of back-and-forth: by Cantor's argument
(Mathlib's `dlo_isExtensionPair`) every finite order-preserving partial map extends to any new
point. In the language of back-and-forth equivalence this gives, for structures of every
cardinality:

* between two nonempty dense linear orders without endpoints, tuples are back-and-forth
  equivalent at every level exactly when they have the same order type, and the two orders are
  potentially isomorphic;
* every dense linear order without endpoints, including the empty one, has internal Scott rank
  one;
* the Scott sentence of a countable nonempty dense linear order without endpoints, such as
  `ℚ`, is satisfied exactly by the nonempty models of `Language.order.dlo`, in every cardinality.

For countable structures potential isomorphism is isomorphism
(`TauCeti.countable_potentialIso_iff_iso`), so the first item refines Cantor's
`ℵ₀`-categoricity (Mathlib's `aleph0_categorical_dlo`); for uncountable orders it is strictly
weaker, as `ℚ` and `ℝ` are potentially isomorphic but not isomorphic.

## Main results

* `TauCeti.dlo_isExtensionPair_self`: the self-extension property, with no nonemptiness
  assumption.
* `TauCeti.bfEquiv_iff_sameAtomicType_of_dlo` and `TauCeti.potentialIso_of_dlo`.
* `TauCeti.internalScottRank_eq_one_of_dlo`.
* `TauCeti.realize_scottSentence_iff_of_dlo`.

## References

* Georg Cantor, *Beiträge zur Begründung der transfiniten Mengenlehre*, 1895.
* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, 1965.
-/

public section

universe w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language

section Self

variable (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.dlo]

/-- A dense linear order without endpoints has the self-extension property. Unlike Mathlib's
`dlo_isExtensionPair`, no nonemptiness is assumed: for an empty order it holds vacuously. -/
theorem dlo_isExtensionPair_self : Language.order.IsExtensionPair M M := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact fun _ m => isEmptyElim m
  · exact dlo_isExtensionPair M M

/-- Every dense linear order without endpoints, of any cardinality and including the empty one,
has internal Scott rank one. -/
@[simp]
theorem internalScottRank_eq_one_of_dlo :
    internalScottRank (L := Language.order) M = 1 :=
  (dlo_isExtensionPair_self M).internalScottRank_eq_one

end Self

section Pair

variable (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.dlo] [Nonempty M]
variable (N : Type w') [Language.order.Structure N] [N ⊨ Language.order.dlo] [Nonempty N]

/-- Between nonempty dense linear orders without endpoints, tuples are back-and-forth equivalent
at any level exactly when they have the same order type. -/
theorem bfEquiv_iff_sameAtomicType_of_dlo {α : Ordinal.{o}} {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} :
    BFEquiv (L := Language.order) α n a b ↔ SameAtomicType (L := Language.order) a b :=
  ⟨BFEquiv.sameAtomicType, fun h =>
    h.bfEquiv_of_isExtensionPair (dlo_isExtensionPair M N) (dlo_isExtensionPair N M) α⟩

/-- Any two nonempty dense linear orders without endpoints are potentially isomorphic, whatever
their cardinalities. -/
theorem potentialIso_of_dlo : PotentialIso (L := Language.order) M N :=
  (isTupleBFSystem_sameAtomicType (dlo_isExtensionPair M N) (dlo_isExtensionPair N M)
    sameAtomicType_elim0).potentialIso

end Pair

/-- The Scott sentence of a countable nonempty dense linear order without endpoints holds in a
structure of any cardinality exactly when that structure is a nonempty dense linear order
without endpoints. -/
theorem realize_scottSentence_iff_of_dlo (M : Type w) [Language.order.Structure M]
    [M ⊨ Language.order.dlo] [Nonempty M] [Countable M] (N : Type w')
    [Language.order.Structure N] :
    SentenceInf.Realize (scottSentence (L := Language.order) M) N ↔
      Nonempty N ∧ N ⊨ Language.order.dlo := by
  constructor
  · intro h
    have hMN := ((potentialIso_of_realize_scottSentence M h).infEquivAt
      ℕ).elementarilyEquivalent
    exact ⟨hMN.nonempty, hMN.theory_model⟩
  · rintro ⟨hN, hdlo⟩
    exact (infEquivAt_iff.mp ((potentialIso_of_dlo M N).infEquivAt ℕ) _).mp
      (realize_scottSentence_self M)

end TauCeti
