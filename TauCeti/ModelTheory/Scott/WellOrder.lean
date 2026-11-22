/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import TauCeti.ModelTheory.BackAndForth.WellOrder
public import TauCeti.ModelTheory.Order
public import TauCeti.ModelTheory.Scott.Isomorphism

/-!
# Scott sentences of well-ordered structures

By Scott's isomorphism theorem every countable order `M` has an `Lω₁ω` sentence, in the language
of orders, whose countable models are exactly the orders isomorphic to `M`. When `M` is a
well-order, for example `o.ToType` for a countable ordinal `o`, its Scott sentence characterizes `M`
up to isomorphism among structures of arbitrary cardinality: models of a Scott sentence are
potentially isomorphic to `M`, and potential isomorphism out of a well-ordered structure is
isomorphism (`TauCeti.potentialIso_iff_iso_of_isWellOrder`,
`TauCeti.potentialIso_iff_iso_of_wellFoundedLT`). The same holds in any countable language with a
binary relation symbol well-ordering `M`, including languages with function symbols via the graph
translation.

For an infinite well-order this cannot be done in first-order logic, even by a theory with
infinitely many sentences: by `TauCeti.exists_countable_model_not_wellFoundedLT`, every
first-order theory of an infinite linear order has a countable model that is not well-ordered.
Hence, by `TauCeti.not_exists_theory_model_iff_nonempty_orderIso`, for an infinite countable
well-order `M` no first-order theory has, among countable structures, exactly the copies of `M` as
its models.

## Main definitions

* `Ordinal.ordinalScottSentence`: the canonical Scott sentence of a countable ordinal in the
  language of orders.

## Main results

* `TauCeti.realize_ordinalScottSentence_iff`: the countable models of the Scott sentence of a
  countable ordinal are exactly the orders isomorphic to that ordinal.
* `TauCeti.realize_scottSentenceAt_iff_of_isWellOrder` and
  `TauCeti.realize_scottSentence_iff_of_isWellOrder`: for a countable relational structure
  well-ordered by a binary relation symbol, its Scott sentence holds in a structure of any
  cardinality exactly when that structure is isomorphic to it.
* `TauCeti.scott_isomorphism_of_isWellOrder`: the same for an arbitrary countable language,
  possibly with function symbols.
* `TauCeti.exists_sentenceω_realize_iff_nonempty_orderIso`: every countable order has an `Lω₁ω`
  sentence true in exactly the countable orders isomorphic to it.
* `TauCeti.exists_sentenceω_realize_iff_nonempty_orderIso_of_wellFoundedLT`: for a countable
  well-order, the countability assumption on the model drops.

## References

* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, in
  *The Theory of Models*, 1965.
* H. Jerome Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
-/

public section

universe u v w w' o

open FirstOrder FirstOrder.Language Structure Ordinal

namespace Ordinal

open TauCeti

/-- The Scott sentence of a countable ordinal `β`, as a well-order in the language of orders. -/
noncomputable def ordinalScottSentence (β : Ordinal.{w}) (hβ : β < ω₁) :
    Language.order.Sentenceω :=
  letI := orderStructure β.ToType
  have := Cardinal.countable_toType_of_lt_omega_one hβ
  scottSentence (L := Language.order) β.ToType

/-- The Scott sentence of a countable ordinal is the canonical Scott sentence of its order. -/
theorem ordinalScottSentence_def (β : Ordinal.{w}) (hβ : β < ω₁) :
    ordinalScottSentence β hβ =
      letI := orderStructure β.ToType
      have := Cardinal.countable_toType_of_lt_omega_one hβ
      scottSentence (L := Language.order) β.ToType :=
  (rfl)

end Ordinal

namespace TauCeti

open FirstOrder FirstOrder.Language Structure
open scoped Ordinal

section Relational

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ k, L.Relations k)]
variable (M : Type w) [L.Structure M] [Countable M]

/-- At a countable internally stabilizing level, the Scott sentence of a countable structure `M`
well-ordered by a binary relation symbol holds in a structure `N` of any cardinality exactly when
`N` is isomorphic to `M`. -/
theorem realize_scottSentenceAt_iff_of_isWellOrder (lt : L.Relations 2)
    [IsWellOrder M (fun x y => RelMap lt ![x, y])] {α : Ordinal.{o}} (hα : α < ω₁)
    (hs : SelfStabilizesCompletely (L := L) M α) (N : Type w') [L.Structure N] :
    SentenceInf.Realize (scottSentenceAt (L := L) M α) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => (potentialIso_of_realize_scottSentenceAt M hα h).nonempty_equiv_of_isWellOrder lt,
    fun ⟨e⟩ => e.realize_scottSentenceAt hα hs⟩

/-- The canonical Scott sentence of a countable structure `M` well-ordered by a binary relation
symbol holds in a structure `N` of any cardinality exactly when `N` is isomorphic to `M`. -/
theorem realize_scottSentence_iff_of_isWellOrder (lt : L.Relations 2)
    [IsWellOrder M (fun x y => RelMap lt ![x, y])] (N : Type w') [L.Structure N] :
    SentenceInf.Realize (scottSentence (L := L) M) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => (potentialIso_of_realize_scottSentence M h).nonempty_equiv_of_isWellOrder lt,
    fun ⟨e⟩ => e.realize_scottSentence⟩

/-- At a countable internally stabilizing level, the Scott sentence of a countable relational
ordered structure whose order is a well-order holds in a structure `N` of any cardinality, with no
order assumption on `N`, exactly when `N` is isomorphic to `M`. -/
theorem realize_scottSentenceAt_iff_of_wellFoundedLT [IsOrdered L] [LinearOrder M] [WellFoundedLT M]
    [L.OrderedStructure M] {α : Ordinal.{o}} (hα : α < ω₁)
    (hs : SelfStabilizesCompletely (L := L) M α) (N : Type w') [L.Structure N] :
    SentenceInf.Realize (scottSentenceAt (L := L) M α) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => (potentialIso_of_realize_scottSentenceAt M hα h).nonempty_equiv_of_wellFoundedLT,
    fun ⟨e⟩ => e.realize_scottSentenceAt hα hs⟩

/-- The canonical Scott sentence of a countable relational ordered structure whose order is a
well-order holds in a structure `N` of any cardinality, with no order assumption on `N`, exactly
when `N` is isomorphic to `M`. -/
theorem realize_scottSentence_iff_of_wellFoundedLT [IsOrdered L] [LinearOrder M] [WellFoundedLT M]
    [L.OrderedStructure M] (N : Type w') [L.Structure N] :
    SentenceInf.Realize (scottSentence (L := L) M) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => (potentialIso_of_realize_scottSentence M h).nonempty_equiv_of_wellFoundedLT,
    fun ⟨e⟩ => e.realize_scottSentence⟩

end Relational

/-- **Scott's isomorphism theorem for well-ordered structures.** In a countable language, possibly
with function symbols, every countable structure `M` well-ordered by a binary relation symbol has
an `Lω₁ω` sentence that `M` satisfies and that holds in a structure `N` of any cardinality, in
any universe, exactly when `N` is isomorphic to `M`. -/
theorem scott_isomorphism_of_isWellOrder {L : Language.{u, v}}
    [Countable (Σ k, L.Functions k)] [Countable (Σ k, L.Relations k)]
    (M : Type w) [L.Structure M] [Countable M]
    (lt : L.Relations 2) [IsWellOrder M (fun x y => RelMap lt ![x, y])] :
    ∃ σ : L.Sentenceω, SentenceInf.Realize σ M ∧
      ∀ (N : Type w') [L.Structure N],
        (SentenceInf.Realize σ N ↔ Nonempty (M ≃[L] N)) := by
  obtain ⟨σ, hM, hN⟩ := scott_isomorphism_of_graph.{u, v, w, w'} (L := L) M
  refine ⟨σ, hM, fun N _ => hN N ?_⟩
  let := graphExpansion L M
  let := graphExpansion L N
  have : IsWellOrder M (fun x y =>
      (graphExpansion L M).RelMap (GraphRelation.base lt) ![x, y]) := by
    simpa only [graphExpansion_relMap_base] using
      (inferInstance : IsWellOrder M (fun x y => RelMap lt ![x, y]))
  exact realize_scottSentence_iff_of_isWellOrder (L := L.graphLanguage) M (GraphRelation.base lt) N

private theorem nonempty_equiv_order_iff {M : Type w} {N : Type w'}
    [Language.order.Structure M] [LE M] [Language.order.OrderedStructure M]
    [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N] :
    Nonempty (M ≃[Language.order] N) ↔ Nonempty (M ≃o N) := by
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ⟨StrongHomClass.toEquiv e⟩⟩
  let := StrongHomClass.toOrderIsoClass Language.order M N (M ≃[Language.order] N)
  exact ⟨OrderIso.ofClass e⟩

/-- A countable ordinal satisfies its own Scott sentence. -/
@[simp]
theorem realize_ordinalScottSentence_self {β : Ordinal.{w}} (hβ : β < ω₁) :
    letI := orderStructure β.ToType
    SentenceInf.Realize (ordinalScottSentence β hβ) β.ToType := by
  let := orderStructure β.ToType
  have := Cardinal.countable_toType_of_lt_omega_one hβ
  rw [ordinalScottSentence_def]
  exact realize_scottSentence_self _

/-- The Scott sentence of a countable ordinal `β` holds in a countable ordered structure, in any
universe, exactly when that structure is order-isomorphic to `β`. -/
@[simp]
theorem realize_ordinalScottSentence_iff {β : Ordinal.{w}} (hβ : β < ω₁) (N : Type w')
    [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N] [Countable N] :
    SentenceInf.Realize (ordinalScottSentence β hβ) N ↔ Nonempty (β.ToType ≃o N) := by
  let := orderStructure β.ToType
  have := Cardinal.countable_toType_of_lt_omega_one hβ
  rw [ordinalScottSentence_def, realize_scottSentence_iff]
  exact nonempty_equiv_order_iff

/-- Every countable order `M` has an `Lω₁ω` sentence in the language of orders that holds in a
countable order, in any universe, exactly when that order is isomorphic to `M`. For a countable
well-order `M`, such as `o.ToType` for an ordinal `o < ω₁`, its countable models are exactly the
well-orders of the order type of `M`. -/
theorem exists_sentenceω_realize_iff_nonempty_orderIso (M : Type w) [LE M] [Countable M] :
    ∃ σ : Language.order.Sentenceω, ∀ (N : Type w') [Language.order.Structure N] [LE N]
      [Language.order.OrderedStructure N] [Countable N],
      SentenceInf.Realize σ N ↔ Nonempty (M ≃o N) := by
  let := orderStructure M
  obtain ⟨σ, -, hσ⟩ := scott_isomorphism.{_, _, _, w'} (L := Language.order) M
  exact ⟨σ, fun N _ _ _ _ => (hσ N).trans nonempty_equiv_order_iff⟩

/-- Every countable well-order `M` has an `Lω₁ω` sentence in the language of orders that holds in
an order `N` of any cardinality, in any universe, exactly when `N` is isomorphic to `M`. -/
theorem exists_sentenceω_realize_iff_nonempty_orderIso_of_wellFoundedLT
    (M : Type w) [LinearOrder M] [WellFoundedLT M] [Countable M] :
    ∃ σ : Language.order.Sentenceω, ∀ (N : Type w') [Language.order.Structure N] [LE N]
      [Language.order.OrderedStructure N],
      SentenceInf.Realize σ N ↔ Nonempty (M ≃o N) := by
  let := orderStructure M
  exact ⟨scottSentence (L := Language.order) M, fun N _ _ _ =>
    (realize_scottSentence_iff_of_wellFoundedLT (L := Language.order) M N).trans
      nonempty_equiv_order_iff⟩

end TauCeti
