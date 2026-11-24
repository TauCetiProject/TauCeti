/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import TauCeti.ModelTheory.Order
public import TauCeti.ModelTheory.Scott.Isomorphism

/-!
# Well-orders of a fixed order type are `Lω₁ω`-definable but not first-order axiomatizable

By Scott's isomorphism theorem every countable order `M` has an `Lω₁ω` sentence, in the language
of orders, whose countable models are exactly the orders isomorphic to `M`. When `M` is a
well-order, for example `o.ToType` for a countable ordinal `o`, these are exactly the countable
well-orders of the order type of `M`.

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

* `TauCeti.exists_sentenceω_realize_iff_nonempty_orderIso`: every countable order has an `Lω₁ω`
  sentence true in exactly the countable orders isomorphic to it.

## References

* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, in
  *The Theory of Models*, 1965.
* H. Jerome Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
-/

public section

universe w w'

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
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ⟨StrongHomClass.toEquiv e⟩⟩
  let := StrongHomClass.toOrderIsoClass Language.order β.ToType N (β.ToType ≃[Language.order] N)
  exact ⟨OrderIso.ofClass e⟩

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
  refine ⟨σ, fun N _ _ _ _ => (hσ N).trans ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ⟨StrongHomClass.toEquiv e⟩⟩⟩
  let := StrongHomClass.toOrderIsoClass Language.order M N (M ≃[Language.order] N)
  exact ⟨OrderIso.ofClass e⟩

end TauCeti
