/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

## Main results

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

namespace TauCeti

open FirstOrder FirstOrder.Language Structure

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
