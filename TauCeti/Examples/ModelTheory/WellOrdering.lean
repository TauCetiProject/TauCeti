/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.CodedConnectives
public import TauCeti.ModelTheory.Scott.WellOrder
import TauCeti.ModelTheory.WellOrdering

/-!
# Well-orders of bounded type

For a countable ordinal `α`, the countable disjunction over `β < α` of the Scott sentences of the
well-orders `β` is an `L_{ω₁ω}` sentence in the language of orders whose countable models are
exactly the well-orders of order type below `α`. So every countable bound on order types is
expressed by a single sentence, and the ordinal `α` itself is not a model. This is consistent with
`Sentenceω.wellOrder_type_boundedness`, which bounds the order types of the models of any sentence
all of whose models are well-ordered.

No single sentence covers all countable well-orders: by
`TauCeti.not_exists_sentenceω_realize_iff_wellFoundedLT`, no sentence of the language of orders has
as its countable linear models exactly the countable well-orders. That result and its main step
`TauCeti.exists_countable_realize_not_wellFoundedLT` are general facts about well-orders, so they
live beside `Sentenceω.wellOrder_type_boundedness` in `TauCeti.ModelTheory.WellOrdering`.

## Main definitions

* `Ordinal.boundedTypeSentence`: the disjunction of the Scott sentences of
  the ordinals below a countable ordinal.

## Main results

* `TauCeti.WellOrdersOfBoundedType.realize_boundedTypeSentence_iff_type_lt`: the countable linear
  models of `boundedTypeSentence α` are the well-orders of type below `α`.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, §4.4.
-/

public section

open FirstOrder FirstOrder.Language Structure Ordinal

universe w w'

namespace Ordinal

open TauCeti

/-! ### Disjunctions of Scott sentences of ordinals -/

/-- For a countable ordinal `α`, the disjunction over the ordinals `β < α` of the Scott sentences
of the well-orders `β`, in the language of orders. -/
noncomputable def boundedTypeSentence (α : Ordinal.{w}) (hα : α < ω₁) :
    Language.order.Sentenceω :=
  BoundedFormulaInf.iSupAlong
    (IndexCoding.ofEncodableWith (Cardinal.countable_Iio_of_lt_omega_one hα).toEncodable)
    fun β => ordinalScottSentence β.val (β.property.trans hα)

/-- The bounded-type sentence is the coded disjunction of the Scott sentences of the ordinals below
`α`. -/
theorem boundedTypeSentence_def (α : Ordinal.{w}) (hα : α < ω₁) :
    boundedTypeSentence α hα = BoundedFormulaInf.iSupAlong
      (IndexCoding.ofEncodableWith (Cardinal.countable_Iio_of_lt_omega_one hα).toEncodable)
      fun β => ordinalScottSentence β.val (β.property.trans hα) :=
  (rfl)

end Ordinal

namespace TauCeti.WellOrdersOfBoundedType

/-- A structure satisfies the disjunction of the Scott sentences of the ordinals below `α` exactly
when it satisfies one of them. -/
@[simp]
theorem realize_boundedTypeSentence {α : Ordinal.{w}} (hα : α < ω₁) (N : Type w')
    [Language.order.Structure N] :
    SentenceInf.Realize (boundedTypeSentence α hα) N ↔
      ∃ (β : Ordinal.{w}) (hβ : β < α),
        SentenceInf.Realize (ordinalScottSentence β (hβ.trans hα)) N := by
  simp only [boundedTypeSentence_def, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iSupAlong, Subtype.exists, Set.mem_Iio]

/-- **The countable models of `boundedTypeSentence α`.** A countable ordered structure, in any
universe, satisfies the disjunction of the Scott sentences of the ordinals below `α` exactly when
it is order-isomorphic to some ordinal `β < α`. -/
theorem realize_boundedTypeSentence_iff {α : Ordinal.{w}} (hα : α < ω₁) (N : Type w')
    [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N] [Countable N] :
    SentenceInf.Realize (boundedTypeSentence α hα) N ↔ ∃ β < α, Nonempty (β.ToType ≃o N) := by
  simp only [realize_boundedTypeSentence, realize_ordinalScottSentence_iff, exists_prop]

/-- **Well-orders of bounded type.** A countable linear order, in any universe, satisfies the
disjunction of the Scott sentences of the ordinals below `α` exactly when it is a well-order of
order type below `α`. -/
theorem realize_boundedTypeSentence_iff_type_lt {α : Ordinal.{w}} (hα : α < ω₁) (N : Type w')
    [Language.order.Structure N] [LinearOrder N] [Language.order.OrderedStructure N]
    [Countable N] :
    SentenceInf.Realize (boundedTypeSentence α hα) N ↔
      ∃ _ : WellFoundedLT N, lift.{w} (typeLT N) < lift.{w'} α := by
  rw [realize_boundedTypeSentence_iff]
  constructor
  · rintro ⟨β, hβ, ⟨e⟩⟩
    have : WellFoundedLT N := e.symm.strictMono.wellFoundedLT
    refine ⟨this, ?_⟩
    have h := lift_type_eq.{w, w', 0}.2 ⟨e.toRelIsoLT⟩
    rw [type_toType] at h
    rw [← h, lift_lt]
    exact hβ
  · rintro ⟨_, h⟩
    obtain ⟨β, hβ, hβN⟩ := lt_lift_iff.1 h
    rw [← type_toType β] at hβN
    obtain ⟨e⟩ := lift_type_eq.{w, w', 0}.1 hβN
    exact ⟨β, hβ, ⟨OrderIso.ofRelIsoLT e⟩⟩

/-- The ordinal `α` is not a model of `boundedTypeSentence α`: its order type is not below
itself. -/
theorem not_realize_boundedTypeSentence_self {α : Ordinal.{w}} (hα : α < ω₁) :
    letI := orderStructure α.ToType
    ¬SentenceInf.Realize (boundedTypeSentence α hα) α.ToType := by
  let := orderStructure α.ToType
  have := Cardinal.countable_toType_of_lt_omega_one hα
  rw [realize_boundedTypeSentence_iff_type_lt]
  rintro ⟨_, h⟩
  simp [type_toType] at h

end TauCeti.WellOrdersOfBoundedType
