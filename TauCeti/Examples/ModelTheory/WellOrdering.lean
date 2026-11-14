/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import TauCeti.ModelTheory.Infinitary.Semantics
public import TauCeti.ModelTheory.Order
import TauCeti.ModelTheory.Infinitary.Theory
import TauCeti.ModelTheory.Scott.Isomorphism
import TauCeti.ModelTheory.WellOrdering

/-!
# Well-orders of bounded type

For a countable ordinal `α`, the countable disjunction over `β < α` of the Scott sentences of the
well-orders `β` is an `L_{ω₁ω}` sentence in the language of orders whose countable models are
exactly the well-orders of order type below `α`. So every countable bound on order types is
expressed by a single sentence, and the ordinal `α` itself is not a model. This is consistent with
`Sentenceω.wellOrder_type_boundedness`, which bounds the order types of the models of any sentence
all of whose models are well-ordered.

No single sentence covers all countable well-orders. A sentence of the language of orders that holds
in every countable ordinal also holds in a countable linear order that is not well-founded, so no
sentence has as its countable linear models exactly the countable well-orders. This is the
`L_{ω₁ω}` counterpart of `TauCeti.exists_countable_model_not_wellFoundedLT` for first-order
theories. It is derived from Marker's chain theorem `Sentenceω.exists_model_relChain_rat`, applied
in the language with a second binary symbol read as the strict order: a chain for the symbol `≤`
itself could be constant.

## Main definitions

* `TauCeti.WellOrdersOfBoundedType.boundedTypeSentence`: the disjunction of the Scott sentences of
  the ordinals below a countable ordinal.

## Main results

* `TauCeti.WellOrdersOfBoundedType.realize_boundedTypeSentence_iff_type_lt`: the countable linear
  models of `boundedTypeSentence α` are the well-orders of type below `α`.
* `TauCeti.WellOrdersOfBoundedType.exists_countable_realize_not_wellFoundedLT`: a sentence true in
  every countable ordinal is true in a countable linear order that is not well-founded.
* `TauCeti.WellOrdersOfBoundedType.not_exists_sentenceω_realize_iff_wellFoundedLT`: no sentence
  defines the countable well-orders among the countable linear orders.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, §4.4.
-/

public section

open FirstOrder FirstOrder.Language Structure Ordinal

universe w w'

namespace TauCeti.WellOrdersOfBoundedType

/-! ### Disjunctions of Scott sentences of ordinals -/

/-- The Scott sentence of a countable ordinal `β`, as a well-order in the language of orders. -/
noncomputable def ordinalScottSentence (β : Ordinal.{w}) (hβ : β < ω₁) :
    Language.order.Sentenceω :=
  letI := orderStructure β.ToType
  have := Cardinal.countable_toType_of_lt_omega_one hβ
  scottSentence (L := Language.order) β.ToType

/-- The Scott sentence of a countable ordinal `β` holds in a countable ordered structure, in any
universe, exactly when that structure is order-isomorphic to `β`. -/
@[simp]
theorem realize_ordinalScottSentence_iff {β : Ordinal.{w}} (hβ : β < ω₁) (N : Type w')
    [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N] [Countable N] :
    SentenceInf.Realize (ordinalScottSentence β hβ) N ↔ Nonempty (β.ToType ≃o N) := by
  let := orderStructure β.ToType
  have := Cardinal.countable_toType_of_lt_omega_one hβ
  rw [ordinalScottSentence, realize_scottSentence_iff]
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ⟨StrongHomClass.toEquiv e⟩⟩
  let := StrongHomClass.toOrderIsoClass Language.order β.ToType N (β.ToType ≃[Language.order] N)
  exact ⟨OrderIso.ofClass e⟩

/-- For a countable ordinal `α`, the disjunction over the ordinals `β < α` of the Scott sentences
of the well-orders `β`, in the language of orders. -/
noncomputable def boundedTypeSentence (α : Ordinal.{w}) (hα : α < ω₁) :
    Language.order.Sentenceω :=
  BoundedFormulaInf.iSupAlong
    (IndexCoding.ofEncodableWith (Cardinal.countable_Iio_of_lt_omega_one hα).toEncodable)
    fun β => ordinalScottSentence β.1 (β.2.trans hα)

/-- **The countable models of `boundedTypeSentence α`.** A countable ordered structure, in any
universe, satisfies the disjunction of the Scott sentences of the ordinals below `α` exactly when
it is order-isomorphic to some ordinal `β < α`. -/
theorem realize_boundedTypeSentence_iff {α : Ordinal.{w}} (hα : α < ω₁) (N : Type w')
    [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N] [Countable N] :
    SentenceInf.Realize (boundedTypeSentence α hα) N ↔ ∃ β < α, Nonempty (β.ToType ≃o N) := by
  simp only [boundedTypeSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iSupAlong]
  simp only [← FormulaInf.realize_def, ← SentenceInf.realize_def,
    realize_ordinalScottSentence_iff]
  exact ⟨fun ⟨β, h⟩ => ⟨β.1, β.2, h⟩, fun ⟨β, hβ, h⟩ => ⟨⟨β, hβ⟩, h⟩⟩

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

/-! ### No sentence defines the countable well-orders -/

/-- The language of orders with a second binary symbol, read as the strict order. -/
private abbrev LtLang : Language := Language.order.sum Language.order

/-- The strict-order symbol of `LtLang`. -/
private noncomputable abbrev ltRel : LtLang.Relations 2 := Sum.inl .le

/-- The structure on an ordered type in `LtLang` reading the first symbol as `<` and the second
as `≤`. -/
private noncomputable abbrev ltLeStructure (M : Type w) [LE M] [LT M] : LtLang.Structure M :=
  @sumStructure _ _ M (@orderStructure M ⟨fun x y => x < y⟩) (orderStructure M)

/-- The sentence saying that the strict-order symbol is the strict part of the order symbol. -/
private noncomputable def ltAxiom : LtLang.Sentence :=
  ∀' ∀' (ltRel.boundedFormula₂ &0 &1).iff
    ((leSymb : LtLang.Relations 2).boundedFormula₂ &0 &1 ⊓
      ∼((leSymb : LtLang.Relations 2).boundedFormula₂ &1 &0))

/-- A structure satisfies `ltAxiom` when its strict-order symbol is the strict part of its order
symbol. -/
private theorem realize_ltAxiom {M : Type w} [LtLang.Structure M] :
    M ⊨ ltAxiom ↔ ∀ x y : M, RelMap ltRel ![x, y] ↔
      RelMap (leSymb : LtLang.Relations 2) ![x, y] ∧
        ¬RelMap (leSymb : LtLang.Relations 2) ![y, x] := by
  simp [ltAxiom, Sentence.Realize, Formula.Realize, BoundedFormula.realize_rel₂, Fin.snoc]

/-- The theory of linear orders is countable. -/
private theorem countable_linearOrderTheory :
    (BoundedFormula.toOmega '' Language.order.linearOrderTheory).Countable :=
  (Set.Finite.countable (by simp [linearOrderTheory, partialOrderTheory, preorderTheory])).image _

/-- The sentence of `LtLang` saying that `φ` holds of the order symbol, which is a linear order, and
that the strict-order symbol is its strict part. -/
private noncomputable def chainSentence (φ : Language.order.Sentenceω) : LtLang.Sentenceω :=
  LHom.sumInr.onBoundedFormulaInf
      (φ ⊓ Theoryω.conjunction _ countable_linearOrderTheory) ⊓
    ltAxiom.toOmega

/-- A linear order satisfying `φ`, with the strict-order symbol read as `<`, satisfies
`chainSentence φ`. -/
private theorem realize_chainSentence (φ : Language.order.Sentenceω) (M : Type w)
    [LinearOrder M] (hφ : letI := orderStructure M; SentenceInf.Realize φ M) :
    letI := ltLeStructure M
    SentenceInf.Realize (chainSentence φ) M := by
  let := orderStructure M
  let := ltLeStructure M
  have := @LHom.sumInr_isExpansionOn _ _ M (@orderStructure M ⟨fun x y => x < y⟩)
    (orderStructure M)
  simp only [chainSentence, SentenceInf.realize_def,
    FormulaInf.realize_def, LHom.realize_onBoundedFormulaInf, BoundedFormulaInf.realize_inf]
  simp only [← FormulaInf.realize_def (M := M), ← SentenceInf.realize_def,
    Theoryω.realize_conjunction_iff, Theoryω.model_image_toOmega_iff, Sentence.realize_toInf,
    realize_ltAxiom]
  -- `ltLeStructure` reads its two symbols as `<` and `≤` by definition
  exact ⟨⟨hφ, inferInstance⟩, fun x y => lt_iff_le_not_ge⟩

/-- **A sentence true in all countable ordinals has a non-well-ordered countable model.** A
sentence of the language of orders that holds in every countable ordinal also holds in a countable
linear order, in any universe, that is not well-founded. -/
theorem exists_countable_realize_not_wellFoundedLT (φ : Language.order.Sentenceω)
    (hφ : ∀ β : Ordinal.{w}, β < ω₁ →
      letI := orderStructure β.ToType
      SentenceInf.Realize φ β.ToType) :
    ∃ (N : Type w') (_ : Language.order.Structure N) (_ : LinearOrder N)
      (_ : Language.order.OrderedStructure N),
        Countable N ∧ SentenceInf.Realize φ N ∧ ¬WellFoundedLT N := by
  classical
  -- the models `(γ + 1, <, ≤)` carry chains indexed by every countable ordinal `γ`
  have hch : Sentenceω.HasWellOrderedChains.{0, 0, w} (chainSentence φ) ltRel := by
    refine Sentenceω.hasWellOrderedChains_iff.2 fun γ hγ => ?_
    have hγ' := (Cardinal.isSuccLimit_omega 1).add_one_lt hγ
    let M := (γ + 1).ToType
    let := ltLeStructure M
    refine ⟨M, inferInstance, nonempty_toType_iff.2 (by simp),
      realize_chainSentence φ M (hφ _ hγ'),
      fun a => ToType.mk ⟨(ToType.toOrd a).1, (ToType.toOrd a).2.trans_le (Order.le_succ γ)⟩,
      relChain_iff.2 fun x y hxy => ?_⟩
    exact ToType.mk.strictMono (Subtype.mk_lt_mk.2 (ToType.mk.symm.strictMono hxy))
  -- so some countable model carries an `ltRel`-chain indexed by `ℚ`
  obtain ⟨N, _, -, hc, hN, f, hf⟩ := Sentenceω.exists_model_relChain_rat.{0, 0, w, w'} hch
  let := (LHom.sumInr : Language.order →ᴸ LtLang).reduct N
  simp only [chainSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    LHom.realize_onBoundedFormulaInf, BoundedFormulaInf.realize_inf] at hN
  simp only [← FormulaInf.realize_def (M := N), ← SentenceInf.realize_def,
    Theoryω.realize_conjunction_iff, Theoryω.model_image_toOmega_iff, Sentence.realize_toInf,
    realize_ltAxiom] at hN
  obtain ⟨⟨hNφ, hlin⟩, hlt⟩ := hN
  let := Language.order.linearOrderOfModels N
  refine ⟨N, inferInstance, inferInstance, inferInstance, hc, hNφ, fun _ => ?_⟩
  -- the chain is increasing for `<`, which is well-founded; the order of `linearOrderOfModels` is
  -- the order symbol, read in the reduct, by definition
  refine hf.not_wellFounded (Subrelation.wf (fun {x y} hxy => ?_) wellFounded_lt)
  exact lt_iff_le_not_ge.2 ((hlt x y).1 hxy)

/-- **Undefinability of countable well-orders.** No `L_{ω₁ω}` sentence of the language of orders
holds in exactly the well-founded ones among the countable linear orders. -/
theorem not_exists_sentenceω_realize_iff_wellFoundedLT :
    ¬∃ φ : Language.order.Sentenceω, ∀ (M : Type w) [Language.order.Structure M] [LinearOrder M]
      [Language.order.OrderedStructure M] [Countable M],
        SentenceInf.Realize φ M ↔ WellFoundedLT M := by
  rintro ⟨φ, hφ⟩
  obtain ⟨N, _, _, _, _, hN, hwf⟩ := exists_countable_realize_not_wellFoundedLT.{w, w} φ
    fun β hβ =>
      letI := orderStructure β.ToType
      have := Cardinal.countable_toType_of_lt_omega_one hβ
      (hφ β.ToType).2 inferInstance
  exact hwf ((hφ N).1 hN)

end TauCeti.WellOrdersOfBoundedType
