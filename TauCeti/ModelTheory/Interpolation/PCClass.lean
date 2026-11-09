/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.LanguageMap
public import TauCeti.ModelTheory.ModelExistence.CountableModel

/-!
# Projective classes of `L_{ω₁ω}` sentences

For a language map `g : L →ᴸ L'` and an `L'`-sentence `Θ`, an `L`-structure `M` lies in the
projective class of `Θ` along `g` when `M` itself, on the same carrier, expands along `g` to a
model of `Θ`. These are Marker's `PC_{ω₁ω}` classes: the classes of `L`-structures obtained from the
models of an `L_{ω₁ω}` sentence by forgetting the symbols outside `L`. No nonemptiness is built in.
They are the classes separated by a single `L`-sentence in the PC separation theorem, which in turn
gives the hard direction of the López-Escobar theorem.

This file gives the basic closure properties. Every class of models of an `L`-sentence is
projective, along the identity. Projective classes are invariant under isomorphism. A projective
class, along `h`, of the expansions in a projective class along `g` is projective along
`h.comp g`. Projective classes along `LHom.sumInl : L →ᴸ L.sum L₁` are closed under binary
intersection and union: the two vocabularies `L₁` and `L₂` are kept apart in
`L.sum (L₁.sum L₂)`, even when `L₁ = L₂`, and the two sentences are translated into it along
`(LHom.id L).sumMap LHom.sumInl` and `(LHom.id L).sumMap LHom.sumInr`. For the union, a structure
in one class must still interpret the symbols of the other vocabulary; this is possible on a
nonempty carrier, and on every carrier for relational vocabularies.

## Main definitions

* `FirstOrder.Language.LHom.PCMem`: membership in the projective class of a sentence along a
  language map.

## Main results

* `FirstOrder.Language.LHom.pcMem_id_iff`: the projective class of an `L`-sentence along the
  identity is its class of models.
* `FirstOrder.Language.LHom.PCMem.realize_of_entails`: a nonempty member of the projective class
  of `Θ` along `g` satisfies every `L`-sentence whose image `Θ` entails.
* `FirstOrder.Language.StrongHomClass.pcMem_iff`: isomorphic structures lie in the same projective
  classes.
* `FirstOrder.Language.LHom.pcMem_comp_iff`: projective classes compose along composite language
  maps.
* `FirstOrder.Language.LHom.pcMem_sumInl_inf_iff`,
  `FirstOrder.Language.LHom.pcMem_sumInl_sup_iff`: projective classes along `LHom.sumInl` are
  closed under binary intersection and union.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, Chapter 4 (`PC_{ω₁ω}` classes and their separation).
* The definition of `PCMem` follows `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/ModelTheory/PCClass.lean`, which
  has only the definition. It is placed in the `LHom` namespace here, so that `g.PCMem Θ M` reads
  along the language map; the closure properties are new.
-/

public section

universe u v u' v' u'' v'' u₁ v₁ u₂ v₂ w w'

namespace FirstOrder

namespace Language

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}

/-- **Projective-class membership.** The `L`-structure `M` lies in the projective class of the
`L'`-sentence `Θ` along `g : L →ᴸ L'` when `M` itself, on the same carrier, carries an
`L'`-structure that expands it along `g` and satisfies `Θ`. No nonemptiness is built in. -/
def PCMem (g : L →ᴸ L') (Θ : L'.Sentenceω) (M : Type w) [L.Structure M] : Prop :=
  ∃ S : L'.Structure M, @IsExpansionOn L L' g M _ S ∧ @SentenceInf.Realize L' ℕ Θ M S

variable {g : L →ᴸ L'} {Θ : L'.Sentenceω} {M : Type w} [iM : L.Structure M]

/-- Unfolding `PCMem`: an expansion of `M` along `g` satisfying `Θ`. -/
theorem pcMem_iff : g.PCMem Θ M ↔
    ∃ S : L'.Structure M, @IsExpansionOn L L' g M _ S ∧ @SentenceInf.Realize L' ℕ Θ M S :=
  Iff.rfl

/-- A structure whose given expansion along `g` satisfies `Θ` lies in the projective class of
`Θ`. -/
theorem pcMem_of_isExpansionOn [L'.Structure M] [g.IsExpansionOn M]
    (h : SentenceInf.Realize Θ M) : g.PCMem Θ M :=
  ⟨_, inferInstance, h⟩

/-- A nonempty member of the projective class of `Θ` along `g` satisfies every `L`-sentence `φ`
whose image along `g` is entailed by `Θ`. The structure may have any cardinality and lie in any
universe. -/
theorem PCMem.realize_of_entails [Nonempty M] (h : g.PCMem Θ M) {φ : L.Sentenceω}
    (hφ : Θ.Entails (g.onBoundedFormulaInf φ)) : SentenceInf.Realize φ M := by
  obtain ⟨S, _, hΘ⟩ := h
  exact (realize_sentenceInf_onBoundedFormulaInf g φ).1 (hφ.realize M hΘ)

/-- **Model classes are projective.** The projective class of an `L`-sentence along the identity
is its class of models. -/
@[simp]
theorem pcMem_id_iff {Θ : L.Sentenceω} : (LHom.id L).PCMem Θ M ↔ SentenceInf.Realize Θ M := by
  refine ⟨fun ⟨S, hS, hΘ⟩ => ?_, pcMem_of_isExpansionOn⟩
  have := @realize_sentenceInf_onBoundedFormulaInf L L ℕ (LHom.id L) M iM S hS Θ
  rw [id_onBoundedFormulaInf] at this
  exact this.1 hΘ

/-- If the expansion of `M` along `h.comp g` satisfies the image of `Θ` along `h`, then `M` lies
in the projective class of `Θ` along `g`, witnessed by the reduct along `h`. -/
theorem pcMem_of_comp {h : L' →ᴸ L''} [L''.Structure M]
    [(h.comp g).IsExpansionOn M] (hΘ : SentenceInf.Realize (h.onBoundedFormulaInf Θ) M) :
    g.PCMem Θ M := by
  let : L'.Structure M := h.reduct M
  exact ⟨_, isExpansionOn_reduct_of_comp h g M, (realize_sentenceInf_onBoundedFormulaInf h Θ).1 hΘ⟩

/-- **Composition of projective classes.** `M` lies in the projective class of
`h(Θ) ∧ Θ'` along `h.comp g` exactly when it has an expansion `S` along `g` satisfying `Θ` that
itself lies in the projective class of `Θ'` along `h`. -/
theorem pcMem_comp_iff {h : L' →ᴸ L''} {Θ' : L''.Sentenceω} :
    (h.comp g).PCMem (h.onBoundedFormulaInf Θ ⊓ Θ') M ↔
      ∃ S : L'.Structure M, @IsExpansionOn L L' g M _ S ∧ @SentenceInf.Realize L' ℕ Θ M S ∧
        @PCMem L' L'' h Θ' M S := by
  constructor
  · rintro ⟨T, hT, hΘ⟩
    rw [SentenceInf.realize_inf] at hΘ
    let : L'.Structure M := h.reduct M
    exact ⟨_, isExpansionOn_reduct_of_comp h g M,
      (realize_sentenceInf_onBoundedFormulaInf h Θ).1 hΘ.1, pcMem_of_isExpansionOn hΘ.2⟩
  · rintro ⟨S, hS, hΘ, T, hT, hΘ'⟩
    refine ⟨T, inferInstance, SentenceInf.realize_inf.2
      ⟨(realize_sentenceInf_onBoundedFormulaInf h Θ).2 hΘ, hΘ'⟩⟩

section Sum

variable {L₁ : Language.{u₁, v₁}} {L₂ : Language.{u₂, v₂}}

/-- Expansions `S₁` and `S₂` of `M` along `sumInl` to `L.sum L₁` and to `L.sum L₂` combine into one
expansion `T` to `L.sum (L₁.sum L₂)`, in which the image of an `L.sum L₁`-sentence along
`(id L).sumMap sumInl` holds exactly when the sentence holds in `S₁`, and likewise for `S₂`. -/
private theorem exists_isExpansionOn_sumInl_sum (S₁ : (L.sum L₁).Structure M)
    (hS₁ : @IsExpansionOn L (L.sum L₁) LHom.sumInl M iM S₁) (S₂ : (L.sum L₂).Structure M)
    (hS₂ : @IsExpansionOn L (L.sum L₂) LHom.sumInl M iM S₂) :
    ∃ T : (L.sum (L₁.sum L₂)).Structure M, @IsExpansionOn L _ LHom.sumInl M iM T ∧
      (∀ Θ₁ : (L.sum L₁).Sentenceω,
        @SentenceInf.Realize _ ℕ (((LHom.id L).sumMap LHom.sumInl).onBoundedFormulaInf Θ₁) M T ↔
          @SentenceInf.Realize _ ℕ Θ₁ M S₁) ∧
      ∀ Θ₂ : (L.sum L₂).Sentenceω,
        @SentenceInf.Realize _ ℕ (((LHom.id L).sumMap LHom.sumInr).onBoundedFormulaInf Θ₂) M T ↔
          @SentenceInf.Realize _ ℕ Θ₂ M S₂ := by
  let : L₁.Structure M := @LHom.reduct L₁ (L.sum L₁) LHom.sumInr M S₁
  let : L₂.Structure M := @LHom.reduct L₂ (L.sum L₂) LHom.sumInr M S₂
  have := @id_isExpansionOn_reduct L (L.sum L₁) LHom.sumInl M iM S₁ hS₁
  have := @id_isExpansionOn_reduct L (L.sum L₂) LHom.sumInl M iM S₂ hS₂
  have := sumMap_isExpansionOn_of_reduct (LHom.id L) (LHom.sumInl : L₁ →ᴸ L₁.sum L₂) M
  have := sumMap_isExpansionOn_of_reduct (LHom.id L) (LHom.sumInr : L₂ →ᴸ L₁.sum L₂) M
  exact ⟨_, inferInstance, fun Θ₁ => realize_sentenceInf_onBoundedFormulaInf _ Θ₁,
    fun Θ₂ => realize_sentenceInf_onBoundedFormulaInf _ Θ₂⟩

/-- A structure in the projective class, along `sumInl : L →ᴸ L.sum L₁'`, of the image of `Θ₁`
along `(id L).sumMap ψ` lies in the projective class of `Θ₁` along `sumInl : L →ᴸ L.sum L₁`. -/
private theorem pcMem_of_pcMem_sumInl_sumMap {L₁' : Language.{u'', v''}} {ψ : L₁ →ᴸ L₁'}
    {Θ₁ : (L.sum L₁).Sentenceω}
    (h : (LHom.sumInl : L →ᴸ L.sum L₁').PCMem (((LHom.id L).sumMap ψ).onBoundedFormulaInf Θ₁) M) :
    (LHom.sumInl : L →ᴸ L.sum L₁).PCMem Θ₁ M := by
  obtain ⟨T, hT, hΘ⟩ := h
  have : (((LHom.id L).sumMap ψ).comp (LHom.sumInl : L →ᴸ L.sum L₁)).IsExpansionOn M := by
    rw [sumMap_comp_inl, comp_id]; exact hT
  exact pcMem_of_comp hΘ

/-- **Intersection of projective classes.** A structure lies in the projective classes of
`Θ₁ : Sentenceω (L.sum L₁)` and `Θ₂ : Sentenceω (L.sum L₂)` exactly when it lies in the projective
class of the conjunction of their images in `L.sum (L₁.sum L₂)`, where the new symbols of `L₁`
and `L₂` are kept apart. -/
theorem pcMem_sumInl_inf_iff {Θ₁ : (L.sum L₁).Sentenceω} {Θ₂ : (L.sum L₂).Sentenceω} :
    (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).PCMem
        (((LHom.id L).sumMap LHom.sumInl).onBoundedFormulaInf Θ₁ ⊓
          ((LHom.id L).sumMap LHom.sumInr).onBoundedFormulaInf Θ₂) M ↔
      (LHom.sumInl : L →ᴸ L.sum L₁).PCMem Θ₁ M ∧ (LHom.sumInl : L →ᴸ L.sum L₂).PCMem Θ₂ M := by
  constructor
  · rintro ⟨T, hT, hΘ⟩
    rw [SentenceInf.realize_inf] at hΘ
    exact ⟨pcMem_of_pcMem_sumInl_sumMap ⟨T, hT, hΘ.1⟩, pcMem_of_pcMem_sumInl_sumMap ⟨T, hT, hΘ.2⟩⟩
  · rintro ⟨⟨S₁, hS₁, hΘ₁⟩, ⟨S₂, hS₂, hΘ₂⟩⟩
    obtain ⟨T, hT, h₁, h₂⟩ := exists_isExpansionOn_sumInl_sum S₁ hS₁ S₂ hS₂
    exact ⟨T, hT, SentenceInf.realize_inf.2 ⟨(h₁ Θ₁).2 hΘ₁, (h₂ Θ₂).2 hΘ₂⟩⟩

/-- **Union of projective classes.** If `M` carries some `L₁`-structure and some `L₂`-structure,
it lies in the projective class of `Θ₁ : Sentenceω (L.sum L₁)` or of `Θ₂ : Sentenceω (L.sum L₂)`
exactly when it lies in the projective class of the disjunction of their images in
`L.sum (L₁.sum L₂)`. Both structures exist when `M` is nonempty
(`nonempty_structure_of_nonempty`) and, on every carrier, when `L₁` and `L₂` are relational
(`nonempty_structure_of_isRelational`). -/
theorem pcMem_sumInl_sup_iff [Nonempty (L₁.Structure M)] [Nonempty (L₂.Structure M)]
    {Θ₁ : (L.sum L₁).Sentenceω} {Θ₂ : (L.sum L₂).Sentenceω} :
    (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).PCMem
        (((LHom.id L).sumMap LHom.sumInl).onBoundedFormulaInf Θ₁ ⊔
          ((LHom.id L).sumMap LHom.sumInr).onBoundedFormulaInf Θ₂) M ↔
      (LHom.sumInl : L →ᴸ L.sum L₁).PCMem Θ₁ M ∨ (LHom.sumInl : L →ᴸ L.sum L₂).PCMem Θ₂ M := by
  constructor
  · rintro ⟨T, hT, hΘ⟩
    rcases SentenceInf.realize_sup.1 hΘ with hΘ | hΘ
    · exact .inl (pcMem_of_pcMem_sumInl_sumMap ⟨T, hT, hΘ⟩)
    · exact .inr (pcMem_of_pcMem_sumInl_sumMap ⟨T, hT, hΘ⟩)
  · rintro (⟨S₁, hS₁, hΘ₁⟩ | ⟨S₂, hS₂, hΘ₂⟩)
    · -- interpret the symbols of `L₂` by any `L₂`-structure on `M`
      let : L₂.Structure M := Classical.arbitrary _
      obtain ⟨T, hT, h₁, -⟩ :=
        exists_isExpansionOn_sumInl_sum S₁ hS₁ (sumStructure L L₂ M) inferInstance
      exact ⟨T, hT, SentenceInf.realize_sup.2 (.inl ((h₁ Θ₁).2 hΘ₁))⟩
    · let : L₁.Structure M := Classical.arbitrary _
      obtain ⟨T, hT, -, h₂⟩ :=
        exists_isExpansionOn_sumInl_sum (sumStructure L L₁ M) inferInstance S₂ hS₂
      exact ⟨T, hT, SentenceInf.realize_sup.2 (.inr ((h₂ Θ₂).2 hΘ₂))⟩

end Sum

end LHom

namespace StrongHomClass

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {g : L →ᴸ L'} {Θ : L'.Sentenceω}
  {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- An isomorphism carries an expansion of its domain to the induced expansion of its codomain. -/
private theorem pcMem_of_equiv (e : M ≃[L] N) (h : g.PCMem Θ M) : g.PCMem Θ N := by
  obtain ⟨S, hS, hΘ⟩ := h
  let : L'.Structure N := e.toEquiv.inducedStructure
  refine ⟨_, ⟨fun {n} f x => ?_, fun {n} R x => ?_⟩, ?_⟩
  · simp only [Equiv.inducedStructure_funMap, LHom.map_onFunction]
    exact (e.map_fun f _).trans (congrArg _ (funext fun i => e.apply_symm_apply (x i)))
  · simp only [Equiv.inducedStructure_RelMap, LHom.map_onRelation]
    exact propext ((e.map_rel R _).symm.trans
      (iff_of_eq (congrArg _ (funext fun i => e.apply_symm_apply (x i)))))
  · exact (realize_sentenceInf e.toEquiv.inducedStructureEquiv Θ).1 hΘ

/-- **Isomorphism invariance of projective classes.** Isomorphic `L`-structures lie in the same
projective classes. -/
theorem pcMem_iff {F : Type*} [EquivLike F M N] [StrongHomClass L F M N] (e : F) :
    g.PCMem Θ M ↔ g.PCMem Θ N :=
  ⟨pcMem_of_equiv (StrongHomClass.toEquiv e), pcMem_of_equiv (StrongHomClass.toEquiv e).symm⟩

end StrongHomClass

end Language

end FirstOrder
