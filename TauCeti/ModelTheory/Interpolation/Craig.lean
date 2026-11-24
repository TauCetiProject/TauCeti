/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Interpolation.PCClass
import TauCeti.ModelTheory.Interpolation.Lyndon

/-!
# Craig interpolation and projective-class separation for `L_{ω₁ω}`

López-Escobar's Craig interpolation theorem gives, for every valid entailment `φ ⊨ ψ` between
sentences of `L_{ω₁ω}`, an interpolant `θ` with `φ ⊨ θ` and `θ ⊨ ψ` whose occurring function and
relation symbols appear in both `φ` and `ψ` (with logical equality permitted freely in `θ`). This
file provides unsigned Craig interpolation for relational languages
(`craig_interpolation_relational`), arbitrary languages with function symbols
(`craig_interpolation`), and countable theories (`Theoryω.craig_interpolation`), deriving the
unsigned relation bounds from the polarity-sensitive Lyndon interpolation theorem of
`TauCeti.ModelTheory.Interpolation.Lyndon`.

From Craig interpolation in a sum language `L.sum (L₁.sum L₂)` together with downward
Löwenheim–Skolem (`Sentenceω.entails_iff_countable`), this file deduces projective-class
separation (`pcSeparation_entails` and `pcSeparation`): if two `PC_{ω₁ω}` classes over `L`, `L₁`,
`L₂` have no common countable nonempty member in `Type w₀`, a single `L_{ω₁ω}` sentence over `L`
separates them on nonempty structures of every cardinality and universe. As a consequence, any
`PC_{ω₁ω}` class whose countable complement is also `PC_{ω₁ω}` is the class of countable nonempty
models of a single `L_{ω₁ω}` sentence (`pcComplement_iff_realize`).

## Main results

* `FirstOrder.Language.craig_interpolation_relational`: relational Craig interpolation for
  `L_{ω₁ω}` sentences over a relational language of arbitrary cardinality.
* `FirstOrder.Language.craig_interpolation`: Craig interpolation for `L_{ω₁ω}` sentences over an
  arbitrary language, bounding both the function and the relation symbols of the interpolant.
* `FirstOrder.Language.Theoryω.craig_interpolation`: Craig interpolation for a countable theory
  `T` entailing a sentence `ψ`.
* `FirstOrder.Language.craig_pcSeparation`: separating the reducts of models of two mutually
  inconsistent sentences in their shared symbol sublanguage.
* `FirstOrder.Language.pcSeparation_entails` and `FirstOrder.Language.pcSeparation`:
  `PC_{ω₁ω}` separation from countable disjointness in `Type w₀` to arbitrary nonempty
  structures in `Type w`.
* `FirstOrder.Language.pcComplement_iff_realize`: a `PC_{ω₁ω}` class whose countable complement
  is also `PC_{ω₁ω}` is the class of countable nonempty models of a single `L_{ω₁ω}` sentence.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971, §4.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, §4.2.
* `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Methods/Interpolation/{Craig,PCSeparation,CraigArbitrary}.lean`. Divergences
  from that source: unsigned Craig interpolation is derived in arbitrary universes and for
  arbitrary-cardinality languages from Lyndon interpolation
  (`TauCeti.ModelTheory.Interpolation.Lyndon`), and projective-class separation is proved in sum
  form for arbitrary languages `L`, `L₁`, `L₂`, transferring countable disjointness in any
  universe `w₀` to nonempty models of arbitrary cardinality and universe `w`.
-/

public section

universe u v u₁ v₁ u₂ v₂ w₀ w w'

namespace FirstOrder.Language

open BoundedFormulaInf

/-! ### Craig interpolation -/

section Craig

variable {L : Language.{u, v}}

/-- **Relational Craig interpolation for `L_{ω₁ω}`.** In any relational language `L` (of any
cardinality and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an
`L_{ω₁ω}` sentence `θ` whose occurring relation symbols lie in `φ.relationsIn ∩ ψ.relationsIn`
such that `φ` entails `θ` and `θ` entails `ψ`. -/
theorem craig_interpolation_relational [L.IsRelational] (φ ψ : L.Sentenceω)
    (h : Sentenceω.Entails φ ψ) :
    ∃ θ : L.Sentenceω, θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
      Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ := by
  obtain ⟨θ, hpos, hneg, hφθ, hθψ⟩ := lyndon_interpolation_relational φ ψ h
  exact ⟨θ, relationsIn_subset_inter_of_relationsInSigned_subset hpos hneg, hφθ, hθψ⟩

/-- **Craig interpolation for `L_{ω₁ω}`.** In any language `L` (of any cardinality, with function
symbols, and in any universes), if an `L_{ω₁ω}` sentence `φ` entails `ψ`, there is an `L_{ω₁ω}`
sentence `θ` whose function symbols lie in `φ.functionsIn ∩ ψ.functionsIn` and whose relation
symbols lie in `φ.relationsIn ∩ ψ.relationsIn` such that `φ` entails `θ` and `θ` entails `ψ`.
Equality is logical, so `θ` may use it freely. -/
theorem craig_interpolation (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧ φ.Entails θ ∧ θ.Entails ψ := by
  obtain ⟨θ, hfun, hpos, hneg, hφθ, hθψ⟩ := lyndon_interpolation φ ψ h
  exact ⟨θ, hfun, relationsIn_subset_inter_of_relationsInSigned_subset hpos hneg, hφθ, hθψ⟩

/-- **Countable-theory Craig interpolation.** If a countable `L_{ω₁ω}` theory `T` entails `ψ`,
there is an interpolant `θ` whose occurring function and relation symbols appear both in some
sentence of `T` and in `ψ`, with `T ⊨ θ` and `θ ⊨ ψ`. -/
theorem Theoryω.craig_interpolation {T : L.Theoryω} (hT : T.Countable) (ψ : L.Sentenceω)
    (h : T.Entails ψ) :
    ∃ θ : L.Sentenceω, θ.functionsIn ⊆ (⋃ φ ∈ T, φ.functionsIn) ∩ ψ.functionsIn ∧
      θ.relationsIn ⊆ (⋃ φ ∈ T, φ.relationsIn) ∩ ψ.relationsIn ∧
      T.Entails θ ∧ Sentenceω.Entails θ ψ := by
  obtain ⟨θ, hfun, hrel, hTθ, hθψ⟩ := Language.craig_interpolation (T.conjunction hT) ψ
    ((Theoryω.entails_iff_conjunction_entails hT).1 h)
  refine ⟨θ, hfun.trans (Set.inter_subset_inter_left _ ?_),
    hrel.trans (Set.inter_subset_inter_left _ ?_),
    (Theoryω.entails_iff_conjunction_entails hT).2 hTθ, hθψ⟩
  · rw [Theoryω.conjunction_def, functionsIn_iInfAlong]
    exact Set.iUnion_subset fun φ => Set.subset_biUnion_of_mem φ.property
  · rw [Theoryω.conjunction_def, relationsIn_iInfAlong]
    exact Set.iUnion_subset fun φ => Set.subset_biUnion_of_mem φ.property

/-- **Projective-class separation from mutual inconsistency.** If `ψ₁ ⊨ ¬ψ₂`, some sentence `θ` of
the shared symbol sublanguage
`symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn) (ψ₁.relationsIn ∩ ψ₂.relationsIn)` holds in the
reduct of every nonempty model of `ψ₁` and fails in the reduct of every nonempty model of `ψ₂`,
across arbitrary universes `w` and `w'`. -/
theorem craig_pcSeparation (ψ₁ ψ₂ : L.Sentenceω) (h : Sentenceω.Entails ψ₁ ψ₂.not) :
    ∃ θ : (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
        (ψ₁.relationsIn ∩ ψ₂.relationsIn)).Sentenceω,
      (∀ (M : Type w) [L.Structure M] [Nonempty M], SentenceInf.Realize ψ₁ M →
        @SentenceInf.Realize _ ℕ θ M
          ((symbSublangIncl (ψ₁.functionsIn ∩ ψ₂.functionsIn)
            (ψ₁.relationsIn ∩ ψ₂.relationsIn)).reduct M)) ∧
      (∀ (M : Type w') [L.Structure M] [Nonempty M], SentenceInf.Realize ψ₂ M →
        ¬ @SentenceInf.Realize _ ℕ θ M
          ((symbSublangIncl (ψ₁.functionsIn ∩ ψ₂.functionsIn)
            (ψ₁.relationsIn ∩ ψ₂.relationsIn)).reduct M)) := by
  obtain ⟨θ₀, hfun, hrel, h₁, h₂⟩ := craig_interpolation ψ₁ ψ₂.not h
  rw [functionsIn_not] at hfun
  rw [relationsIn_not] at hrel
  refine ⟨θ₀.restrictSymbols hfun hrel, ?_, ?_⟩
  · intro M _ _ hM₁
    let : (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
        (ψ₁.relationsIn ∩ ψ₂.relationsIn)).Structure M :=
      (symbSublangIncl _ _).reduct M
    have hM := h₁.realize M hM₁
    rw [SentenceInf.realize_def, FormulaInf.realize_def] at hM ⊢
    exact (realize_restrictSymbols θ₀ hfun hrel Empty.elim default).2 hM
  · intro M _ _ hM₂ hθM
    let : (symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn)
        (ψ₁.relationsIn ∩ ψ₂.relationsIn)).Structure M :=
      (symbSublangIncl _ _).reduct M
    rw [SentenceInf.realize_def, FormulaInf.realize_def] at hθM
    exact SentenceInf.realize_not.1 (h₂.realize M <| by
      rw [SentenceInf.realize_def, FormulaInf.realize_def]
      exact (realize_restrictSymbols θ₀ hfun hrel Empty.elim default).1 hθM) hM₂

end Craig

/-! ### Projective-class separation -/

section PCSeparation

variable {L : Language.{u, v}} {L₁ : Language.{u₁, v₁}} {L₂ : Language.{u₂, v₂}}

/-- **Entailment form of `PC_{ω₁ω}` separation.** For arbitrary languages `L`, `L₁`, `L₂`, if no
countable nonempty `L`-structure in `Type w₀` lies in both `LHom.sumInl.PCMem Θ₁` and
`LHom.sumInl.PCMem Θ₂`, there is a single sentence `θ : L.Sentenceω` whose image in `L.sum L₁` is
entailed by `Θ₁` and whose negated image in `L.sum L₂` is entailed by `Θ₂`. -/
theorem pcSeparation_entails (Θ₁ : (L.sum L₁).Sentenceω) (Θ₂ : (L.sum L₂).Sentenceω)
    (h : ∀ (M : Type w₀) [L.Structure M] [Nonempty M] [Countable M],
      LHom.sumInl.PCMem Θ₁ M → ¬ LHom.sumInl.PCMem Θ₂ M) :
    ∃ θ : L.Sentenceω,
      Sentenceω.Entails Θ₁ (LHom.sumInl.onBoundedFormulaInf θ) ∧
      Sentenceω.Entails Θ₂ (LHom.sumInl.onBoundedFormulaInf θ).not := by
  let g₁ : L.sum L₁ →ᴸ L.sum (L₁.sum L₂) := (LHom.id L).sumMap LHom.sumInl
  let g₂ : L.sum L₂ →ᴸ L.sum (L₁.sum L₂) := (LHom.id L).sumMap LHom.sumInr
  have hg₁ : g₁.Injective :=
    ⟨fun h => (Function.injective_id.sumMap LHom.sumInl_injective.onFunction) h,
     fun h => (Function.injective_id.sumMap LHom.sumInl_injective.onRelation) h⟩
  have hg₂ : g₂.Injective :=
    ⟨fun h => (Function.injective_id.sumMap LHom.sumInr_injective.onFunction) h,
     fun h => (Function.injective_id.sumMap LHom.sumInr_injective.onRelation) h⟩
  let Θ₁' := g₁.onBoundedFormulaInf Θ₁
  let Θ₂' := g₂.onBoundedFormulaInf Θ₂
  have hent : Sentenceω.Entails Θ₁' Θ₂'.not := by
    rw [Sentenceω.entails_iff_countable.{_, _, w₀}]
    intro M _ _ _ hM₁
    refine SentenceInf.realize_not.2 fun hM₂ => ?_
    let : L.Structure M := (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)).reduct M
    obtain ⟨h₁, h₂⟩ := LHom.pcMem_sumInl_inf_iff.1
      (LHom.pcMem_of_isExpansionOn (SentenceInf.realize_inf.2 ⟨hM₁, hM₂⟩))
    exact h M h₁ h₂
  obtain ⟨θ', hfun, hrel, h₁, h₂⟩ := craig_interpolation Θ₁' Θ₂'.not hent
  rw [functionsIn_not, LHom.functionsIn_onBoundedFormulaInf,
    LHom.functionsIn_onBoundedFormulaInf] at hfun
  rw [relationsIn_not, LHom.relationsIn_onBoundedFormulaInf,
    LHom.relationsIn_onBoundedFormulaInf] at hrel
  obtain ⟨θ, hθ⟩ := LHom.exists_eq_onBoundedFormulaInf_of_subset_range
    (LHom.sumInl : L →ᴸ L.sum (L₁.sum L₂)) θ'
    (fun _ hs => LHom.mem_range_sumInl_onFunction_of_mem_range_sumMap
      (Set.mem_range_of_mem_image _ _ (hfun hs).1) (Set.mem_range_of_mem_image _ _ (hfun hs).2))
    (fun _ hs => LHom.mem_range_sumInl_onRelation_of_mem_range_sumMap
      (Set.mem_range_of_mem_image _ _ (hrel hs).1) (Set.mem_range_of_mem_image _ _ (hrel hs).2))
  have hcomp₁ : g₁.onBoundedFormulaInf (LHom.sumInl.onBoundedFormulaInf θ) = θ' := by
    rw [← LHom.comp_onBoundedFormulaInf, LHom.sumMap_comp_inl, LHom.comp_id, hθ]
  have hcomp₂ : g₂.onBoundedFormulaInf (LHom.sumInl.onBoundedFormulaInf θ) = θ' := by
    rw [← LHom.comp_onBoundedFormulaInf, LHom.sumMap_comp_inl, LHom.comp_id, hθ]
  refine ⟨θ, (Sentenceω.entails_onBoundedFormulaInf_iff hg₁).1 (hcomp₁ ▸ h₁),
    (Sentenceω.entails_onBoundedFormulaInf_iff hg₂).1 ?_⟩
  rw [LHom.onBoundedFormulaInf_not, hcomp₂]
  exact Sentenceω.entails_iff.2 fun M _ _ hM₂ =>
    SentenceInf.realize_not.2 fun hθ'M => SentenceInf.realize_not.1 (h₂.realize M hθ'M) hM₂

/-- **Projective-class separation.** For arbitrary languages `L`, `L₁`, `L₂` (of any cardinality,
with function symbols, and in any universes), if two `PC_{ω₁ω}` classes `LHom.sumInl.PCMem Θ₁` and
`LHom.sumInl.PCMem Θ₂` have no common countable nonempty member in `Type w₀`, there is a single
`L_{ω₁ω}` sentence `θ` over `L` that holds in every nonempty member of the first class and fails in
every nonempty member of the second class, in any universe `w`. -/
theorem pcSeparation (Θ₁ : (L.sum L₁).Sentenceω) (Θ₂ : (L.sum L₂).Sentenceω)
    (h : ∀ (M : Type w₀) [L.Structure M] [Nonempty M] [Countable M],
      LHom.sumInl.PCMem Θ₁ M → ¬ LHom.sumInl.PCMem Θ₂ M) :
    ∃ θ : L.Sentenceω,
      (∀ (M : Type w) [L.Structure M] [Nonempty M], LHom.sumInl.PCMem Θ₁ M →
        SentenceInf.Realize θ M) ∧
      (∀ (M : Type w) [L.Structure M] [Nonempty M], LHom.sumInl.PCMem Θ₂ M →
        ¬ SentenceInf.Realize θ M) := by
  obtain ⟨θ, h₁, h₂⟩ := pcSeparation_entails Θ₁ Θ₂ h
  refine ⟨θ, fun M _ _ hM => hM.realize_of_entails h₁, fun M _ _ hM => ?_⟩
  simpa only [SentenceInf.realize_not] using
    hM.realize_of_entails (φ := θ.not) (by simpa using h₂)

/-- **Suslin–Kleene characterization for `PC_{ω₁ω}` classes.** If every countable nonempty
`L`-structure in `Type w₀` lies in exactly one of `LHom.sumInl.PCMem Θ₁` and
`LHom.sumInl.PCMem Θ₂`, then `LHom.sumInl.PCMem Θ₁` on countable nonempty structures is the model
class of a single `L_{ω₁ω}` sentence `θ`. -/
theorem pcComplement_iff_realize (Θ₁ : (L.sum L₁).Sentenceω) (Θ₂ : (L.sum L₂).Sentenceω)
    (h : ∀ (M : Type w₀) [L.Structure M] [Nonempty M] [Countable M],
      LHom.sumInl.PCMem Θ₁ M ↔ ¬ LHom.sumInl.PCMem Θ₂ M) :
    ∃ θ : L.Sentenceω, ∀ (M : Type w₀) [L.Structure M] [Nonempty M] [Countable M],
      LHom.sumInl.PCMem Θ₁ M ↔ SentenceInf.Realize θ M := by
  obtain ⟨θ, h₁, h₂⟩ := pcSeparation.{u, v, u₁, v₁, u₂, v₂, w₀, w₀} Θ₁ Θ₂
    fun M _ _ _ hM₁ => (h M).1 hM₁
  exact ⟨θ, fun M _ _ _ => ⟨h₁ M, fun hθM => by_contra fun hM₁ => h₂ M ((h M).not_left.1 hM₁) hθM⟩⟩

end PCSeparation

end FirstOrder.Language
