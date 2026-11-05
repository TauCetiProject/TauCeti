/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Polarity
public import TauCeti.ModelTheory.Infinitary.GraphTranslation.BackTranslate
public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Reconstruct

/-!
# Signed relation occurrences across the graph translation

This file tracks syntactic relation polarity (`BoundedFormulaInf.relationsInSigned`) across the
graph translation (`BoundedFormulaInf.relationalize`), the back-translation
(`BoundedFormulaInf.backTranslate`), and the graph axioms (`graphAxioms`).

A term graph `t.graphFormula ρ y` uses only equality, positive graph-relation atoms `G_f`, finite
conjunctions, and existential quantifiers, so its positive occurrences are the graph relations of
`t.functionsIn` and it has no negative occurrences. Consequently, `φ.relationalize` preserves base
relation occurrences with their exact polarity
(`BoundedFormulaInf.preimage_baseRelSym_relationsInSigned_relationalize`) and introduces only graph
relations of `φ.functionsIn` (`BoundedFormulaInf.relationsInSigned_relationalize_subset`). In the
reverse direction, `BoundedFormulaInf.backTranslate` turns graph-relation atoms into equations, so
its signed relation occurrences are the base preimage of those of its input
(`BoundedFormulaInf.relationsInSigned_backTranslate`).

In the graph axioms of a function symbol `f`, totality `∀ xs, ∃ y, G_f(xs, y)` contributes `G_f`
positively and functionality `∀ xs y z, G_f(xs, y) → G_f(xs, z) → y = z` contributes `G_f`
negatively. Hence `graphAxioms F` and its countable conjunction `(graphAxioms F).conjunction hF`
have signed relation occurrences equal to `relSym F ∅` at *both* polarities. Adjoining
`(graphAxioms F).conjunction hF` to `φ.relationalize`, either conjunctively (as in the premise of a
translated entailment) or implicatively (as in the conclusion), therefore yields the exact signed
occurrence identity `relSym F (φ.relationsInSigned s)` whenever `φ.functionsIn ⊆ F`. Combined with
`relSym_inter` and `BoundedFormulaInf.relationsInSigned_backTranslate`, this reduces Lyndon
interpolation for arbitrary languages to Lyndon interpolation for relational languages.

## Main results

* `FirstOrder.Language.Term.relationsInSigned_graphFormula`: signed relation occurrences of a term
  graph.
* `FirstOrder.Language.BoundedFormulaInf.preimage_baseRelSym_relationsInSigned_relationalize` and
  `FirstOrder.Language.BoundedFormulaInf.relationsInSigned_relationalize_subset`: exact base-symbol
  polarity preservation and upper bound for `relationalize`.
* `FirstOrder.Language.BoundedFormulaInf.relationsInSigned_backTranslate`: exact signed occurrence
  calculus of `backTranslate`.
* `FirstOrder.Language.relationsInSigned_graphAxioms`,
  `FirstOrder.Language.relationsInSigned_conjunction_graphAxioms`,
  `FirstOrder.Language.relationsInSigned_conjunction_graphAxioms_inf_relationalize`, and
  `FirstOrder.Language.relationsInSigned_conjunction_graphAxioms_imp_relationalize`: signed
  occurrences of the graph axioms and of graph-translated premises and conclusions.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapter 4.
* Adapted from `InfinitaryLogic/Methods/Interpolation/LyndonRelationalize.lean` in
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`.
  Divergences from that source: languages and variables live in arbitrary universes,
  `relationsInSigned_backTranslate` holds at every branching carrier `ι`, and the exact signed
  occurrence equalities for `(graphAxioms F).conjunction hF` paired with `φ.relationalize` are
  isolated as standalone lemmas.
-/

public section

universe u v u' uι uβ

namespace FirstOrder.Language

variable {L : Language.{u, v}} {α : Type u'}

namespace Term

variable {β : Type uβ}

/-- A term graph mentions the graph relations of the function symbols of the term positively, and
mentions no relation symbols negatively. -/
@[simp]
theorem relationsInSigned_graphFormula {n : ℕ} (s : Bool) (t : L.Term β)
    (ρ : β → α ⊕ Fin n) (y : α ⊕ Fin n) :
    (t.graphFormula ρ y).relationsInSigned s =
      if s then graphRelSym '' t.functionsIn else ∅ := by
  induction t generalizing n with
  | var b => cases s <;> simp
  | @func k f ts ih =>
    cases s with
    | false => simp [graphFormula_func, ih]
    | true =>
      simp only [graphFormula_func, BoundedFormulaInf.relationsInSigned_exsLast,
        BoundedFormulaInf.relationsInSigned_inf, BoundedFormulaInf.relationsInSigned_iInfAlong, ih,
        ite_true, BoundedFormulaInf.relationsInSigned_rel, functionsIn_func, Set.image_union,
        Set.image_iUnion, Set.image_singleton, graphRelSym_mk, Set.union_comm]

end Term

namespace BoundedFormulaInf

variable {n : ℕ}

/-- **Exact base-symbol polarity preservation**: a base relation symbol occurs with polarity `s` in
`φ.relationalize` if and only if the underlying relation symbol of `L` occurs with polarity `s` in
`φ`. -/
@[simp]
theorem preimage_baseRelSym_relationsInSigned_relationalize (s : Bool)
    (φ : L.BoundedFormulaω α n) :
    baseRelSym ⁻¹' (φ.relationalize.relationsInSigned s) = φ.relationsInSigned s := by
  induction φ generalizing s with
  | falsum => simp
  | equal t₁ t₂ =>
    cases s with
    | false => simp [relationalize_equal]
    | true =>
      ext r
      simp only [relationalize_equal, relationsInSigned_exsLast, relationsInSigned_inf,
        Term.relationsInSigned_graphFormula, ite_true, relationsInSigned_equal, Set.mem_preimage,
        Set.mem_union, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_or]
      exact ⟨fun ⟨f, _, hf⟩ => baseRelSym_ne_graphRelSym r f hf.symm,
        fun ⟨f, _, hf⟩ => baseRelSym_ne_graphRelSym r f hf.symm⟩
  | rel R ts =>
    cases s with
    | false => simp [relationalize_rel]
    | true =>
      ext r
      simp only [relationalize_rel, relationsInSigned_exsLast, relationsInSigned_inf,
        relationsInSigned_iInfAlong, Term.relationsInSigned_graphFormula, ite_true,
        relationsInSigned_rel, Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_image,
        Set.mem_singleton_iff]
      refine ⟨?_, fun hr => Or.inr (by rw [hr, baseRelSym_mk])⟩
      rintro (⟨_, f, _, hf⟩ | hr)
      · exact (baseRelSym_ne_graphRelSym r f hf.symm).elim
      · exact baseRelSym_injective (hr.trans (baseRelSym_mk R).symm)
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Membership form of `preimage_baseRelSym_relationsInSigned_relationalize`. -/
@[simp]
theorem baseRelSym_mem_relationsInSigned_relationalize {s : Bool} {φ : L.BoundedFormulaω α n}
    {r : Σ k, L.Relations k} :
    baseRelSym r ∈ φ.relationalize.relationsInSigned s ↔ r ∈ φ.relationsInSigned s := by
  rw [← Set.mem_preimage, preimage_baseRelSym_relationsInSigned_relationalize]

/-- Raw-pair simp form of `baseRelSym_mem_relationsInSigned_relationalize`. -/
@[simp]
theorem mk_base_mem_relationsInSigned_relationalize {s : Bool} {φ : L.BoundedFormulaω α n}
    {k : ℕ} {R : L.Relations k} :
    (⟨k, GraphRelation.base R⟩ : Σ m, L.GraphRelation m) ∈
        φ.relationalize.relationsInSigned s ↔
      ⟨k, R⟩ ∈ φ.relationsInSigned s := by
  simpa only [baseRelSym_mk] using
    baseRelSym_mem_relationsInSigned_relationalize (s := s) (φ := φ) (r := ⟨k, R⟩)

/-- Every signed occurrence of a relation symbol of `L` in `φ` appears with the same polarity as a
base relation symbol in `φ.relationalize`. -/
theorem image_baseRelSym_relationsInSigned_subset_relationalize (s : Bool)
    (φ : L.BoundedFormulaω α n) :
    baseRelSym '' (φ.relationsInSigned s) ⊆ φ.relationalize.relationsInSigned s := by
  rw [Set.image_subset_iff, preimage_baseRelSym_relationsInSigned_relationalize]

/-- Every relation symbol occurring with polarity `s` in `φ.relationalize` is either the base
symbol of a relation occurring with polarity `s` in `φ` or the graph symbol of a function symbol
occurring in `φ`. The inclusion can be strict before adjoining `graphAxioms`, since negating an
equation flips the polarity of its graph-relation atoms. -/
theorem relationsInSigned_relationalize_subset (s : Bool) (φ : L.BoundedFormulaω α n) :
    φ.relationalize.relationsInSigned s ⊆ relSym φ.functionsIn (φ.relationsInSigned s) := by
  induction φ generalizing s with
  | falsum => simp
  | equal t₁ t₂ =>
    cases s with
    | false => simp [relationalize_equal]
    | true => simp [relationalize_equal, relSym_def, Set.image_union]
  | rel R ts =>
    cases s with
    | false => simp [relationalize_rel]
    | true => simp [relationalize_rel, relSym_def, Set.union_comm, Set.image_iUnion]
  | imp φ ψ ihφ ihψ =>
    simp only [relationalize_imp, relationsInSigned_imp, functionsIn_imp, relSym_union]
    exact Set.union_subset_union (ihφ (!s)) (ihψ s)
  | all φ ih => simpa using ih s
  | iSup φs ih =>
    simp only [relationalize_iSup, relationsInSigned_iSup, functionsIn_iSup, relSym_iUnion]
    exact Set.iUnion_mono fun i => ih i s
  | iInf φs ih =>
    simp only [relationalize_iInf, relationsInSigned_iInf, functionsIn_iInf, relSym_iUnion]
    exact Set.iUnion_mono fun i => ih i s

/-- **Signed occurrence calculus of back-translation**: the relation symbols occurring with polarity
`s` in `φ.backTranslate` are the relation symbols of `L` whose base symbol occurs with polarity `s`
in `φ`. Graph-relation atoms become equations and contribute to neither polarity. -/
@[simp]
theorem relationsInSigned_backTranslate {ι : Type uι} (s : Bool)
    (φ : L.graphLanguage.BoundedFormulaInf ι α n) :
    φ.backTranslate.relationsInSigned s = baseRelSym ⁻¹' (φ.relationsInSigned s) := by
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel R ts =>
    cases s with
    | false => cases R <;> simp
    | true =>
      ext r
      cases R with
      | base R => simpa using (baseRelSym_injective.eq_iff (a := r) (b := ⟨_, R⟩)).symm
      | graph f => simpa using baseRelSym_ne_graphRelSym r ⟨_, f⟩
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

end BoundedFormulaInf

/-! ### Signed occurrences in the graph axioms and translated entailments -/

namespace Functions

variable {k : ℕ} (f : L.Functions k)

/-- Totality `∀ xs, ∃ y, G_f(xs, y)` mentions `G_f` positively and nothing negatively. -/
@[simp]
theorem relationsInSigned_graphTotality (s : Bool) :
    f.graphTotality.relationsInSigned s = if s then {graphRelSym ⟨k, f⟩} else ∅ := by
  simp [graphTotality_def]

/-- Functionality `∀ xs y z, G_f(xs, y) → G_f(xs, z) → y = z` mentions `G_f` negatively and
nothing positively. -/
@[simp]
theorem relationsInSigned_graphFunctionality (s : Bool) :
    f.graphFunctionality.relationsInSigned s = if s then ∅ else {graphRelSym ⟨k, f⟩} := by
  cases s <;> simp [graphFunctionality_def]

end Functions

section GraphAxioms

variable {F : Set (Σ k, L.Functions k)}

/-- Because totality supplies `G_f` positively and functionality supplies `G_f` negatively, the
graph axioms of `F` mention exactly `relSym F ∅` at *both* polarities. -/
theorem relationsInSigned_graphAxioms (s : Bool) :
    ⋃ φ ∈ graphAxioms F, φ.relationsInSigned s = relSym F ∅ := by
  ext S
  simp only [Set.mem_iUnion, mem_graphAxioms_iff, relSym_def, Set.image_empty, Set.empty_union,
    Set.mem_image]
  constructor
  · rintro ⟨φ, ⟨⟨k, f⟩, hf, rfl | rfl⟩, hS⟩
    · cases s <;> simp only [Functions.relationsInSigned_graphTotality, ↓reduceIte,
        Bool.false_eq_true, Set.mem_singleton_iff, Set.mem_empty_iff_false] at hS
      exact ⟨⟨k, f⟩, hf, hS.symm⟩
    · cases s <;> simp only [Functions.relationsInSigned_graphFunctionality, ↓reduceIte,
        Bool.false_eq_true, Set.mem_singleton_iff, Set.mem_empty_iff_false] at hS
      exact ⟨⟨k, f⟩, hf, hS.symm⟩
  · rintro ⟨⟨k, f⟩, hf, rfl⟩
    cases s with
    | false => exact ⟨f.graphFunctionality, ⟨⟨k, f⟩, hf, Or.inr rfl⟩, by simp⟩
    | true => exact ⟨f.graphTotality, ⟨⟨k, f⟩, hf, Or.inl rfl⟩, by simp⟩

/-- The countable conjunction of the graph axioms of `F` has signed relation occurrences equal to
`relSym F ∅` at both polarities. -/
theorem relationsInSigned_conjunction_graphAxioms (s : Bool) (hF : (graphAxioms F).Countable) :
    ((graphAxioms F).conjunction hF).relationsInSigned s = relSym F ∅ := by
  rw [Theoryω.relationsInSigned_conjunction, relationsInSigned_graphAxioms]

/-- Adjoining `(graphAxioms F).conjunction hF` conjunctively to `φ.relationalize` gives the exact
signed occurrence set `relSym F (φ.relationsInSigned s)` whenever `φ.functionsIn ⊆ F`. -/
theorem relationsInSigned_conjunction_graphAxioms_inf_relationalize (s : Bool)
    (hF : (graphAxioms F).Countable) (φ : L.Sentenceω) (hφ : φ.functionsIn ⊆ F) :
    ((graphAxioms F).conjunction hF ⊓ φ.relationalize).relationsInSigned s =
      relSym F (φ.relationsInSigned s) := by
  rw [BoundedFormulaInf.relationsInSigned_inf, relationsInSigned_conjunction_graphAxioms]
  refine Set.Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · simp [relSym_def]
  · refine (φ.relationsInSigned_relationalize_subset s).trans ?_
    rw [relSym_def, relSym_def]
    exact Set.union_subset_union_right _ (Set.image_mono hφ)
  · rw [relSym_def]
    exact Set.union_subset
      ((φ.image_baseRelSym_relationsInSigned_subset_relationalize s).trans Set.subset_union_right)
      (by simp [relSym_def])

/-- Adjoining `(graphAxioms F).conjunction hF` as an antecedent before `φ.relationalize` likewise
gives the exact signed occurrence set `relSym F (φ.relationsInSigned s)` whenever
`φ.functionsIn ⊆ F`, because `(graphAxioms F).conjunction hF` carries `relSym F ∅` at the flipped
polarity `!s` as well. -/
theorem relationsInSigned_conjunction_graphAxioms_imp_relationalize (s : Bool)
    (hF : (graphAxioms F).Countable) (φ : L.Sentenceω) (hφ : φ.functionsIn ⊆ F) :
    (((graphAxioms F).conjunction hF).imp φ.relationalize).relationsInSigned s =
      relSym F (φ.relationsInSigned s) := by
  rw [BoundedFormulaInf.relationsInSigned_imp, relationsInSigned_conjunction_graphAxioms,
    ← relationsInSigned_conjunction_graphAxioms s hF, ← BoundedFormulaInf.relationsInSigned_inf]
  exact relationsInSigned_conjunction_graphAxioms_inf_relationalize s hF φ hφ

end GraphAxioms

end FirstOrder.Language
