/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.Infinitary.GraphTranslation.BackTranslate
public import TauCeti.ModelTheory.Scott.PotentialIso

/-!
# Scott's isomorphism theorem

For a countable language, every countable structure `M` is characterized up to isomorphism among
countable structures by a single `Lω₁ω` sentence.

For a countable relational language, the Scott sentence of `M` at any countable internally
stabilizing level is such a sentence: it holds in a countable structure exactly when that
structure is isomorphic to `M`. Its models are potentially isomorphic to `M`, and potential
isomorphism between countable structures is isomorphism. Conversely, isomorphic copies satisfy
it by invariance of infinitary satisfaction.

A language with function symbols reduces to its graph language `L.graphLanguage`, which is
relational and has countably many relation symbols when `L` has countably many symbols. The
back-translation of the Scott sentence of the graph expansion of `M` holds in a structure exactly
when that Scott sentence holds in its graph expansion
(`FirstOrder.Language.BoundedFormulaInf.realize_backTranslate`), and two structures are
isomorphic exactly when their graph expansions are.

The countability of the model cannot be dropped: models of the Scott sentence of any cardinality
are only potentially isomorphic to `M` (`TauCeti.potentialIso_of_realize_scottSentenceAt`).

## Main results

* `TauCeti.realize_scottSentenceAt_iff`: in a countable relational language, at a countable
  internally stabilizing level, the Scott sentence holds in a countable structure exactly when it
  is isomorphic to `M`.
* `TauCeti.realize_scottSentence_iff`: the same for the canonical Scott sentence.
* `TauCeti.scott_isomorphism`: **Scott's isomorphism theorem**, in a countable language every
  countable structure has an `Lω₁ω` sentence true in exactly the countable structures isomorphic
  to it.

## References

* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, in
  *The Theory of Models*, 1965.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language
open scoped Ordinal

variable {L : Language.{u, v}}

section Relational

variable [L.IsRelational] [Countable (Σ k, L.Relations k)]
variable (M : Type w) [L.Structure M] [Countable M]

/-- At a countable internally stabilizing level, the Scott sentence of a countable structure `M`
holds in a countable structure exactly when that structure is isomorphic to `M`. -/
theorem realize_scottSentenceAt_iff {α : Ordinal.{o}} (hα : α < ω₁)
    (hs : SelfStabilizesCompletely (L := L) M α) (N : Type w') [L.Structure N] [Countable N] :
    SentenceInf.Realize (scottSentenceAt (L := L) M α) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => countable_potentialIso_iff_iso.mp (potentialIso_of_realize_scottSentenceAt M hα h),
    fun ⟨e⟩ => e.realize_scottSentenceAt hα hs⟩

/-- The canonical Scott sentence of a countable structure `M` holds in a countable structure
exactly when that structure is isomorphic to `M`. -/
@[simp]
theorem realize_scottSentence_iff (N : Type w') [L.Structure N] [Countable N] :
    SentenceInf.Realize (scottSentence (L := L) M) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => countable_potentialIso_iff_iso.mp (potentialIso_of_realize_scottSentence M h),
    fun ⟨e⟩ => e.realize_scottSentence⟩

end Relational

/-- Two structures are isomorphic exactly when their graph expansions are. -/
private theorem nonempty_equiv_graphExpansion_iff {M : Type w} {N : Type w'} [L.Structure M]
    [L.Structure N] :
    letI := graphExpansion L M
    letI := graphExpansion L N
    Nonempty (M ≃[L.graphLanguage] N) ↔ Nonempty (M ≃[L] N) := by
  let := graphExpansion L M
  let := graphExpansion L N
  constructor
  · rintro ⟨e⟩
    refine ⟨{ toEquiv := e.toEquiv, map_fun' := ?_, map_rel' := ?_ }⟩
    · intro k f x
      have h := (e.map_rel (GraphRelation.graph f) (Fin.snoc x (Structure.funMap f x))).mpr
        (by simp)
      simp only [graphExpansion_relMap_graph, Fin.init_def, Function.comp_apply,
        Fin.snoc_castSucc, Fin.snoc_last] at h
      exact h.symm
    · intro k R x
      have h := e.map_rel (GraphRelation.base R) x
      rw [graphExpansion_relMap_base, graphExpansion_relMap_base] at h
      exact h
  · rintro ⟨e⟩
    refine ⟨{ toEquiv := e.toEquiv, map_fun' := fun f => PEmpty.elim f, map_rel' := ?_ }⟩
    intro k R x
    cases R with
    | base R =>
      rw [graphExpansion_relMap_base, graphExpansion_relMap_base]
      exact e.map_rel R x
    | graph f =>
      rw [graphExpansion_relMap_graph, graphExpansion_relMap_graph]
      have : Fin.init (e.toFun ∘ x) = e ∘ Fin.init x := rfl
      rw [this, ← e.map_fun]
      exact e.injective.eq_iff

/-- **Scott's isomorphism theorem.** In a countable language, every countable structure `M` has
an `Lω₁ω` sentence that `M` satisfies and that holds in a countable structure, in any universe,
exactly when that structure is isomorphic to `M`.

Function symbols are allowed: the sentence is the back-translation of the Scott sentence of the
graph expansion of `M`. -/
theorem scott_isomorphism [Countable (Σ k, L.Functions k)] [Countable (Σ k, L.Relations k)]
    (M : Type w) [L.Structure M] [Countable M] :
    ∃ σ : L.Sentenceω, SentenceInf.Realize σ M ∧
      ∀ (N : Type w') [L.Structure N] [Countable N],
        (SentenceInf.Realize σ N ↔ Nonempty (M ≃[L] N)) := by
  let := graphExpansion L M
  refine ⟨(scottSentence (L := L.graphLanguage) M).backTranslate, ?_, fun N _ _ => ?_⟩
  · have h := realize_scottSentence_self (L := L.graphLanguage) M
    rw [SentenceInf.realize_def, FormulaInf.realize_def] at h ⊢
    exact (BoundedFormulaInf.realize_backTranslate _ _ _).mpr h
  let := graphExpansion L N
  rw [← nonempty_equiv_graphExpansion_iff, ← realize_scottSentence_iff M N,
    SentenceInf.realize_def, FormulaInf.realize_def, SentenceInf.realize_def,
    FormulaInf.realize_def]
  exact BoundedFormulaInf.realize_backTranslate _ _ _

end TauCeti
