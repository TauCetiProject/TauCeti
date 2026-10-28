/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics

/-!
# Isomorphism invariance of infinitary satisfaction

An isomorphism of first-order structures preserves realization of infinitary formulas,
with both free and bound valuations transported along the isomorphism. In particular,
isomorphic structures satisfy the same infinitary sentences. The branching carrier and
the two structure universes are independent, and neither structure needs to be nonempty.

These results allow characteristic sentences of structures to be transported to their
isomorphic copies. They apply to languages with functions as well as relational languages.

The API and the atomic cases follow Mathlib's `StrongHomClass.realize_boundedFormula`,
`realize_formula`, and `realize_sentence` in `Mathlib/ModelTheory/Semantics.lean`
(Aaron Anderson, Jesse Michael Han, Floris van Doorn). Infinitary conjunctions and disjunctions
additionally require preservation of realization at every branch.
-/

public section

universe u v u' uι w w'

namespace FirstOrder.Language.StrongHomClass

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {n : ℕ}
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
variable {F : Type*} [EquivLike F M N] [StrongHomClass L F M N] (g : F)

/-- Isomorphisms preserve realization of infinitary bounded formulas when both valuations
are transported along the isomorphism. -/
@[simp]
theorem realize_boundedFormulaInf (φ : L.BoundedFormulaInf ι α n) {v : α → M}
    {xs : Fin n → M} : φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => simp
  | equal =>
    simp only [BoundedFormulaInf.realize_equal, ← Sum.comp_elim, HomClass.realize_term,
      EmbeddingLike.apply_eq_iff_eq g]
  | rel =>
    simp only [BoundedFormulaInf.realize_rel, ← Sum.comp_elim, HomClass.realize_term]
    exact StrongHomClass.map_rel g _ _
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInf.realize_imp, ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormulaInf.realize_all]
    exact (EquivLike.surjective g).forall.trans
      (forall_congr' fun y => by rw [← Fin.comp_snoc, ih])
  | iSup φs ih => simp only [BoundedFormulaInf.realize_iSup, ih]
  | iInf φs ih => simp only [BoundedFormulaInf.realize_iInf, ih]

/-- Isomorphisms preserve realization of infinitary formulas under transported free
valuations. -/
@[simp]
theorem realize_formulaInf (φ : L.FormulaInf ι α) {v : α → M} :
    φ.Realize (g ∘ v) ↔ φ.Realize v := by
  rw [FormulaInf.realize_def, FormulaInf.realize_def, ← realize_boundedFormulaInf g φ,
    Unique.eq_default (g ∘ (default : Fin 0 → M))]

include g in
/-- Isomorphic structures satisfy the same infinitary sentences. -/
theorem realize_sentenceInf (φ : L.SentenceInf ι) : φ.Realize M ↔ φ.Realize N := by
  rw [SentenceInf.realize_def, SentenceInf.realize_def, ← realize_formulaInf g φ,
    Subsingleton.elim (g ∘ (Empty.elim : Empty → M)) Empty.elim]

end FirstOrder.Language.StrongHomClass
