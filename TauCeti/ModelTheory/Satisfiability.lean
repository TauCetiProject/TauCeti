/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Satisfiability
public import TauCeti.ModelTheory.LanguageMap
public import TauCeti.ModelTheory.Semantics
import TauCeti.ModelTheory.Syntax
import TauCeti.ModelTheory.Term.Constants

/-!
# Entailment, completeness and partial-type realization for first-order theories

Additions to Mathlib's `Mathlib.ModelTheory.Satisfiability` describing how semantic entailment
(`Theory.ModelsBoundedFormula`, written `T ⊨ᵇ φ`) and theory completeness (`Theory.IsComplete`)
behave under language homomorphisms and language equivalences across arbitrary universes, and
relating realization of sets of formulas and partial types to `Theory.IsSatisfiable`.

Any language homomorphism `g : L →ᴸ L'` pushes semantic entailment forward
(`FirstOrder.Language.Theory.ModelsBoundedFormula.onTheory`): any model of `g.onTheory T` restricts
along `g.reduct` to a model of `T`. When `g` is injective, `g.defaultExpansion` expands every
nonempty model of `T` to a model of `g.onTheory T`, so `g` also reflects entailment
(`FirstOrder.Language.Theory.modelsBoundedFormula_onTheory_iff`,
`FirstOrder.Language.Theory.models_onSentence_onTheory_iff`) and reflects completeness
(`FirstOrder.Language.Theory.IsComplete.of_onTheory`). Along a language equivalence `e : L ≃ᴸ L'`,
`e.onSentence` is surjective on sentences as well, so satisfiability, entailment and completeness
are preserved and reflected (`FirstOrder.Language.LEquiv.isSatisfiable_onTheory_iff`,
`FirstOrder.Language.LEquiv.modelsBoundedFormula_onTheory_iff`,
`FirstOrder.Language.LEquiv.isComplete_onTheory_iff`).

A set `p` of formulas in free variables `α` is realized at some valuation in a nonempty model of a
first-order theory `T` if and only if `T` together with the constant-expansion sentences
`Formula.equivSentence '' p` is satisfiable in `L[[α]]`
(`FirstOrder.Language.Theory.exists_modelType_realize_iff_isSatisfiable_equivSentence`), providing
the existential counterpart to
`FirstOrder.Language.Theory.models_formula_iff_onTheory_models_equivSentence`.
Specializing to closed bounded formulas in `n` bound variables characterizes realization of a
partial `n`-type `p` in terms of `BoundedFormula.evalAtConstants '' p` in `L[[Fin n]]`
(`FirstOrder.Language.Theory.exists_modelType_realize_iff_isSatisfiable_evalAtConstants`), from
which compactness for first-order partial types follows via
`Theory.isSatisfiable_directed_union_iff`
(`FirstOrder.Language.Theory.exists_modelType_realize_iff_forall_finset_isSatisfiable`): `p` is
realized in some nonempty model of `T` if and only if for every finite subset `s` of `p`, `T`
together with the existential closure of the conjunction of `s` is satisfiable.

## Main results

* `FirstOrder.Language.Theory.ModelsBoundedFormula.onTheory` and
  `FirstOrder.Language.Theory.modelsBoundedFormula_onTheory_iff`: entailment is preserved by every
  language map and reflected by injective ones, across arbitrary universes.
* `FirstOrder.Language.Theory.IsComplete.of_onTheory` and
  `FirstOrder.Language.LEquiv.isComplete_onTheory_iff`: completeness is reflected by injective
  language maps and invariant under language equivalences.
* `FirstOrder.Language.Theory.exists_modelType_realize_iff_isSatisfiable_equivSentence`: realizing
  a set of formulas in `L.Formula α` is equivalent to satisfiability of the constant expansion in
  `L[[α]]`.
* `FirstOrder.Language.Theory.exists_modelType_realize_iff_isSatisfiable_evalAtConstants`:
  realizing a partial `n`-type in `L.BoundedFormula Empty n` is equivalent to satisfiability of its
  constant evaluation in `L[[Fin n]]`.
* `FirstOrder.Language.Theory.exists_modelType_realize_iff_forall_finset_isSatisfiable`: a
  first-order partial type is realized in some nonempty model if and only if the conjunction of
  every finite subset is satisfiable with the theory.

## References

* D. Marker, *Model Theory: An Introduction*, Springer, 2002, Sections 2.1 and 4.2.
* Extends the language-map and constant-expansion API of `Mathlib/ModelTheory/Satisfiability.lean`
  (Aaron Anderson).
-/

public section

universe u v u' v' w

namespace FirstOrder.Language

namespace Theory

section LanguageMap

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {T : L.Theory} {α : Type w} {n : ℕ}

/-- **Language maps preserve semantic entailment.** If `T ⊨ᵇ φ`, then `g.onTheory T` models
`g.onBoundedFormula φ` for every language map `g : L →ᴸ L'`, across arbitrary universes. -/
theorem ModelsBoundedFormula.onTheory {φ : L.BoundedFormula α n} (h : T ⊨ᵇ φ) (g : L →ᴸ L') :
    g.onTheory T ⊨ᵇ g.onBoundedFormula φ := by
  intro M v xs
  let : L.Structure M := g.reduct M
  have : M ⊨ T := (g.onTheory_model T).1 M.is_model
  exact (g.realize_onBoundedFormula φ).2 (h.realize_boundedFormula M)

/-- **Language maps preserve sentence entailment.** If `T ⊨ᵇ φ` for a sentence `φ`, then
`g.onTheory T ⊨ᵇ g.onSentence φ`. -/
theorem ModelsBoundedFormula.onSentence {φ : L.Sentence} (h : T ⊨ᵇ φ) (g : L →ᴸ L') :
    g.onTheory T ⊨ᵇ g.onSentence φ :=
  h.onTheory g

/-- **Injective language maps preserve and reflect semantic entailment.** For an injective language
map `g : L →ᴸ L'`, `g.onTheory T` models `g.onBoundedFormula φ` if and only if `T` models `φ`. -/
theorem modelsBoundedFormula_onTheory_iff {g : L →ᴸ L'} (hg : g.Injective)
    {φ : L.BoundedFormula α n} :
    g.onTheory T ⊨ᵇ g.onBoundedFormula φ ↔ T ⊨ᵇ φ := by
  classical
  refine ⟨fun h M v xs => ?_, fun h => h.onTheory g⟩
  have : Inhabited M := Classical.inhabited_of_nonempty'
  let : L'.Structure M := g.defaultExpansion M
  have : g.IsExpansionOn M := hg.isExpansionOn_default M
  have : M ⊨ g.onTheory T := (g.onTheory_model T).2 M.is_model
  exact (g.realize_onBoundedFormula φ).1 (h.realize_boundedFormula M)

/-- **Injective language maps preserve and reflect sentence entailment.** -/
theorem models_onSentence_onTheory_iff {g : L →ᴸ L'} (hg : g.Injective) {φ : L.Sentence} :
    g.onTheory T ⊨ᵇ g.onSentence φ ↔ T ⊨ᵇ φ :=
  modelsBoundedFormula_onTheory_iff hg

/-- **Injective language maps reflect completeness.** If `g : L →ᴸ L'` is injective and
`g.onTheory T` is complete, then `T` is complete. -/
theorem IsComplete.of_onTheory {g : L →ᴸ L'} (hg : g.Injective) (h : (g.onTheory T).IsComplete) :
    T.IsComplete := by
  refine ⟨isSatisfiable_of_isSatisfiable_onTheory g h.1, fun φ => ?_⟩
  rcases h.2 (g.onSentence φ) with hφ | hφ
  · exact .inl ((models_onSentence_onTheory_iff hg).1 hφ)
  · rw [← LHom.onSentence_not] at hφ
    exact .inr ((models_onSentence_onTheory_iff hg).1 hφ)

end LanguageMap

section RealizeType

variable {L : Language.{u, v}}

/-- A set of formulas `p` in free variables `α` is realized at some valuation in a nonempty model
of `T` if and only if `T` together with `Formula.equivSentence '' p` is satisfiable in `L[[α]]`.
This is the existential counterpart to `Theory.models_formula_iff_onTheory_models_equivSentence`. -/
theorem exists_modelType_realize_iff_isSatisfiable_equivSentence {T : L.Theory} {α : Type w}
    {p : Set (L.Formula α)} :
    (∃ M : ModelType.{u, v, max u v w} T, ∃ v : α → M, ∀ φ ∈ p, φ.Realize v) ↔
      ((L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' p).IsSatisfiable := by
  let g := L.lhomWithConstants α
  constructor
  · rintro ⟨M, v, hv⟩
    let : (constantsOn α).Structure M := constantsOn.structure v
    have hM : M ⊨ g.onTheory T ∪ Formula.equivSentence '' p := by
      refine model_union_iff.2 ⟨(g.onTheory_model T).2 M.is_model, (model_iff _).2 ?_⟩
      rintro _ ⟨φ, hφ, rfl⟩
      rw [Formula.realize_equivSentence]
      simpa only [coe_con_constantsOn_structure] using hv φ hφ
    let := hM
    exact Model.isSatisfiable M
  · rintro ⟨M⟩
    let : L.Structure M := g.reduct M
    have := g.isExpansionOn_reduct M
    have hMT : M ⊨ T := (g.onTheory_model T).1 (M.is_model.mono Set.subset_union_left)
    have hMp : M ⊨ Formula.equivSentence '' p := M.is_model.mono Set.subset_union_right
    have hreal (φ : L.Formula α) (hφ : φ ∈ p) : φ.Realize fun a => (L.con a : M) :=
      (Formula.realize_equivSentence M φ).1 (hMp.realize_of_mem _ ⟨φ, hφ, rfl⟩)
    let := hMT
    exact ⟨ModelType.of T M, fun a => (L.con a : M), hreal⟩

/-- A partial `n`-type `p` is realized in some nonempty model of `T` if and only if `T` together
with `p` evaluated at `n` fresh constants is satisfiable in `L[[Fin n]]`. -/
theorem exists_modelType_realize_iff_isSatisfiable_evalAtConstants {T : L.Theory} {n : ℕ}
    {p : Set (L.BoundedFormula Empty n)} :
    (∃ M : ModelType.{u, v, max u v} T, ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a) ↔
      ((L.lhomWithConstants (Fin n)).onTheory T ∪
        BoundedFormula.evalAtConstants '' p).IsSatisfiable := by
  have himg : BoundedFormula.evalAtConstants '' p = Formula.equivSentence ''
      ((fun ψ : L.BoundedFormula Empty n =>
        ψ.toFormula.relabel (Sum.elim Empty.elim id)) '' p) := by
    rw [Set.image_image]
    simp only [BoundedFormula.evalAtConstants_def]
  rw [himg, ← exists_modelType_realize_iff_isSatisfiable_equivSentence]
  refine exists_congr fun M => exists_congr fun a => ?_
  simp only [Set.forall_mem_image, Formula.realize_relabel, BoundedFormula.realize_toFormula,
    Function.comp_assoc, Sum.elim_comp_inl, Sum.elim_comp_inr, Function.comp_id,
    Subsingleton.elim (a ∘ Empty.elim) Empty.elim]

/-- **Compactness for first-order partial types.** A partial type `p` is realized in some nonempty
model of `T` if and only if for every finite subset `s` of `p`, `T` together with the existential
closure of the conjunction of `s` is satisfiable in the sense of `Theory.IsSatisfiable`. Compare
with isolation modulo `T`, which asks for a single formula `φ` consistent with `T` that implies
every member of `p`. -/
theorem exists_modelType_realize_iff_forall_finset_isSatisfiable {T : L.Theory} {n : ℕ}
    {p : Set (L.BoundedFormula Empty n)} :
    (∃ M : ModelType.{u, v, max u v} T, ∃ a : Fin n → M, ∀ ψ ∈ p, ψ.Realize Empty.elim a) ↔
      ∀ s : Finset (L.BoundedFormula Empty n), (s : Set (L.BoundedFormula Empty n)) ⊆ p →
        (insert (BoundedFormula.iInf fun ψ : s => ψ.val).exs T).IsSatisfiable := by
  constructor
  · rintro ⟨M, a, ha⟩ s hs
    have hM : M ⊨ insert (BoundedFormula.iInf fun ψ : s => ψ.val).exs T :=
      model_insert_iff.2 ⟨(Sentence.realize_exs _).2
        ⟨a, BoundedFormula.realize_iInf.2 fun ψ => ha ψ.val (hs ψ.property)⟩, M.is_model⟩
    let := hM
    exact Model.isSatisfiable M
  · intro hfin
    -- Express `p` as the directed union of its finite subsets in `L[[Fin n]]` and apply
    -- compactness via `isSatisfiable_directed_union_iff`.
    rw [exists_modelType_realize_iff_isSatisfiable_evalAtConstants]
    let g := L.lhomWithConstants (Fin n)
    let Sub := {s : Finset (L.BoundedFormula Empty n) // (s : Set (L.BoundedFormula Empty n)) ⊆ p}
    have : Nonempty Sub := ⟨⟨∅, by simp⟩⟩
    let S : Sub → L[[Fin n]].Theory :=
      fun s => g.onTheory T ∪ BoundedFormula.evalAtConstants '' (s.val : Set _)
    have hdir : Directed (· ⊆ ·) S := by
      classical
      intro s₁ s₂
      exact ⟨⟨s₁.val ∪ s₂.val, by simp [s₁.property, s₂.property]⟩,
        Set.union_subset_union_right _ (Set.image_mono (by simp)),
        Set.union_subset_union_right _ (Set.image_mono (by simp))⟩
    have hsatS (s : Sub) : (S s).IsSatisfiable := by
      obtain ⟨N⟩ := hfin s.val s.property
      have hNT : N ⊨ T := N.is_model.mono (Set.subset_insert _ _)
      obtain ⟨a, ha⟩ := (Sentence.realize_exs _).1
        (N.is_model.realize_of_mem _ (Set.mem_insert _ _))
      let := hNT
      exact exists_modelType_realize_iff_isSatisfiable_evalAtConstants.1
        ⟨ModelType.of T N, a, fun ψ hψ => BoundedFormula.realize_iInf.1 ha ⟨ψ, hψ⟩⟩
    have hu : (⋃ s : Sub, S s) = g.onTheory T ∪ BoundedFormula.evalAtConstants '' p := by
      ext σ
      simp only [S, Set.mem_iUnion, Set.mem_union, Set.mem_image, Finset.mem_coe]
      refine ⟨?_, ?_⟩
      · rintro ⟨s, hT | ⟨ψ, hψ, rfl⟩⟩
        · exact Or.inl hT
        · exact Or.inr ⟨ψ, s.property hψ, rfl⟩
      · rintro (hT | ⟨ψ, hψ, rfl⟩)
        · exact ⟨⟨∅, by simp⟩, Or.inl hT⟩
        · exact ⟨⟨{ψ}, by simp [hψ]⟩, Or.inr ⟨ψ, Finset.mem_singleton_self ψ, rfl⟩⟩
    exact hu ▸ (isSatisfiable_directed_union_iff hdir).2 hsatS

end RealizeType

end Theory

namespace LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}} (e : L ≃ᴸ L')
  {T : L.Theory} {α : Type w} {n : ℕ}

/-- A language equivalence preserves and reflects satisfiability of first-order theories. -/
@[simp]
theorem isSatisfiable_onTheory_iff : (e.toLHom.onTheory T).IsSatisfiable ↔ T.IsSatisfiable :=
  Theory.isSatisfiable_onTheory_iff e.toLHom_injective

/-- A language equivalence preserves and reflects semantic entailment of bounded formulas. -/
@[simp]
theorem modelsBoundedFormula_onTheory_iff {φ : L.BoundedFormula α n} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onBoundedFormula φ ↔ T ⊨ᵇ φ :=
  Theory.modelsBoundedFormula_onTheory_iff e.toLHom_injective

/-- A language equivalence preserves and reflects semantic entailment of sentences. -/
@[simp]
theorem models_onSentence_onTheory_iff {φ : L.Sentence} :
    e.toLHom.onTheory T ⊨ᵇ e.toLHom.onSentence φ ↔ T ⊨ᵇ φ :=
  Theory.models_onSentence_onTheory_iff e.toLHom_injective

/-- **Completeness along a language equivalence.** The image of a first-order theory along a
language equivalence is complete if and only if the theory is complete. -/
@[simp]
theorem isComplete_onTheory_iff : (e.toLHom.onTheory T).IsComplete ↔ T.IsComplete := by
  refine ⟨fun h => h.of_onTheory e.toLHom_injective, fun ⟨hsat, hdec⟩ => ?_⟩
  refine ⟨e.isSatisfiable_onTheory_iff.2 hsat, fun ψ => ?_⟩
  obtain ⟨φ, rfl⟩ := e.onSentence.surjective ψ
  exact (hdec φ).imp e.models_onSentence_onTheory_iff.2 e.models_onSentence_onTheory_iff.2

end LEquiv

end FirstOrder.Language
