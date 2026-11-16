/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Satisfiability
public import TauCeti.ModelTheory.Semantics
import TauCeti.ModelTheory.Term.Constants

/-!
# Realizing sets of formulas and partial types over a first-order theory

Additions to Mathlib's `Mathlib.ModelTheory.Satisfiability` relating realization of sets of
first-order formulas and partial types to `FirstOrder.Language.Theory.IsSatisfiable`.

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
* Extends the constant-expansion API of `Mathlib/ModelTheory/Satisfiability.lean` (Aaron Anderson).
-/

public section

universe u v w

namespace FirstOrder.Language.Theory

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
        (insert (BoundedFormula.iInf fun ψ : s => ψ.1).exs T).IsSatisfiable := by
  constructor
  · rintro ⟨M, a, ha⟩ s hs
    have hM : M ⊨ insert (BoundedFormula.iInf fun ψ : s => ψ.1).exs T :=
      model_insert_iff.2 ⟨(Sentence.realize_exs _).2
        ⟨a, BoundedFormula.realize_iInf.2 fun ψ => ha ψ.1 (hs ψ.2)⟩, M.is_model⟩
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
      fun s => g.onTheory T ∪ BoundedFormula.evalAtConstants '' (s.1 : Set _)
    have hdir : Directed (· ⊆ ·) S := by
      classical
      intro s₁ s₂
      exact ⟨⟨s₁.1 ∪ s₂.1, by simp [s₁.2, s₂.2]⟩,
        Set.union_subset_union_right _ (Set.image_mono (by simp)),
        Set.union_subset_union_right _ (Set.image_mono (by simp))⟩
    have hsatS (s : Sub) : (S s).IsSatisfiable := by
      obtain ⟨N⟩ := hfin s.1 s.2
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
        · exact Or.inr ⟨ψ, s.2 hψ, rfl⟩
      · rintro (hT | ⟨ψ, hψ, rfl⟩)
        · exact ⟨⟨∅, by simp⟩, Or.inl hT⟩
        · exact ⟨⟨{ψ}, by simp [hψ]⟩, Or.inr ⟨ψ, Finset.mem_singleton_self ψ, rfl⟩⟩
    exact hu ▸ (isSatisfiable_directed_union_iff hdir).2 hsatS

end FirstOrder.Language.Theory
