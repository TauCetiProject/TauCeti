/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# One-point structures with countably many unary predicates

In a finite relational language, the Scott sentence of a finite structure is equivalent to a
first-order sentence (`TauCeti.realize_scottSentence_iff_realize_characteristicSentence`).
Finiteness of the language cannot be dropped. In the language with a unary predicate `P i` for
every natural number `i`, no first-order sentence characterizes a one-point structure up to
isomorphism, even among countable structures: a first-order sentence mentions only finitely
many predicates, and changing the interpretation of an unmentioned predicate gives a
non-isomorphic model. The Scott sentence of such a structure, an infinitary sentence, still
characterizes it.

## Main results

* `TauCeti.natPredicateLanguage`: the relational language of countably many unary predicates.
* `TauCeti.natPredicateStructure S`: the one-point structure in which `P i` holds exactly when
  `i ∈ S`.
* `TauCeti.not_exists_sentence_iff_nonempty_equiv_natPredicateStructure`: no one-point structure
  in this language has a first-order Scott sentence.
-/

public section

namespace TauCeti

open FirstOrder FirstOrder.Language

/-- The relation symbols of the language of countably many unary predicates: a unary symbol
`pred i` for each natural number `i`. -/
inductive NatPredicateRel : ℕ → Type
  | pred (i : ℕ) : NatPredicateRel 1

/-- The relational language with a unary predicate symbol for each natural number. -/
@[expose] def natPredicateLanguage : Language := ⟨fun _ => Empty, NatPredicateRel⟩
  deriving IsRelational

/-- The language of countably many unary predicates has countably many relation symbols. -/
instance : Countable (Σ k, natPredicateLanguage.Relations k) := by
  refine Function.Surjective.countable
    (f := fun i : ℕ => (⟨1, NatPredicateRel.pred i⟩ : Σ k, natPredicateLanguage.Relations k)) ?_
  rintro ⟨_, ⟨i⟩⟩
  exact ⟨i, rfl⟩

/-- The one-point structure in the language of countably many unary predicates in which the
predicate `pred i` holds exactly when `i ∈ S`. -/
@[instance_reducible]
def natPredicateStructure (S : Set ℕ) : natPredicateLanguage.Structure Unit where
  RelMap | .pred i => fun _ => i ∈ S

/-- In `natPredicateStructure S`, the predicate `pred i` holds exactly when `i ∈ S`. -/
@[simp]
theorem relMap_natPredicateStructure (S : Set ℕ) (i : ℕ) (x : Fin 1 → Unit) :
    @Structure.RelMap natPredicateLanguage Unit (natPredicateStructure S) 1
      (NatPredicateRel.pred i) x ↔ i ∈ S :=
  Iff.rfl

/-- A first-order formula mentions only finitely many of the predicates: its truth in the
one-point structures depends only on the predicates below some bound. -/
private theorem exists_forall_realize_iff {α : Type*} {n : ℕ}
    (φ : natPredicateLanguage.BoundedFormula α n) :
    ∃ k : ℕ, ∀ S T : Set ℕ, (∀ i < k, i ∈ S ↔ i ∈ T) → ∀ (v : α → Unit) (xs : Fin n → Unit),
      (letI := natPredicateStructure S; φ.Realize v xs) ↔
        (letI := natPredicateStructure T; φ.Realize v xs) := by
  induction φ with
  | falsum => exact ⟨0, fun _ _ _ _ _ => Iff.rfl⟩
  | equal t₁ t₂ =>
    -- An equation realizes as an equality of elements of `Unit`, which always holds.
    exact ⟨0, fun _ _ _ _ _ => iff_of_true (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  | rel R ts =>
    cases R with
    | pred i =>
      refine ⟨i + 1, fun S T h _ _ => ?_⟩
      simpa only [BoundedFormula.Realize, relMap_natPredicateStructure] using h i i.lt_succ_self
  | imp φ ψ ihφ ihψ =>
    obtain ⟨k₁, h₁⟩ := ihφ
    obtain ⟨k₂, h₂⟩ := ihψ
    refine ⟨max k₁ k₂, fun S T h v xs => ?_⟩
    simp only [BoundedFormula.realize_imp]
    exact imp_congr (h₁ S T (fun i hi => h i (lt_max_of_lt_left hi)) v xs)
      (h₂ S T (fun i hi => h i (lt_max_of_lt_right hi)) v xs)
  | all φ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k, fun S T h v xs => ?_⟩
    simp only [BoundedFormula.realize_all]
    exact forall_congr' fun x => hk S T h v (Fin.snoc xs x)

/-- In the language of countably many unary predicates, no first-order sentence characterizes a
one-point structure up to isomorphism, even among countable structures. Its Scott sentence, an
infinitary sentence, does characterize it (`realize_scottSentence_iff_of_finite`). -/
theorem not_exists_sentence_iff_nonempty_equiv_natPredicateStructure (S : Set ℕ) :
    letI := natPredicateStructure S
    ¬ ∃ φ : natPredicateLanguage.Sentence, ∀ (N : Type) [natPredicateLanguage.Structure N]
      [Countable N], N ⊨ φ ↔ Nonempty (Unit ≃[natPredicateLanguage] N) := by
  let := natPredicateStructure S
  rintro ⟨φ, hφ⟩
  obtain ⟨k, hk⟩ := exists_forall_realize_iff φ
  -- Flip the predicate `pred k`, which `φ` does not mention.
  let T : Set ℕ := {i | i ∈ S ↔ i ≠ k}
  have hT : (letI := natPredicateStructure T; Unit ⊨ φ) := by
    refine (hk S T (fun i hi => ?_) default default).mp ((hφ Unit).mpr ⟨.refl _ _⟩)
    simp [T, hi.ne]
  obtain ⟨e⟩ := (@hφ Unit (natPredicateStructure T) _).mp hT
  have hk' := @Equiv.map_rel _ _ _ (natPredicateStructure S) (natPredicateStructure T) e _
    (NatPredicateRel.pred k) default
  simp [T] at hk'

end TauCeti
