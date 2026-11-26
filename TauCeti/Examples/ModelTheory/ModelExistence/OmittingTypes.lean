/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.OmittingTypes

/-!
# Regression examples: first-order isolation and the omitting types theorem

These examples exercise first-order isolation and omission of types from a downstream module,
through public statements only:

* the empty type is isolated over every satisfiable theory and is omitted by no nonempty
  structure, so the non-isolation hypothesis of the first-order omitting types theorem cannot be
  dropped;
* the type `{⊥}` is isolated over no theory and is omitted by every structure;
* for a sentence `ψ`, a structure omits `{ψ}` exactly when it does not satisfy `ψ`;
* **standard numbers.** In the language `{0, S}`, the type `{x ≠ Sᵏ0 : k ∈ ℕ}` of a nonstandard
  number is omitted by `ℕ`, so it is not isolated over the complete theory of `ℕ`: a formula
  consistent with that complete theory holds of some standard number. The first-order omitting
  types theorem then gives, in every universe, a countable model of the complete theory of `ℕ`
  in which every element is the value of a numeral.

For the first-order omitting types theorem see D. Marker, *Model Theory: An Introduction*,
Springer, 2002, §4.2.
-/

@[expose] public section

namespace TauCeti

open FirstOrder FirstOrder.Language

universe u v w

section Checks

variable {L : Language.{u, v}} {T : L.Theory} {n : ℕ}

-- The empty type is isolated, by `⊤`, over every satisfiable theory.
example (hT : T.IsSatisfiable) : T.IsolatesFO (∅ : Set (L.BoundedFormula Empty n)) :=
  Theory.isolatesFO_empty_iff.2 hT

-- No nonempty structure omits the empty type.
example (M : Type w) [L.Structure M] [Nonempty M] :
    ¬OmitsFOType M (∅ : Set (L.BoundedFormula Empty n)) := by
  simp

-- The type `{⊥}` is isolated over no theory.
example : ¬T.IsolatesFO ({⊥} : Set (L.BoundedFormula Empty n)) :=
  Theory.not_isolatesFO_singleton_bot

-- Every structure omits the type `{⊥}`.
example (M : Type w) [L.Structure M] : OmitsFOType M ({⊥} : Set (L.BoundedFormula Empty n)) :=
  omitsFOType_singleton_bot

-- At `n = 0`, a structure omits `{ψ}` exactly when it does not satisfy the sentence `ψ`.
example (M : Type w) [L.Structure M] (ψ : L.Sentence) : OmitsFOType M {ψ} ↔ ¬M ⊨ ψ := by
  rw [omitsFOType_singleton_iff, Unique.forall_iff, Sentence.Realize, Formula.Realize,
    Subsingleton.elim (default : Empty → M) Empty.elim]

end Checks

namespace StandardNumbersExample

/-- The function symbols of the language `{0, S}`. -/
inductive Func : ℕ → Type
  | zero : Func 0
  | succ : Func 1

/-- The language `{0, S}` of zero and successor, with no relation symbols. -/
abbrev lang : Language.{0, 0} :=
  ⟨Func, fun _ => Empty⟩

/-- The language `{0, S}` has countably many function symbols: at most one of each arity. -/
instance : Countable (Σ l, lang.Functions l) := by
  refine Function.Injective.countable (f := fun x : Σ l, lang.Functions l => x.1) ?_
  rintro ⟨_, a⟩ ⟨_, b⟩ h
  cases a <;> cases b <;> first | rfl | simp at h

/-- The natural numbers, with `0` and successor. -/
instance : lang.Structure ℕ where
  funMap
    | .zero, _ => 0
    | .succ, x => x 0 + 1
  RelMap r := Empty.elim r

/-- The numeral `Sᵏ0`, as a term over any variables. -/
def numeral {α : Type*} : ℕ → lang.Term α
  | 0 => .func Func.zero default
  | k + 1 => .func Func.succ ![numeral k]

/-- The value of a numeral does not depend on the valuation of the variables. -/
theorem realize_numeral_congr {α β M : Type*} [lang.Structure M] (k : ℕ) (v : α → M)
    (w : β → M) : (numeral k).realize v = (numeral k).realize w := by
  induction k with
  | zero =>
    simp only [numeral, Term.realize_func]
    congr
    ext i
    exact i.elim0
  | succ k ih =>
    simp only [numeral, Term.realize_func]
    congr
    ext i
    rw [Fin.fin_one_eq_zero i]
    exact ih

/-- In `ℕ`, the numeral `Sᵏ0` denotes `k`. -/
@[simp]
theorem realize_numeral {α : Type*} (k : ℕ) (v : α → ℕ) : (numeral k).realize v = k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (· + 1) ih

/-- The formula `x₀ ≠ Sᵏ0` in one bound position. -/
def neNumeral (k : ℕ) : lang.BoundedFormula Empty 1 :=
  (Term.bdEqual (Term.var (Sum.inr 0)) (numeral k)).not

/-- The type `{x₀ ≠ Sᵏ0 : k ∈ ℕ}` of a nonstandard number. -/
def nonstandardType : Set (lang.BoundedFormula Empty 1) :=
  Set.range neNumeral

/-- A one-tuple satisfies `x₀ ≠ Sᵏ0` exactly when its entry is not the value of `Sᵏ0`. -/
theorem realize_neNumeral_iff {M : Type*} [lang.Structure M] (k : ℕ) (a : Fin 1 → M) :
    (neNumeral k).Realize Empty.elim a ↔ a 0 ≠ (numeral k).realize (Empty.elim : Empty → M) := by
  simp only [neNumeral, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    Term.realize_var, Sum.elim_inr]
  rw [realize_numeral_congr k _ (Empty.elim : Empty → M)]

/-- `ℕ` omits the type of a nonstandard number: every natural number is the value of a numeral. -/
theorem omitsFOType_nonstandardType : OmitsFOType ℕ nonstandardType :=
  omitsFOType_iff.2 fun a => ⟨neNumeral (a 0), ⟨a 0, rfl⟩, by
    rw [realize_neNumeral_iff, realize_numeral, not_not]⟩

/-- The type of a nonstandard number is not isolated over the complete theory of `ℕ`, since `ℕ`
omits it. -/
theorem not_isolatesFO_nonstandardType : ¬(lang.completeTheory ℕ).IsolatesFO nonstandardType :=
  fun h => h.not_omitsFOType (fun _ hσ => Theory.models_sentence_of_mem
    ((mem_completeTheory (L := lang)).2 hσ)) omitsFOType_nonstandardType

/-- **Standard models.** The first-order omitting types theorem gives, in every universe, a
countable nonempty model of the complete theory of `ℕ` in the language `{0, S}` in which every
element is the value of a numeral. -/
theorem exists_countable_model_completeTheory_forall_eq_numeral :
    ∃ (M : Type w) (_ : lang.Structure M), Countable M ∧ Nonempty M ∧
      M ⊨ lang.completeTheory ℕ ∧
        ∀ x : M, ∃ k : ℕ, (numeral k).realize (Empty.elim : Empty → M) = x := by
  obtain ⟨M, _, hMc, hMne, hMT, hMo⟩ := Theory.exists_countable_model_omitting.{0, 0, w}
    (Theory.Model.isSatisfiable ℕ) (fun _ : Unit => nonstandardType)
    (fun _ => not_isolatesFO_nonstandardType)
  refine ⟨M, inferInstance, hMc, hMne, hMT, fun x => ?_⟩
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := omitsFOType_iff.1 (hMo ()) fun _ => x
  exact ⟨k, (not_not.1 (mt (realize_neNumeral_iff k _).2 hk)).symm⟩

end StandardNumbersExample

end TauCeti
