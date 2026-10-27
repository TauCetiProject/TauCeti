/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics
public import TauCeti.ModelTheory.Infinitary.Syntax

/-!
# Semantics of infinitary first-order formulas

This file defines realization of `L_{∞ω}` formulas in a structure, with a simp lemma for every
constructor and derived connective. The branching carrier is a type parameter, so each
realization lemma is a single statement generic in the carrier and its universe: there is no
separate `L_{ω₁ω}` semantics.

Quantification extends the bound-variable valuation at the last slot, with `Fin.snoc`, as for
finitary formulas.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.Realize`: realization with free-variable and
  bound-variable valuations.
* `FirstOrder.Language.FormulaInf.Realize` and `FirstOrder.Language.SentenceInf.Realize`, with
  the low-priority simp lemmas `FormulaInf.realize_def` and `SentenceInf.realize_def` reducing
  them to bounded-formula realization once no formula- or sentence-level lemma applies.

## Main results

* One simp lemma per constructor and derived connective, each generic in the carrier and its
  universe: `realize_iSup`, `realize_iInf`, `realize_inf`, `realize_iff`, `realize_alls`, ….
* `FirstOrder.Language.BoundedFormula.realize_toInf`: the finitary embedding preserves
  realization, at every carrier.
* `FirstOrder.Language.Sentence.realize_toInf`: the sentence-level finitary embedding preserves
  satisfaction.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, whose infinitary semantics is
  `Mathlib/ModelTheory/Infinitary/Semantics.lean` in `leanprover-community/mathlib4#42758`
  (Apache 2.0) at commit `2264c2c872bb642ab519aa2288d53110f07af37d`.
* Divergences from these sources: realization laws for the added binary connectives
  (`realize_inf`, `realize_sup`, `realize_iff`); `FormulaInf.Realize` and
  `SentenceInf.Realize` are not exposed, with the simp bridges `FormulaInf.realize_def` and
  `SentenceInf.realize_def` (at priority `low`, so default-priority facts stated at the formula or
  sentence level are tried first) in their place; `realize_alls` and `realize_exs` are stated for
  bounded realization at the empty valuation of the bound-variable slots, their simp-normal form.

## Implementation notes

`BoundedFormulaInf.Realize` is exposed, as in the sources. Its pattern-matching definition
compiles through an auxiliary matcher, which is named `BoundedFormulaInf.Realize.match_1` only
when the body is exposed (otherwise the matcher gets a private, module-specific name). Exposing
it keeps that name stable, so that a downstream restatement of the same definition can be
compared with this one constant by constant.
-/

public section

universe u v u' uι w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- Realization of an infinitary bounded formula in a structure, given valuations of the free
and bound variables. One recursion serves every carrier. -/
@[expose]
def Realize {M : Type w} [L.Structure M] :
    ∀ {n}, L.BoundedFormulaInf ι α n → (α → M) → (Fin n → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, .rel R ts, v, xs => Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs)
  | _, .imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | _, .all φ, v, xs => ∀ y : M, Realize φ v (Fin.snoc xs y)
  | _, .iSup φs, v, xs => ∃ i, Realize (φs i) v xs
  | _, .iInf φs, v, xs => ∀ i, Realize (φs i) v xs

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_falsum : (falsum : L.BoundedFormulaInf ι α n).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_equal {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_rel {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (rel R ts : L.BoundedFormulaInf ι α n).Realize v xs ↔
      Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_imp {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_all {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.all.Realize v xs ↔ ∀ y : M, φ.Realize v (Fin.snoc xs y) :=
  Iff.rfl

/-- Realization of an infinitary disjunction: one statement, generic in the carrier and its
universe. -/
@[simp]
theorem realize_iSup {φs : ι → L.BoundedFormulaInf ι α n} :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  Iff.rfl

/-- Realization of an infinitary conjunction: one statement, generic in the carrier and its
universe. -/
@[simp]
theorem realize_iInf {φs : ι → L.BoundedFormulaInf ι α n} :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_not {φ : L.BoundedFormulaInf ι α n} :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormulaInf ι α n).Realize v xs ↔ True := by
  rw [top_def, realize_not, realize_falsum, not_false_eq_true]

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormulaInf ι α n).Realize v xs ↔ False := by
  rw [bot_def, realize_falsum]

@[simp]
theorem realize_inf {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp only [inf_def, realize_not, realize_imp, not_imp, not_not]

@[simp]
theorem realize_sup {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [sup_def, realize_imp, realize_not]
  tauto

@[simp]
theorem realize_iff {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormulaInf.iff_def, realize_inf, realize_imp, ← _root_.iff_def]

@[simp]
theorem realize_ex {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.ex.Realize v xs ↔ ∃ y : M, φ.Realize v (Fin.snoc xs y) := by
  simp only [BoundedFormulaInf.ex, realize_not, realize_all, not_forall, not_not]

end BoundedFormulaInf

namespace BoundedFormula

/-- The finitary embedding preserves realization, at every carrier. -/
@[simp]
theorem realize_toInf {M : Type w} [L.Structure M] :
    ∀ {n} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M),
      (toInf (ι := ι) φ).Realize v xs ↔ φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => intro v xs; simp [BoundedFormula.Realize]
  | equal => intro v xs; simp [BoundedFormula.Realize]
  | rel => intro v xs; simp [BoundedFormula.Realize]
  | imp φ ψ ihφ ihψ =>
    intro v xs
    simpa only [toInf_imp, BoundedFormulaInf.realize_imp, BoundedFormula.realize_imp] using
      imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    simpa only [toInf_all, BoundedFormulaInf.realize_all, BoundedFormula.realize_all] using
      forall_congr' fun y ↦ ih v (Fin.snoc xs y)

end BoundedFormula

/-- Realization of an `L_{∞ω}` formula, which has no bound-variable slots. -/
def FormulaInf.Realize {M : Type w} [L.Structure M] (φ : L.FormulaInf ι α) (v : α → M) : Prop :=
  BoundedFormulaInf.Realize φ v default

/-- A formula is realized when it is realized as a bounded formula with no bound variables, so the
realization lemmas for bounded formulas apply to formulas. The priority is `low` so that `simp`
tries default-priority facts stated at the formula level (hypotheses passed to `simp`, downstream
simp lemmas) before descending to bounded realization. -/
@[simp low]
theorem FormulaInf.realize_def {M : Type w} [L.Structure M] (φ : L.FormulaInf ι α) (v : α → M) :
    φ.Realize v ↔ BoundedFormulaInf.Realize φ v default :=
  Iff.rfl

section AllsExs

variable {M : Type w} [L.Structure M]

/-- Closing all bound-variable slots universally realizes as universal quantification over the
valuations of those slots. -/
@[simp]
theorem BoundedFormulaInf.realize_alls {φ : L.BoundedFormulaInf ι α n} {v : α → M} :
    BoundedFormulaInf.Realize φ.alls v default ↔ ∀ xs : Fin n → M, φ.Realize v xs := by
  induction n with
  | zero => rw [BoundedFormulaInf.alls_zero]; exact Unique.forall_iff.symm
  | succ n ih =>
    simp only [BoundedFormulaInf.alls_succ, ih, BoundedFormulaInf.realize_all]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

/-- Closing all bound-variable slots existentially realizes as existential quantification over
the valuations of those slots. -/
@[simp]
theorem BoundedFormulaInf.realize_exs {φ : L.BoundedFormulaInf ι α n} {v : α → M} :
    BoundedFormulaInf.Realize φ.exs v default ↔ ∃ xs : Fin n → M, φ.Realize v xs := by
  induction n with
  | zero => rw [BoundedFormulaInf.exs_zero]; exact Unique.exists_iff.symm
  | succ n ih =>
    simp only [BoundedFormulaInf.exs_succ, ih, BoundedFormulaInf.realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩; exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      exact ⟨Fin.init xs, xs (Fin.last n), by rwa [Fin.snoc_init_self]⟩

end AllsExs

/-- Realization of an `L_{∞ω}` sentence in a structure. -/
def SentenceInf.Realize (φ : L.SentenceInf ι) (M : Type w) [L.Structure M] : Prop :=
  FormulaInf.Realize (M := M) φ Empty.elim

/-- A sentence is realized in a structure when it is realized as a formula under the empty
valuation of its free variables. The priority is `low` for the same reason as
`FormulaInf.realize_def`. -/
@[simp low]
theorem SentenceInf.realize_def (φ : L.SentenceInf ι) (M : Type w) [L.Structure M] :
    φ.Realize M ↔ FormulaInf.Realize (M := M) φ Empty.elim :=
  Iff.rfl

/-- A conjunction of sentences holds exactly when both sentences hold. -/
@[simp]
theorem SentenceInf.realize_inf {M : Type w} [L.Structure M] {φ ψ : L.SentenceInf ι} :
    SentenceInf.Realize (φ ⊓ ψ) M ↔ φ.Realize M ∧ ψ.Realize M := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_inf]

/-- An infinitary conjunction of sentences holds exactly when every sentence holds. -/
@[simp]
theorem SentenceInf.realize_iInf {M : Type w} [L.Structure M] {φs : ι → L.SentenceInf ι} :
    SentenceInf.Realize (BoundedFormulaInf.iInf φs) M ↔ ∀ i, (φs i).Realize M := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormulaInf.realize_iInf]

/-- The finitary embedding of a sentence preserves satisfaction, at every branching carrier. -/
@[simp]
theorem Sentence.realize_toInf (φ : L.Sentence) (M : Type w) [L.Structure M] :
    SentenceInf.Realize (φ.toInf (ι := ι)) M ↔ M ⊨ φ := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormula.realize_toInf,
    Sentence.Realize, Formula.Realize, Subsingleton.elim default Empty.elim]

end Language

end FirstOrder
