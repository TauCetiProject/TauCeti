/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Substitution

/-!
# Opening the bound positions of an infinitary formula

`BoundedFormulaInf.toFormula` turns the in-scope bound positions of a formula into additional
free variables. Variables bound by quantifiers inside the formula remain bound. Its realization
law allows a formula with parameters in bound positions to be used as an ordinary formula with
free parameters, without changing its meaning. The construction works for every branching
carrier, including the empty carrier.

The constructor equations and compatibility with the first-order embedding describe the syntax;
`BoundedFormulaInf.realize_toFormula` describes the semantics.

The definition and the quantifier step of the realization proof follow Mathlib's
`FirstOrder.Language.BoundedFormula.toFormula` and `BoundedFormula.realize_toFormula` in
`Mathlib/ModelTheory/Syntax.lean` and `Mathlib/ModelTheory/Semantics.lean` (Aaron Anderson).
The two infinitary connectives are handled componentwise.
-/

public section

universe u v uι uα w

namespace FirstOrder.Language.BoundedFormulaInf

variable {L : FirstOrder.Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}

/-- Turn the `n` in-scope bound positions into free variables of type `α ⊕ Fin n`.
Quantifiers within the formula still bind their own variables. -/
def toFormula : ∀ {n}, L.BoundedFormulaInf ι α n → L.FormulaInf ι (α ⊕ Fin n)
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (t₁.relabel Sum.inl) (t₂.relabel Sum.inl)
  | _, .rel R ts => .rel R fun i => (ts i).relabel Sum.inl
  | _, .imp φ ψ => (toFormula φ).imp (toFormula ψ)
  | _, .all φ =>
    (TauCeti.BoundedFormulaInf.relabel
      (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))
      (toFormula φ)).all
  | _, .iSup φs => .iSup fun i => toFormula (φs i)
  | _, .iInf φs => .iInf fun i => toFormula (φs i)

/-- Opening positions fixes falsum. -/
@[simp]
theorem toFormula_falsum : toFormula (.falsum : L.BoundedFormulaInf ι α n) = .falsum :=
  (rfl)

/-- Opening an equality regards the variables of its terms as free variables. -/
@[simp]
theorem toFormula_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    toFormula (.equal t₁ t₂ : L.BoundedFormulaInf ι α n) =
      .equal (t₁.relabel Sum.inl) (t₂.relabel Sum.inl) := (rfl)

/-- Opening a relation atom regards the variables of its terms as free variables. -/
@[simp]
theorem toFormula_rel {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)) :
    toFormula (.rel R ts : L.BoundedFormulaInf ι α n) =
      .rel R (fun i => (ts i).relabel Sum.inl) := (rfl)

/-- Opening positions commutes with implication. -/
@[simp]
theorem toFormula_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    toFormula (φ.imp ψ) = (toFormula φ).imp (toFormula ψ) := (rfl)

/-- Opening the body of a quantifier makes its last position free temporarily; relabelling
binds that position again, leaving only the original in-scope positions free. -/
@[simp]
theorem toFormula_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    toFormula φ.all =
      (TauCeti.BoundedFormulaInf.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))
        (toFormula φ)).all := (rfl)

/-- Opening positions commutes with infinitary disjunction. -/
@[simp]
theorem toFormula_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    toFormula (.iSup φs) = .iSup fun i => toFormula (φs i) := (rfl)

/-- Opening positions commutes with infinitary conjunction. -/
@[simp]
theorem toFormula_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    toFormula (.iInf φs) = .iInf fun i => toFormula (φs i) := (rfl)

/-- Opening positions fixes bottom. -/
@[simp]
theorem toFormula_bot : toFormula (⊥ : L.BoundedFormulaInf ι α n) = ⊥ := (rfl)

/-- Opening positions commutes with negation. -/
@[simp]
theorem toFormula_not (φ : L.BoundedFormulaInf ι α n) :
    toFormula φ.not = (toFormula φ).not := (rfl)

/-- Opening positions fixes top. -/
@[simp]
theorem toFormula_top : toFormula (⊤ : L.BoundedFormulaInf ι α n) = ⊤ := by
  simp [top_def]

/-- Opening positions commutes with binary conjunction. -/
@[simp]
theorem toFormula_inf (φ ψ : L.BoundedFormulaInf ι α n) :
    toFormula (φ ⊓ ψ) = toFormula φ ⊓ toFormula ψ := (rfl)

/-- Opening positions commutes with binary disjunction. -/
@[simp]
theorem toFormula_sup (φ ψ : L.BoundedFormulaInf ι α n) :
    toFormula (φ ⊔ ψ) = toFormula φ ⊔ toFormula ψ := (rfl)

/-- Opening positions commutes with logical equivalence. -/
@[simp]
theorem toFormula_iff (φ ψ : L.BoundedFormulaInf ι α n) :
    toFormula (φ.iff ψ) = (toFormula φ).iff (toFormula ψ) := by
  simp [iff_def]

/-- Opening the body of an existential quantifier keeps its last position bound. -/
@[simp]
theorem toFormula_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    toFormula φ.ex =
      (TauCeti.BoundedFormulaInf.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))
        (toFormula φ)).ex := by
  simp [BoundedFormulaInf.ex]

/-- Opening the bound positions preserves bounded realization for any assignment to the empty
bound context of the resulting formula. -/
@[simp]
theorem realize_toFormula_bounded {M : Type w} [L.Structure M] (φ : L.BoundedFormulaInf ι α n)
    (v : α ⊕ Fin n → M) (xs : Fin 0 → M) :
    BoundedFormulaInf.Realize (toFormula φ) v xs ↔
      φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [Sum.elim_comp_inl_inr]
  | rel R ts => simp [Sum.elim_comp_inl_inr]
  | imp φ ψ ihφ ihψ =>
    simpa only [toFormula_imp, realize_imp] using
      imp_congr (ihφ v) (ihψ v)
  | all φ ih =>
    simp only [toFormula_all, realize_all]
    refine forall_congr' fun a => ?_
    have h := ih (Sum.elim (v ∘ Sum.inl) (Fin.snoc (v ∘ Sum.inr) a))
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    rw [← h, TauCeti.BoundedFormulaInf.realize_relabel, iff_iff_eq]
    -- Compare the free-variable assignments and the empty bound assignments of type Fin 0 → M.
    congr 1
    · funext x
      rcases x with x | x
      · simp
      · induction x using Fin.lastCases with
        | last => simp [Fin.snoc]
        | cast x => simp [Function.comp_def]
    · exact Subsingleton.elim _ _
  | iSup φs ih =>
    simpa only [toFormula_iSup, realize_iSup] using
      exists_congr (fun i => ih i v)
  | iInf φs ih =>
    simpa only [toFormula_iInf, realize_iInf] using
      forall_congr' (fun i => ih i v)

/-- Opening the bound positions preserves realization: the left and right parts of the new
free-variable assignment supply the old free-variable and bound-position assignments. -/
@[simp]
theorem realize_toFormula {M : Type w} [L.Structure M] (φ : L.BoundedFormulaInf ι α n)
    (v : α ⊕ Fin n → M) :
    FormulaInf.Realize (toFormula φ) v ↔ φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  rw [FormulaInf.realize_def]
  exact realize_toFormula_bounded φ v default

/-- Opening bound positions commutes with embedding a first-order formula. -/
@[simp]
theorem toFormula_toInf (φ : L.BoundedFormula α n) :
    toFormula (φ.toInf : L.BoundedFormulaInf ι α n) = φ.toFormula.toInf := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [Term.equal, Term.bdEqual]
  | rel R ts => simp [Relations.formula, Relations.boundedFormula]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormula.toInf_all, toFormula_all, ih,
      TauCeti.BoundedFormulaInf.relabel_toInf, BoundedFormula.toFormula]

end FirstOrder.Language.BoundedFormulaInf
