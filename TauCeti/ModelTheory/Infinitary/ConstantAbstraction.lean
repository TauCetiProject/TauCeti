/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics
public import TauCeti.ModelTheory.LanguageMap
public import TauCeti.ModelTheory.Syntax

/-!
# Abstracting constants in infinitary formulas

`BoundedFormulaInf.constantsVarsEquiv` exchanges the added constants of `L[[γ]]` for free
variables indexed by `γ`, leaving the bound positions unchanged. Its inverse interprets those
free variables as constants. This allows parameters in a sentence to be abstracted before
quantifying them, as in witness elimination and omitting-types arguments.

The equivalence works for any connective carrier, language and variable universes. In an
expansion along `lhomWithConstants`, abstraction preserves realization when the new free
variables are assigned the interpretations of the corresponding constants.

The construction follows Mathlib's `BoundedFormula.constantsVarsEquiv`, reusing
`Term.constantsVarsEquivLeft` on atoms. The infinitary conjunction and disjunction cases
act componentwise; `constantsVarsEquiv_toInf` verifies agreement with the finitary construction.
-/

public section

universe u v uι uα uγ w

namespace FirstOrder.Language.BoundedFormulaInf

variable {L : FirstOrder.Language.{u, v}} {ι : Type uι} {α : Type uα} {γ : Type uγ}

private def abstractConstants : ∀ {n : ℕ}, L[[γ]].BoundedFormulaInf ι α n →
    L.BoundedFormulaInf ι (γ ⊕ α) n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (Term.constantsVarsEquivLeft t₁) (Term.constantsVarsEquivLeft t₂)
  | _, .rel R ts => .rel ((Equiv.sumEmpty _ _) R) fun i => Term.constantsVarsEquivLeft (ts i)
  | _, .imp φ ψ => (abstractConstants φ).imp (abstractConstants ψ)
  | _, .all φ => (abstractConstants φ).all
  | _, .iSup φs => .iSup fun i => abstractConstants (φs i)
  | _, .iInf φs => .iInf fun i => abstractConstants (φs i)

private def restoreConstants : ∀ {n : ℕ}, L.BoundedFormulaInf ι (γ ⊕ α) n →
    L[[γ]].BoundedFormulaInf ι α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ =>
    .equal (Term.constantsVarsEquivLeft.symm t₁) (Term.constantsVarsEquivLeft.symm t₂)
  | _, .rel R ts =>
    .rel ((Equiv.sumEmpty _ _).symm R) fun i => Term.constantsVarsEquivLeft.symm (ts i)
  | _, .imp φ ψ => (restoreConstants φ).imp (restoreConstants ψ)
  | _, .all φ => (restoreConstants φ).all
  | _, .iSup φs => .iSup fun i => restoreConstants (φs i)
  | _, .iInf φs => .iInf fun i => restoreConstants (φs i)

/-- Exchange the added constants indexed by `γ` for free variables indexed by `γ`, preserving
all bound positions. The inverse replaces those free variables by their constants. -/
def constantsVarsEquiv {n : ℕ} :
    L[[γ]].BoundedFormulaInf ι α n ≃ L.BoundedFormulaInf ι (γ ⊕ α) n where
  toFun := abstractConstants
  invFun := restoreConstants
  left_inv φ := by
    induction φ with
    | falsum => rfl
    | equal => simp only [abstractConstants, restoreConstants, _root_.Equiv.symm_apply_apply]
    | rel R ts =>
      simp only [abstractConstants, restoreConstants, _root_.Equiv.symm_apply_apply]
      -- The inverse of sumEmpty is the relation map of lhomWithConstants (both are sumInl).
      exact congrArg (fun R => rel R ts) (lhomWithConstants_onRelation_sumEmpty R)
    | imp φ ψ ihφ ihψ => simp [abstractConstants, restoreConstants, ihφ, ihψ]
    | all φ ih => simp [abstractConstants, restoreConstants, ih]
    | iSup φs ih => simp [abstractConstants, restoreConstants, ih]
    | iInf φs ih => simp [abstractConstants, restoreConstants, ih]
  right_inv φ := by
    induction φ with
    | falsum => rfl
    | equal => simp only [abstractConstants, restoreConstants, _root_.Equiv.apply_symm_apply]
    | rel => simp only [abstractConstants, restoreConstants, _root_.Equiv.apply_symm_apply]
    | imp φ ψ ihφ ihψ => simp [abstractConstants, restoreConstants, ihφ, ihψ]
    | all φ ih => simp [abstractConstants, restoreConstants, ih]
    | iSup φs ih => simp [abstractConstants, restoreConstants, ih]
    | iInf φs ih => simp [abstractConstants, restoreConstants, ih]

variable {n : ℕ}

@[simp]
theorem constantsVarsEquiv_falsum :
    constantsVarsEquiv (.falsum : L[[γ]].BoundedFormulaInf ι α n) = .falsum := (rfl)

@[simp]
theorem constantsVarsEquiv_equal (t₁ t₂ : L[[γ]].Term (α ⊕ Fin n)) :
    constantsVarsEquiv (.equal t₁ t₂ : L[[γ]].BoundedFormulaInf ι α n) =
      .equal (Term.constantsVarsEquivLeft t₁) (Term.constantsVarsEquivLeft t₂) := (rfl)

@[simp]
theorem constantsVarsEquiv_rel {l : ℕ} (R : L[[γ]].Relations l)
    (ts : Fin l → L[[γ]].Term (α ⊕ Fin n)) :
    constantsVarsEquiv (.rel R ts : L[[γ]].BoundedFormulaInf ι α n) =
      .rel ((Equiv.sumEmpty _ _) R) (fun i => Term.constantsVarsEquivLeft (ts i)) := (rfl)

@[simp]
theorem constantsVarsEquiv_imp (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    constantsVarsEquiv (φ.imp ψ) = (constantsVarsEquiv φ).imp (constantsVarsEquiv ψ) := (rfl)

@[simp]
theorem constantsVarsEquiv_all (φ : L[[γ]].BoundedFormulaInf ι α (n + 1)) :
    constantsVarsEquiv φ.all = (constantsVarsEquiv φ).all := (rfl)

@[simp]
theorem constantsVarsEquiv_iSup (φs : ι → L[[γ]].BoundedFormulaInf ι α n) :
    constantsVarsEquiv (.iSup φs) = .iSup fun i => constantsVarsEquiv (φs i) := (rfl)

@[simp]
theorem constantsVarsEquiv_iInf (φs : ι → L[[γ]].BoundedFormulaInf ι α n) :
    constantsVarsEquiv (.iInf φs) = .iInf fun i => constantsVarsEquiv (φs i) := (rfl)

@[simp]
theorem constantsVarsEquiv_symm_falsum :
    constantsVarsEquiv.symm (.falsum : L.BoundedFormulaInf ι (γ ⊕ α) n) = .falsum := (rfl)

@[simp]
theorem constantsVarsEquiv_symm_equal (t₁ t₂ : L.Term ((γ ⊕ α) ⊕ Fin n)) :
    constantsVarsEquiv.symm (.equal t₁ t₂ : L.BoundedFormulaInf ι (γ ⊕ α) n) =
      .equal (Term.constantsVarsEquivLeft.symm t₁) (Term.constantsVarsEquivLeft.symm t₂) := (rfl)

@[simp]
theorem constantsVarsEquiv_symm_rel {l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term ((γ ⊕ α) ⊕ Fin n)) :
    constantsVarsEquiv.symm (.rel R ts : L.BoundedFormulaInf ι (γ ⊕ α) n) =
      .rel ((Equiv.sumEmpty _ _).symm R) (fun i => Term.constantsVarsEquivLeft.symm (ts i)) := (rfl)

@[simp]
theorem constantsVarsEquiv_symm_imp (φ ψ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    constantsVarsEquiv.symm (φ.imp ψ) =
      (constantsVarsEquiv.symm φ).imp (constantsVarsEquiv.symm ψ) := (rfl)

@[simp]
theorem constantsVarsEquiv_symm_all (φ : L.BoundedFormulaInf ι (γ ⊕ α) (n + 1)) :
    constantsVarsEquiv.symm φ.all = (constantsVarsEquiv.symm φ).all := (rfl)

@[simp]
theorem constantsVarsEquiv_symm_iSup (φs : ι → L.BoundedFormulaInf ι (γ ⊕ α) n) :
    constantsVarsEquiv.symm (.iSup φs) = .iSup fun i => constantsVarsEquiv.symm (φs i) := (rfl)

@[simp]
theorem constantsVarsEquiv_symm_iInf (φs : ι → L.BoundedFormulaInf ι (γ ⊕ α) n) :
    constantsVarsEquiv.symm (.iInf φs) = .iInf fun i => constantsVarsEquiv.symm (φs i) := (rfl)

@[simp]
theorem constantsVarsEquiv_bot :
    constantsVarsEquiv (⊥ : L[[γ]].BoundedFormulaInf ι α n) = ⊥ := (rfl)

@[simp]
theorem constantsVarsEquiv_not (φ : L[[γ]].BoundedFormulaInf ι α n) :
    constantsVarsEquiv φ.not = (constantsVarsEquiv φ).not := by
  simp only [BoundedFormulaInf.not, constantsVarsEquiv_imp, constantsVarsEquiv_falsum]

@[simp]
theorem constantsVarsEquiv_top :
    constantsVarsEquiv (⊤ : L[[γ]].BoundedFormulaInf ι α n) = ⊤ := by
  simp only [top_def, constantsVarsEquiv_not, constantsVarsEquiv_falsum]

@[simp]
theorem constantsVarsEquiv_ex (φ : L[[γ]].BoundedFormulaInf ι α (n + 1)) :
    constantsVarsEquiv φ.ex = (constantsVarsEquiv φ).ex := by
  simp only [BoundedFormulaInf.ex, constantsVarsEquiv_not, constantsVarsEquiv_all]

@[simp]
theorem constantsVarsEquiv_inf (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    constantsVarsEquiv (φ ⊓ ψ) = constantsVarsEquiv φ ⊓ constantsVarsEquiv ψ := by
  simp only [inf_def, constantsVarsEquiv_not, constantsVarsEquiv_imp]

@[simp]
theorem constantsVarsEquiv_sup (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    constantsVarsEquiv (φ ⊔ ψ) = constantsVarsEquiv φ ⊔ constantsVarsEquiv ψ := by
  simp only [sup_def, constantsVarsEquiv_not, constantsVarsEquiv_imp]

@[simp]
theorem constantsVarsEquiv_iff (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    constantsVarsEquiv (φ.iff ψ) = (constantsVarsEquiv φ).iff (constantsVarsEquiv ψ) := by
  simp only [iff_def, constantsVarsEquiv_inf, constantsVarsEquiv_imp]

@[simp]
theorem constantsVarsEquiv_alls :
    ∀ {n} (φ : L[[γ]].BoundedFormulaInf ι α n),
      constantsVarsEquiv φ.alls = (constantsVarsEquiv φ).alls
  | 0, φ => by rw [alls_zero, alls_zero]
  | _ + 1, φ => by
    rw [alls_succ, alls_succ, constantsVarsEquiv_alls φ.all, constantsVarsEquiv_all]

@[simp]
theorem constantsVarsEquiv_exs :
    ∀ {n} (φ : L[[γ]].BoundedFormulaInf ι α n),
      constantsVarsEquiv φ.exs = (constantsVarsEquiv φ).exs
  | 0, φ => by rw [exs_zero, exs_zero]
  | _ + 1, φ => by
    rw [exs_succ, exs_succ, constantsVarsEquiv_exs φ.ex, constantsVarsEquiv_ex]

@[simp]
theorem constantsVarsEquiv_symm_bot :
    constantsVarsEquiv.symm (⊥ : L.BoundedFormulaInf ι (γ ⊕ α) n) = ⊥ := (rfl)

@[simp]
theorem constantsVarsEquiv_symm_not (φ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    constantsVarsEquiv.symm φ.not = (constantsVarsEquiv.symm φ).not := by
  simp only [BoundedFormulaInf.not, constantsVarsEquiv_symm_imp, constantsVarsEquiv_symm_falsum]

@[simp]
theorem constantsVarsEquiv_symm_top :
    constantsVarsEquiv.symm (⊤ : L.BoundedFormulaInf ι (γ ⊕ α) n) = ⊤ := by
  simp only [top_def, constantsVarsEquiv_symm_not, constantsVarsEquiv_symm_falsum]

@[simp]
theorem constantsVarsEquiv_symm_ex (φ : L.BoundedFormulaInf ι (γ ⊕ α) (n + 1)) :
    constantsVarsEquiv.symm φ.ex = (constantsVarsEquiv.symm φ).ex := by
  simp only [BoundedFormulaInf.ex, constantsVarsEquiv_symm_not, constantsVarsEquiv_symm_all]

@[simp]
theorem constantsVarsEquiv_symm_inf (φ ψ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    constantsVarsEquiv.symm (φ ⊓ ψ) = constantsVarsEquiv.symm φ ⊓ constantsVarsEquiv.symm ψ := by
  simp only [inf_def, constantsVarsEquiv_symm_not, constantsVarsEquiv_symm_imp]

@[simp]
theorem constantsVarsEquiv_symm_sup (φ ψ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    constantsVarsEquiv.symm (φ ⊔ ψ) = constantsVarsEquiv.symm φ ⊔ constantsVarsEquiv.symm ψ := by
  simp only [sup_def, constantsVarsEquiv_symm_not, constantsVarsEquiv_symm_imp]

@[simp]
theorem constantsVarsEquiv_symm_iff (φ ψ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    constantsVarsEquiv.symm (φ.iff ψ) =
      (constantsVarsEquiv.symm φ).iff (constantsVarsEquiv.symm ψ) := by
  simp only [iff_def, constantsVarsEquiv_symm_inf, constantsVarsEquiv_symm_imp]

@[simp]
theorem constantsVarsEquiv_symm_alls :
    ∀ {n} (φ : L.BoundedFormulaInf ι (γ ⊕ α) n),
      constantsVarsEquiv.symm φ.alls = (constantsVarsEquiv.symm φ).alls
  | 0, φ => by rw [alls_zero, alls_zero]
  | _ + 1, φ => by
    rw [alls_succ, alls_succ, constantsVarsEquiv_symm_alls φ.all, constantsVarsEquiv_symm_all]

@[simp]
theorem constantsVarsEquiv_symm_exs :
    ∀ {n} (φ : L.BoundedFormulaInf ι (γ ⊕ α) n),
      constantsVarsEquiv.symm φ.exs = (constantsVarsEquiv.symm φ).exs
  | 0, φ => by rw [exs_zero, exs_zero]
  | _ + 1, φ => by
    rw [exs_succ, exs_succ, constantsVarsEquiv_symm_exs φ.ex, constantsVarsEquiv_symm_ex]

/-- Abstraction agrees with Mathlib's constant abstraction on finitary formulas. -/
@[simp]
theorem constantsVarsEquiv_toInf (φ : L[[γ]].BoundedFormula α n) :
    constantsVarsEquiv (φ.toInf : L[[γ]].BoundedFormulaInf ι α n) =
      (BoundedFormula.constantsVarsEquiv φ).toInf := by
  induction φ with
  | falsum => simp only [BoundedFormula.constantsVarsEquiv_falsum, BoundedFormula.toInf_falsum,
      constantsVarsEquiv_falsum]
  | equal => simp only [BoundedFormula.constantsVarsEquiv_equal, BoundedFormula.toInf_equal,
      constantsVarsEquiv_equal]
  | rel => simp only [BoundedFormula.constantsVarsEquiv_rel, BoundedFormula.toInf_rel,
      constantsVarsEquiv_rel]
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.constantsVarsEquiv_imp, BoundedFormula.toInf_imp,
      constantsVarsEquiv_imp, ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormula.constantsVarsEquiv_all, BoundedFormula.toInf_all,
      constantsVarsEquiv_all, ih]

/-- Restoring constants agrees with Mathlib's inverse abstraction on finitary formulas. -/
@[simp]
theorem constantsVarsEquiv_symm_toInf (φ : L.BoundedFormula (γ ⊕ α) n) :
    constantsVarsEquiv.symm (φ.toInf : L.BoundedFormulaInf ι (γ ⊕ α) n) =
      (BoundedFormula.constantsVarsEquiv.symm φ).toInf := by
  apply constantsVarsEquiv.symm_apply_eq.mpr
  simp only [constantsVarsEquiv_toInf, _root_.Equiv.apply_symm_apply]

/-- Abstraction preserves truth when its new free variables denote the added constants. -/
@[simp]
theorem realize_constantsVarsEquiv {M : Type w} [L.Structure M] [L[[γ]].Structure M]
    [(L.lhomWithConstants γ).IsExpansionOn M] (φ : L[[γ]].BoundedFormulaInf ι α n)
    (v : α → M) (xs : Fin n → M) :
    (constantsVarsEquiv φ).Realize (Sum.elim (fun c => (L.con c : M)) v) xs ↔
      φ.Realize v xs := by
  induction φ with
  | falsum => simp
  | equal => simp only [constantsVarsEquiv_equal, realize_equal,
      Term.realize_constantsVarsEquivLeft]
  | rel R ts =>
    simp only [constantsVarsEquiv_rel, realize_rel, Term.realize_constantsVarsEquivLeft]
    rw [← LHom.map_onRelation (L.lhomWithConstants γ), lhomWithConstants_onRelation_sumEmpty]
  | imp φ ψ ihφ ihψ => simp [realize_imp, ihφ, ihψ]
  | all φ ih => simp [realize_all, ih]
  | iSup φs ih => simp [realize_iSup, ih]
  | iInf φs ih => simp [realize_iInf, ih]

/-- Restoring constants preserves truth at the assignment given by their interpretations. -/
@[simp]
theorem realize_constantsVarsEquiv_symm {M : Type w} [L.Structure M] [L[[γ]].Structure M]
    [(L.lhomWithConstants γ).IsExpansionOn M] (φ : L.BoundedFormulaInf ι (γ ⊕ α) n)
    (v : α → M) (xs : Fin n → M) :
    (constantsVarsEquiv.symm φ).Realize v xs ↔
      φ.Realize (Sum.elim (fun c => (L.con c : M)) v) xs := by
  have h := (realize_constantsVarsEquiv (constantsVarsEquiv.symm φ) v xs).symm
  rw [constantsVarsEquiv.apply_symm_apply] at h
  exact h

end FirstOrder.Language.BoundedFormulaInf
