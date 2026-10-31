/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics

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
      exact congrArg (fun R => rel R ts) ((Equiv.sumEmpty _ _).symm_apply_apply R)
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

/-- Abstraction agrees with Mathlib's constant abstraction on finitary formulas. -/
@[simp]
theorem constantsVarsEquiv_toInf (φ : L[[γ]].BoundedFormula α n) :
    constantsVarsEquiv (φ.toInf : L[[γ]].BoundedFormulaInf ι α n) =
      (BoundedFormula.constantsVarsEquiv φ).toInf := by
  -- Mathlib presents abstraction through its generic term-and-relation mapper, rather than
  -- constructor equations, so unfold that presentation to compare the two recursions.
  induction φ with
  | falsum => simp [BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      BoundedFormula.mapTermRel]
  | equal => simp [BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      BoundedFormula.mapTermRel]
  | rel =>
    simp [BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      BoundedFormula.mapTermRel]
    rfl
  | imp φ ψ ihφ ihψ =>
    simpa only [BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      Equiv.coe_fn_mk, BoundedFormula.mapTermRel, BoundedFormula.toInf_imp,
      constantsVarsEquiv_imp] using congrArg₂ BoundedFormulaInf.imp ihφ ihψ
  | all φ ih =>
    simpa only [BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv,
      Equiv.coe_fn_mk, BoundedFormula.mapTermRel, BoundedFormula.toInf_all,
      constantsVarsEquiv_all, id_eq] using congrArg BoundedFormulaInf.all ih

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
    have hR : (L.lhomWithConstants γ).onRelation ((Equiv.sumEmpty _ _) R) = R :=
      (Equiv.sumEmpty _ _).symm_apply_apply R
    rw [← LHom.map_onRelation (L.lhomWithConstants γ), hR]
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
