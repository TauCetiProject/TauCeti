/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.ConstantSupport
public import TauCeti.ModelTheory.Infinitary.FreeVarSupport
public import TauCeti.ModelTheory.Infinitary.Semantics
public import TauCeti.ModelTheory.Infinitary.Symbols
public import TauCeti.ModelTheory.LanguageMap
public import TauCeti.ModelTheory.Syntax

/-!
# Abstracting constants in infinitary formulas

`BoundedFormulaInf.constantsVarsEquiv` exchanges the added constants of `L[[γ]]` for free
variables indexed by `γ`, leaving the bound positions unchanged. Its inverse interprets those
free variables as constants. `BoundedFormulaInf.abstractConst c φ` abstracts a single added
constant `L.con c` of `φ : L[[γ]].BoundedFormulaInf ι α n` into the new outermost bound slot
`Fin.last n`, leaving all other constants, free variables and bound slots unchanged. This allows
parameters in a sentence to be abstracted before quantifying them, as in witness elimination and
omitting-types arguments.

The equivalence and single-constant abstraction work for any connective carrier, language and
variable universes. In an expansion along `lhomWithConstants`, abstraction preserves realization
when the new free variables or bound slot are assigned the interpretations of the corresponding
constants, while preserving occurring relation and non-constant function symbols and removing `c`
from the constant support.

The construction of `constantsVarsEquiv` follows Mathlib's `BoundedFormula.constantsVarsEquiv`,
reusing `Term.constantsVarsEquivLeft` on atoms. The infinitary conjunction and disjunction cases
act componentwise; `constantsVarsEquiv_toInf` verifies agreement with the finitary construction.
Single-constant abstraction `abstractConst` corresponds to `abstractJConst` of
`cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
`InfinitaryLogic/Methods/Interpolation/ConstantElimination.lean`, generalized here to arbitrary
carriers, constant types, free-variable types, bound arities and language universes by factoring
through `constantsVarsEquiv` and `TauCeti.BoundedFormulaInf.relabel`.
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

/-! ### Occurring symbols and supports under constant abstraction -/

/-- Abstracting constants projects the occurring relation symbols to `L`. -/
@[simp]
theorem relationsIn_constantsVarsEquiv (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (constantsVarsEquiv φ).relationsIn =
      (fun s => ⟨s.1, (Equiv.sumEmpty _ _) s.2⟩) '' φ.relationsIn := by
  induction φ with
  | imp _ _ ihφ ihψ => simp [ihφ, ihψ, Set.image_union]
  | all _ ih => simp [ih]
  | iSup _ ih | iInf _ ih => simp [ih, Set.image_iUnion]
  | _ => simp

private theorem constantsVarsEquiv_symm_rel_onRelation {l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term ((γ ⊕ α) ⊕ Fin n)) :
    constantsVarsEquiv.symm (.rel R ts : L.BoundedFormulaInf ι (γ ⊕ α) n) =
      .rel ((L.lhomWithConstants γ).onRelation R)
        (fun i => Term.constantsVarsEquivLeft.symm (ts i)) := by
  -- `constantsVarsEquiv_symm_rel` types `(Equiv.sumEmpty _ _).symm R` in the unfolded sum rather
  -- than `L[[γ]].Relations l`, blocking `implicit`-transparency matching in downstream rewrites.
  rw [constantsVarsEquiv_symm_rel]
  refine congrArg (fun R' => rel R' _) ?_
  have h := lhomWithConstants_onRelation_sumEmpty (L := L) (γ := γ) ((Equiv.sumEmpty _ _).symm R)
  rwa [_root_.Equiv.apply_symm_apply] at h

/-- Restoring constants embeds the occurring relation symbols along `lhomWithConstants`. -/
@[simp]
theorem relationsIn_constantsVarsEquiv_symm (φ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    (constantsVarsEquiv.symm φ).relationsIn =
      (fun s => ⟨s.1, (L.lhomWithConstants γ).onRelation s.2⟩) '' φ.relationsIn := by
  induction φ with
  | rel R _ =>
    rw [constantsVarsEquiv_symm_rel_onRelation, relationsIn_rel, relationsIn_rel,
      Set.image_singleton]
  | imp _ _ ihφ ihψ => simp [ihφ, ihψ, Set.image_union]
  | all _ ih => simp [ih]
  | iSup _ ih | iInf _ ih => simp [ih, Set.image_iUnion]
  | _ => simp

private theorem constantsVarsEquivLeft_symm_var_inl_inl {β : Type*} (c : γ) :
    Term.constantsVarsEquivLeft.symm (Term.var (Sum.inl (Sum.inl c)) : L.Term ((γ ⊕ α) ⊕ β)) =
      (L.con c).term := by
  -- Mathlib's `Term.varsToConstants` unfolds to `Constants.term (Sum.inr c)`, matching `L.con c`.
  rw [Term.constantsVarsEquivLeft_symm_apply]
  rfl

private theorem constantsVarsEquivLeft_symm_func {β : Type*} {l : ℕ} (f : L.Functions l)
    (ts : Fin l → L.Term ((γ ⊕ α) ⊕ β)) :
    Term.constantsVarsEquivLeft.symm (Term.func f ts) =
      Term.func ((L.lhomWithConstants γ).onFunction f)
        fun i => Term.constantsVarsEquivLeft.symm (ts i) := by
  -- `Term.varsToConstants` maps `f` to `Sum.inl f`, matching `lhomWithConstants`.
  rw [Term.constantsVarsEquivLeft_symm_apply]
  rfl

/-- Restoring constants embeds the occurring function symbols of `L` and adds the constants
corresponding to the left free variables. -/
@[simp]
theorem functionsIn_constantsVarsEquiv_symm (φ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    (constantsVarsEquiv.symm φ).functionsIn =
      (fun s => ⟨s.1, (L.lhomWithConstants γ).onFunction s.2⟩) '' φ.functionsIn ∪
        (fun c => (⟨0, L.con c⟩ : Σ k, L[[γ]].Functions k)) '' (Sum.inl ⁻¹' φ.freeVarSupport) := by
  classical
  have hterm {k : ℕ} (t : L.Term ((γ ⊕ α) ⊕ Fin k)) :
      (Term.constantsVarsEquivLeft.symm t).functionsIn =
        (fun s => ⟨s.1, (L.lhomWithConstants γ).onFunction s.2⟩) '' t.functionsIn ∪
          (fun c => (⟨0, L.con c⟩ : Σ m, L[[γ]].Functions m)) ''
            (Sum.inl ⁻¹' (t.varFinsetLeft : Set (γ ⊕ α))) := by
    induction t with
    | var x =>
      rcases x with (c | a) | i
      · rw [constantsVarsEquivLeft_symm_var_inl_inl]
        ext s; simp [Constants.term, Term.varFinsetLeft, eq_comm]
      · ext s; simp [Term.varFinsetLeft]
      · ext s; simp [Term.varFinsetLeft]
    | func f ts ih =>
      rw [constantsVarsEquivLeft_symm_func, Term.functionsIn_func, Term.functionsIn_func]
      ext s
      simp only [ih, Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image,
        Set.mem_preimage, Finset.mem_coe, Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ,
        true_and]
      aesop
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [constantsVarsEquiv_symm_equal, functionsIn_equal, freeVarSupport_equal, hterm,
      Set.image_union, Set.preimage_union]
    ext; simp only [Set.mem_union]; tauto
  | rel R _ =>
    simp only [constantsVarsEquiv_symm_rel_onRelation, functionsIn_rel, freeVarSupport_rel, hterm,
      Set.image_iUnion, Set.preimage_iUnion, Set.iUnion_union_distrib]
  | imp _ _ ihφ ihψ =>
    simp only [constantsVarsEquiv_symm_imp, functionsIn_imp, freeVarSupport_imp, ihφ, ihψ,
      Set.image_union, Set.preimage_union]
    ext; simp only [Set.mem_union]; tauto
  | all _ ih => simp [ih]
  | iSup _ ih | iInf _ ih =>
    simp only [constantsVarsEquiv_symm_iSup, constantsVarsEquiv_symm_iInf, functionsIn_iSup,
      functionsIn_iInf, freeVarSupport_iSup, freeVarSupport_iInf, ih, Set.image_iUnion,
      Set.preimage_iUnion, Set.iUnion_union_distrib]

/-- Restoring constants turns the left free variables into the constant support. -/
@[simp]
theorem constantSupport_constantsVarsEquiv_symm (φ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    (constantsVarsEquiv.symm φ).constantSupport = Sum.inl ⁻¹' φ.freeVarSupport := by
  ext c
  simp only [mem_constantSupport, functionsIn_constantsVarsEquiv_symm, Set.mem_union,
    Set.mem_image, Set.mem_preimage]
  refine ⟨?_, fun hc => .inr ⟨c, hc, rfl⟩⟩
  rintro (⟨⟨k, f⟩, -, hm⟩ | ⟨d, hd, hm⟩)
  · obtain ⟨rfl, hf⟩ := Sigma.mk.inj_iff.1 hm
    exact (Sum.inl_ne_inr (eq_of_heq hf)).elim
  · exact Sum.inr_injective (eq_of_heq (Sigma.mk.inj hm).2) ▸ hd

/-- Restoring constants keeps the right free variables as the free-variable support. -/
@[simp]
theorem freeVarSupport_constantsVarsEquiv_symm (φ : L.BoundedFormulaInf ι (γ ⊕ α) n) :
    (constantsVarsEquiv.symm φ).freeVarSupport = Sum.inr ⁻¹' φ.freeVarSupport := by
  classical
  have hterm {k : ℕ} (t : L.Term ((γ ⊕ α) ⊕ Fin k)) :
      ((Term.constantsVarsEquivLeft.symm t).varFinsetLeft : Set α) =
        Sum.inr ⁻¹' (t.varFinsetLeft : Set (γ ⊕ α)) := by
    induction t with
    | var x => rcases x with (c | a) | i <;> · ext; simp [Constants.term, Term.varFinsetLeft]
    | func f ts ih =>
      simp only [Term.constantsVarsEquivLeft_symm_apply, Term.relabel, Term.varsToConstants]
      ext b
      simp only [Finset.mem_coe, Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ,
        true_and, Set.mem_preimage]
      exact exists_congr fun i => Set.ext_iff.1 (ih i) b
  induction φ with
  | falsum => simp
  | equal _ _ =>
    rw [constantsVarsEquiv_symm_equal, freeVarSupport_equal, freeVarSupport_equal]
    simp only [hterm, Set.preimage_union]
  | rel R _ =>
    simp only [constantsVarsEquiv_symm_rel_onRelation, freeVarSupport_rel, hterm,
      Set.preimage_iUnion]
  | imp _ _ ihφ ihψ => simp [ihφ, ihψ, Set.preimage_union]
  | all _ ih => simp [ih]
  | iSup _ ih | iInf _ ih => simp [ih, Set.preimage_iUnion]

/-- Abstracting constants splits the free-variable support into the constant support on the left
and the original free-variable support on the right. -/
@[simp]
theorem freeVarSupport_constantsVarsEquiv (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (constantsVarsEquiv φ).freeVarSupport =
      Sum.inl '' φ.constantSupport ∪ Sum.inr '' φ.freeVarSupport := by
  have hc := constantSupport_constantsVarsEquiv_symm (constantsVarsEquiv φ)
  have ha := freeVarSupport_constantsVarsEquiv_symm (constantsVarsEquiv φ)
  rw [constantsVarsEquiv.symm_apply_apply] at hc ha
  ext (_ | _) <;> simp [hc, ha]

/-- Abstracting constants keeps the non-constant function symbols of `φ`. -/
@[simp]
theorem functionsIn_constantsVarsEquiv (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (constantsVarsEquiv φ).functionsIn =
      (fun s => ⟨s.1, (L.lhomWithConstants γ).onFunction s.2⟩) ⁻¹' φ.functionsIn := by
  have h := functionsIn_constantsVarsEquiv_symm (constantsVarsEquiv φ)
  rw [constantsVarsEquiv.symm_apply_apply] at h
  ext ⟨k, f⟩
  simp only [Set.mem_preimage, h, Set.mem_union, Set.mem_image]
  refine ⟨fun hf => .inl ⟨⟨k, f⟩, hf, rfl⟩, ?_⟩
  rintro (⟨⟨m, f'⟩, hf', hm⟩ | ⟨c, -, hm⟩)
  · obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.1 hm
    exact (L.lhomWithConstants_injective γ).onFunction (eq_of_heq heq) ▸ hf'
  · obtain ⟨rfl, heq⟩ := Sigma.mk.inj_iff.1 hm
    exact (Sum.inr_ne_inl (eq_of_heq heq)).elim

/-! ### Abstracting a single constant into the outermost bound slot -/

/-- Abstract a single added constant `L.con c` of `φ : L[[γ]].BoundedFormulaInf ι α n` into the
new outermost bound slot `Fin.last n`, keeping all other constants, free variables and bound
positions unchanged. -/
def abstractConst [DecidableEq γ] (c : γ) (φ : L[[γ]].BoundedFormulaInf ι α n) :
    L[[γ]].BoundedFormulaInf ι α (n + 1) :=
  constantsVarsEquiv.symm
    (mapBound (Fin.addCases (fun _ : Fin 1 => Fin.last n) Fin.castSucc)
      (TauCeti.BoundedFormulaInf.relabel
        (Sum.elim (fun d => if d = c then Sum.inr 0 else Sum.inl (Sum.inl d))
          (Sum.inl ∘ Sum.inr))
        (constantsVarsEquiv φ)))

/-- Unfolding lemma for `BoundedFormulaInf.abstractConst`. -/
theorem abstractConst_def [DecidableEq γ] (c : γ) (φ : L[[γ]].BoundedFormulaInf ι α n) :
    abstractConst c φ =
      constantsVarsEquiv.symm
        (mapBound (Fin.addCases (fun _ : Fin 1 => Fin.last n) Fin.castSucc)
          (TauCeti.BoundedFormulaInf.relabel
            (Sum.elim (fun d => if d = c then Sum.inr 0 else Sum.inl (Sum.inl d))
              (Sum.inl ∘ Sum.inr))
            (constantsVarsEquiv φ))) := (rfl)

@[simp]
theorem abstractConst_falsum [DecidableEq γ] (c : γ) :
    abstractConst c (.falsum : L[[γ]].BoundedFormulaInf ι α n) = .falsum := by
  simp [abstractConst_def]

@[simp]
theorem abstractConst_bot [DecidableEq γ] (c : γ) :
    abstractConst c (⊥ : L[[γ]].BoundedFormulaInf ι α n) = ⊥ :=
  abstractConst_falsum c

@[simp]
theorem abstractConst_imp [DecidableEq γ] (c : γ) (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    abstractConst c (φ.imp ψ) = (abstractConst c φ).imp (abstractConst c ψ) := by
  simp [abstractConst_def]

@[simp]
theorem abstractConst_not [DecidableEq γ] (c : γ) (φ : L[[γ]].BoundedFormulaInf ι α n) :
    abstractConst c φ.not = (abstractConst c φ).not := by simp [BoundedFormulaInf.not]

@[simp]
theorem abstractConst_top [DecidableEq γ] (c : γ) :
    abstractConst c (⊤ : L[[γ]].BoundedFormulaInf ι α n) = ⊤ := by simp [top_def]

@[simp]
theorem abstractConst_inf [DecidableEq γ] (c : γ) (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    abstractConst c (φ ⊓ ψ) = abstractConst c φ ⊓ abstractConst c ψ := by simp [inf_def]

@[simp]
theorem abstractConst_sup [DecidableEq γ] (c : γ) (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    abstractConst c (φ ⊔ ψ) = abstractConst c φ ⊔ abstractConst c ψ := by simp [sup_def]

@[simp]
theorem abstractConst_iff [DecidableEq γ] (c : γ) (φ ψ : L[[γ]].BoundedFormulaInf ι α n) :
    abstractConst c (φ.iff ψ) = (abstractConst c φ).iff (abstractConst c ψ) := by simp [iff_def]

@[simp]
theorem abstractConst_iSup [DecidableEq γ] (c : γ) (φs : ι → L[[γ]].BoundedFormulaInf ι α n) :
    abstractConst c (.iSup φs) = .iSup fun i => abstractConst c (φs i) := by
  simp [abstractConst_def]

@[simp]
theorem abstractConst_iInf [DecidableEq γ] (c : γ) (φs : ι → L[[γ]].BoundedFormulaInf ι α n) :
    abstractConst c (.iInf φs) = .iInf fun i => abstractConst c (φs i) := by
  simp [abstractConst_def]

/-- Abstracting a constant preserves the occurring relation symbols. -/
@[simp]
theorem relationsIn_abstractConst [DecidableEq γ] (c : γ) (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (abstractConst c φ).relationsIn = φ.relationsIn := by
  rw [abstractConst_def, relationsIn_constantsVarsEquiv_symm, relationsIn_mapBound,
    TauCeti.BoundedFormulaInf.relationsIn_relabel, relationsIn_constantsVarsEquiv, Set.image_image]
  rw [show (fun s : Σ k, L[[γ]].Relations k =>
      (⟨s.1, (L.lhomWithConstants γ).onRelation ((Equiv.sumEmpty _ _) s.2)⟩ :
        Σ k, L[[γ]].Relations k)) = id from funext fun ⟨_, R⟩ =>
      Sigma.ext rfl (heq_of_eq (lhomWithConstants_onRelation_sumEmpty R)), Set.image_id]

/-- Abstracting `c` removes `c` from the constant support and keeps all other constants. -/
@[simp]
theorem constantSupport_abstractConst [DecidableEq γ] (c : γ)
    (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (abstractConst c φ).constantSupport = φ.constantSupport \ {c} := by
  rw [abstractConst_def, constantSupport_constantsVarsEquiv_symm, freeVarSupport_mapBound,
    TauCeti.BoundedFormulaInf.freeVarSupport_relabel, freeVarSupport_constantsVarsEquiv]
  ext d
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
  refine ⟨?_, fun ⟨hd, hdc⟩ => ⟨Sum.inl d, .inl ⟨d, hd, rfl⟩, by simp [hdc]⟩⟩
  rintro ⟨_, (⟨d', hd', rfl⟩ | ⟨_, _, rfl⟩), hx⟩
  · by_cases hdc : d' = c <;> simp_all
  · simp at hx

/-- Abstracting `c` removes `⟨0, L.con c⟩` from the occurring function symbols and keeps all other
function symbols. -/
@[simp]
theorem functionsIn_abstractConst [DecidableEq γ] (c : γ)
    (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (abstractConst c φ).functionsIn = φ.functionsIn \ {⟨0, L.con c⟩} := by
  have heq : (constantsVarsEquiv (abstractConst c φ)).functionsIn =
      (constantsVarsEquiv φ).functionsIn := by
    rw [abstractConst_def, constantsVarsEquiv.apply_symm_apply, functionsIn_mapBound,
      TauCeti.BoundedFormulaInf.functionsIn_relabel]
  ext ⟨k, f | d⟩
  · have hmem {m : ℕ} (ψ : L[[γ]].BoundedFormulaInf ι α m) :
        (⟨k, Sum.inl f⟩ : Σ m, L[[γ]].Functions m) ∈ ψ.functionsIn ↔
          (⟨k, f⟩ : Σ m, L.Functions m) ∈ (constantsVarsEquiv ψ).functionsIn :=
      (Set.ext_iff.1 (functionsIn_constantsVarsEquiv ψ) ⟨k, f⟩).symm
    rw [Set.mem_sdiff, Set.mem_singleton_iff, hmem, heq, ← hmem]
    refine ⟨fun h => ⟨h, fun hc => ?_⟩, And.left⟩
    obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.1 hc
    exact Sum.inl_ne_inr (eq_of_heq hc)
  · cases k with
    | zero =>
      let d' : γ := d
      have hd : (⟨0, Sum.inr d⟩ : Σ m, L[[γ]].Functions m) = ⟨0, L.con d'⟩ := rfl
      rw [hd, ← mem_constantSupport, constantSupport_abstractConst, Set.mem_sdiff, Set.mem_sdiff,
        Set.mem_singleton_iff, Set.mem_singleton_iff, mem_constantSupport]
      exact and_congr_right fun _ => not_congr
        ⟨fun h => h ▸ rfl, fun h => Sum.inr_injective (eq_of_heq (Sigma.mk.inj h).2)⟩
    | succ _ => exact d.elim

/-- Abstracting a constant preserves the free-variable support. -/
@[simp]
theorem freeVarSupport_abstractConst [DecidableEq γ] (c : γ)
    (φ : L[[γ]].BoundedFormulaInf ι α n) :
    (abstractConst c φ).freeVarSupport = φ.freeVarSupport := by
  rw [abstractConst_def, freeVarSupport_constantsVarsEquiv_symm, freeVarSupport_mapBound,
    TauCeti.BoundedFormulaInf.freeVarSupport_relabel, freeVarSupport_constantsVarsEquiv]
  ext a
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_union]
  refine ⟨?_, fun ha => ⟨Sum.inr a, .inr ⟨a, ha, rfl⟩, rfl⟩⟩
  rintro ⟨_, (⟨d', _, rfl⟩ | ⟨a', ha', rfl⟩), hx⟩
  · by_cases hdc : d' = c <;> simp [hdc] at hx
  · simp_all

/-- **Realization of single-constant abstraction.** Evaluating the new outermost bound slot of
`abstractConst c φ` at `m` under the constant interpretation `e` is equivalent to realizing `φ`
under `Function.update e c m`. -/
@[simp]
theorem realize_abstractConst [DecidableEq γ] {M : Type w} [L.Structure M] (e : γ → M) (c : γ)
    (φ : L[[γ]].BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) (m : M) :
    @Realize _ ι α M (@withConstantsStructure L M _ γ (constantsOn.structure e)) (n + 1)
        (abstractConst c φ) v (Fin.snoc xs m) ↔
      @Realize _ ι α M (@withConstantsStructure L M _ γ
        (constantsOn.structure (Function.update e c m))) n φ v xs := by
  let f : Fin (1 + n) → Fin (n + 1) := Fin.addCases (fun _ : Fin 1 => Fin.last n) Fin.castSucc
  let g : γ ⊕ α → (γ ⊕ α) ⊕ Fin 1 :=
    Sum.elim (fun d => if d = c then Sum.inr 0 else Sum.inl (Sum.inl d)) (Sum.inl ∘ Sum.inr)
  have h₀ : @Realize _ ι α M (@withConstantsStructure L M _ γ (constantsOn.structure e)) (n + 1)
      (abstractConst c φ) v (Fin.snoc xs m) ↔
      (mapBound f (TauCeti.BoundedFormulaInf.relabel g (constantsVarsEquiv φ))).Realize
        (Sum.elim e v) (Fin.snoc xs m) :=
    let : (constantsOn γ).Structure M := constantsOn.structure e
    realize_constantsVarsEquiv_symm _ v (Fin.snoc xs m)
  have h₁ : (constantsVarsEquiv φ).Realize (Sum.elim (Function.update e c m) v) xs ↔
      @Realize _ ι α M (@withConstantsStructure L M _ γ
        (constantsOn.structure (Function.update e c m))) n φ v xs :=
    let : (constantsOn γ).Structure M := constantsOn.structure (Function.update e c m)
    realize_constantsVarsEquiv φ v xs
  have hcast : (Fin.snoc xs m ∘ f) ∘ Fin.castAdd n = fun _ : Fin 1 => m := funext fun _ => by
    simp [f]
  have hnat : (Fin.snoc xs m ∘ f) ∘ Fin.natAdd 1 = xs := funext fun _ => by simp [f]
  have hval : Sum.elim (Sum.elim e v) (fun _ : Fin 1 => m) ∘ g =
      Sum.elim (Function.update e c m) v := by
    funext x; rcases x with d | a
    · by_cases hdc : d = c
      · subst hdc; simp [g]
      · simp [g, hdc]
    · rfl
  rw [h₀, realize_mapBound, TauCeti.BoundedFormulaInf.realize_relabel, hcast, hnat, hval, h₁]

end FirstOrder.Language.BoundedFormulaInf
