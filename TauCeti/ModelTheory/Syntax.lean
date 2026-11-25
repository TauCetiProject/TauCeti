/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Syntax

/-!
# First-order terms under relabelling, substitution and language maps

Mathlib's `FirstOrder.Language.Term.varFinsetLeft` collects the variables of a term over `α ⊕ β`
that come from the left summand `α`. This file characterizes it through the full variable set
`Term.varFinset`, and computes it after `Term.relabel` and `Term.subst`. It also records that a
language map commutes with relabelling the variables of a term, and a language map that is
injective on function symbols acts injectively on terms. Constructor equations for
`BoundedFormula.constantsVarsEquiv`, `Formula.relabel`, and `Formula.equivSentence` describe
variable relabelling and abstraction of constants in finitary formulas.

## Main results

* `FirstOrder.Language.Term.mem_varFinsetLeft_iff`: `a` is a left variable of `t` exactly when
  `Sum.inl a` is a variable of `t`.
* `FirstOrder.Language.Term.mem_varFinsetLeft_relabel`: the left variables of a relabelled term.
* `FirstOrder.Language.Term.mem_varFinsetLeft_subst`: the left variables of a substituted term.
* `FirstOrder.Language.Term.exists_eq_var_of_isRelational`: in a relational language, every term
  is a variable.
* `FirstOrder.Language.Term.exists_eq_var_inr_of_isRelational`: in a relational language, a term
  over `α ⊕ β` with `α` empty is a variable `Sum.inr b`.
* `FirstOrder.Language.LHom.onTerm_relabel`, `FirstOrder.Language.LHom.varFinset_onTerm` and
  `FirstOrder.Language.LHom.varFinsetLeft_onTerm`: a language map commutes with relabelling the
  variables of a term and preserves its occurring variables and left variables.
* `FirstOrder.Language.LHom.onTerm_injective`: a language map that is injective on function
  symbols acts injectively on terms; `FirstOrder.Language.LHom.Injective.onTerm_injective`
  specializes it to injective language maps.
* `FirstOrder.Language.LHom.constantsToVars_addConstants_onTerm`,
  `FirstOrder.Language.LHom.addConstants_onTerm_varsToConstants`,
  `FirstOrder.Language.Term.constantsToVars_lhomWithConstants_onTerm` and
  `FirstOrder.Language.Term.constantsToVars_lhomWithConstantsMap_onTerm` (with matching forms for
  `Term.constantsVarsEquivLeft`): constant abstraction on terms commutes with `LHom.addConstants`
  and translates `lhomWithConstants` and `lhomWithConstantsMap` into variable relabellings.
* `FirstOrder.Language.LHom.onBoundedFormula_not`, `FirstOrder.Language.LHom.onFormula_not`,
  `FirstOrder.Language.LHom.onSentence_not`, `FirstOrder.Language.LHom.id_onSentence`,
  `FirstOrder.Language.LHom.comp_onSentence`: language maps commute with negation and act
  functorially on sentences.
* `FirstOrder.Language.LHom.onTheory_empty`, `FirstOrder.Language.LHom.onTheory_singleton`,
  `FirstOrder.Language.LHom.onTheory_insert`, `FirstOrder.Language.LHom.onTheory_union`,
  `FirstOrder.Language.LHom.onTheory_mono`, `FirstOrder.Language.LHom.id_onTheory`,
  `FirstOrder.Language.LHom.comp_onTheory`: set-operation and functoriality laws for
  `LHom.onTheory`.
-/

public section

namespace FirstOrder

namespace Language

namespace Term

variable {L : Language} {α β γ δ : Type*}

/-- A left variable of a term over `α ⊕ β` is a variable `Sum.inl a` of the term. -/
theorem mem_varFinsetLeft_iff [DecidableEq α] [DecidableEq β] {t : L.Term (α ⊕ β)} {a : α} :
    a ∈ t.varFinsetLeft ↔ Sum.inl a ∈ t.varFinset := by
  induction t with
  | var x => cases x <;> simp
  | func f ts ih => simp [ih]

/-- The left variables of `t.relabel f` are the left values of `f` on the variables of `t`. -/
theorem mem_varFinsetLeft_relabel [DecidableEq α] [DecidableEq β] (f : α → β ⊕ γ)
    {t : L.Term α} {b : β} :
    b ∈ (t.relabel f).varFinsetLeft ↔ ∃ x ∈ t.varFinset, f x = Sum.inl b := by
  induction t with
  | var x =>
    rcases hx : f x with c | c <;> simp [hx, eq_comm]
  | func g ts ih =>
    simp only [relabel, varFinsetLeft, varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      ih]
    exact ⟨fun ⟨i, x, hx, h⟩ => ⟨x, ⟨i, hx⟩, h⟩, fun ⟨x, ⟨i, hx⟩, h⟩ => ⟨i, x, hx, h⟩⟩

/-- The left variables of `t.subst σ` are the left variables of `σ x` for the variables `x`
of `t`. -/
theorem mem_varFinsetLeft_subst [DecidableEq α] [DecidableEq β] (σ : α → L.Term (β ⊕ γ))
    {t : L.Term α} {b : β} :
    b ∈ (t.subst σ).varFinsetLeft ↔ ∃ x ∈ t.varFinset, b ∈ (σ x).varFinsetLeft := by
  induction t with
  | var x => simp
  | func g ts ih =>
    simp only [subst, varFinsetLeft, varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      ih]
    exact ⟨fun ⟨i, x, hx, h⟩ => ⟨x, ⟨i, hx⟩, h⟩, fun ⟨x, ⟨i, hx⟩, h⟩ => ⟨i, x, hx, h⟩⟩

/-- In a relational language, every term is a variable. -/
theorem exists_eq_var_of_isRelational [L.IsRelational] (t : L.Term α) : ∃ a, t = var a := by
  cases t with
  | var a => exact ⟨a, rfl⟩
  | func f _ => exact isEmptyElim f

/-- In a relational language, a term whose left variables range over an empty type is a right
variable. -/
theorem exists_eq_var_inr_of_isRelational [L.IsRelational] [IsEmpty α] (t : L.Term (α ⊕ β)) :
    ∃ b, t = var (Sum.inr b) := by
  cases t with
  | var x => rcases x with a | b
             · exact isEmptyElim a
             · exact ⟨b, rfl⟩
  | func f _ => exact isEmptyElim f

end Term

namespace LHom

variable {L : Language} {L' : Language}

/-- A language map commutes with relabelling the variables of a term. -/
@[simp]
theorem onTerm_relabel {β γ : Type*} (g : L →ᴸ L') (h : β → γ) (t : L.Term β) :
    g.onTerm (t.relabel h) = (g.onTerm t).relabel h := by
  induction t with
  | var => rfl
  | func f ts ih => simp [Term.relabel, ih]

/-- A language map preserves the variables occurring in a term; no injectivity on function
symbols is required. -/
@[simp]
theorem varFinset_onTerm {β : Type*} [DecidableEq β] (g : L →ᴸ L') (t : L.Term β) :
    (g.onTerm t).varFinset = t.varFinset := by
  induction t with
  | var => rfl
  | func f ts ih => simp [Term.varFinset, ih]

/-- A language map preserves the left variables occurring in a term over a sum type; no
injectivity on function symbols is required. -/
@[simp]
theorem varFinsetLeft_onTerm {β γ : Type*} [DecidableEq β] (g : L →ᴸ L') (t : L.Term (β ⊕ γ)) :
    (g.onTerm t).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var x => cases x <;> rfl
  | func f ts ih => simp [Term.varFinsetLeft, ih]

/-- A language map that is injective on function symbols acts injectively on terms; terms
mention no relation symbols, so nothing is assumed about those. -/
theorem onTerm_injective {g : L →ᴸ L'}
    (hg : ∀ {n}, Function.Injective fun f : L.Functions n => g.onFunction f) {β : Type*} :
    Function.Injective (g.onTerm : L.Term β → L'.Term β) := by
  intro t₁ t₂ h
  induction t₁ generalizing t₂ with
  | var a =>
    cases t₂ with
    | var b => simpa [onTerm] using h
    | func f ts => simp [onTerm] at h
  | func f ts ih =>
    cases t₂ with
    | var b => simp [onTerm] at h
    | func f' ts' =>
      simp only [onTerm, Term.func.injEq] at h
      obtain ⟨rfl, hf, hts⟩ := h
      rw [hg (eq_of_heq hf)]
      exact congrArg _ (funext fun i => ih i (congrFun (eq_of_heq hts) i))

/-- An injective language map acts injectively on terms. -/
theorem Injective.onTerm_injective {g : L →ᴸ L'} (hg : g.Injective) {β : Type*} :
    Function.Injective (g.onTerm : L.Term β → L'.Term β) :=
  LHom.onTerm_injective fun {_} => hg.onFunction

/-- Turning constants into variables commutes with extending a language map by `addConstants`. -/
@[simp]
theorem constantsToVars_addConstants_onTerm (g : L →ᴸ L') {γ α : Type*} (t : L[[γ]].Term α) :
    ((g.addConstants γ).onTerm t).constantsToVars = g.onTerm t.constantsToVars := by
  induction t with
  | var => rfl
  | @func n F ts ih =>
    cases n <;> rcases F with F | c
    · simp only [LHom.onTerm, Term.constantsToVars, ih]; simp [LHom.addConstants]
    · rfl
    · simp only [LHom.onTerm, Term.constantsToVars, ih]; simp [LHom.addConstants]
    · exact isEmptyElim c

/-- Restoring constants from variables commutes with extending a language map by `addConstants`. -/
@[simp]
theorem addConstants_onTerm_varsToConstants (g : L →ᴸ L') {γ α : Type*}
    (t : L.Term (γ ⊕ α)) :
    (g.addConstants γ).onTerm t.varsToConstants = (g.onTerm t).varsToConstants := by
  induction t with
  | var x =>
    rcases x with c | a
    · simp only [Term.varsToConstants, Constants.term, LHom.onTerm]
      congr
      exact funext fun i => i.elim0
    · rfl
  | func F ts ih =>
    simp only [LHom.onTerm, Term.varsToConstants, ih]
    simp [LHom.addConstants]

/-- Left constant abstraction on terms commutes with `LHom.addConstants`. -/
theorem constantsVarsEquivLeft_addConstants_onTerm (g : L →ᴸ L') {γ α β : Type*}
    (t : L[[γ]].Term (α ⊕ β)) :
    Term.constantsVarsEquivLeft ((g.addConstants γ).onTerm t) =
      g.onTerm (Term.constantsVarsEquivLeft t) := by
  simp only [Term.constantsVarsEquivLeft_apply, constantsToVars_addConstants_onTerm, onTerm_relabel]

/-- Inverse left constant abstraction on terms commutes with `LHom.addConstants`. -/
theorem addConstants_onTerm_constantsVarsEquivLeft_symm (g : L →ᴸ L') {γ α β : Type*}
    (t : L.Term ((γ ⊕ α) ⊕ β)) :
    (g.addConstants γ).onTerm (Term.constantsVarsEquivLeft.symm t) =
      Term.constantsVarsEquivLeft.symm (g.onTerm t) := by
  simp only [Term.constantsVarsEquivLeft_symm_apply, addConstants_onTerm_varsToConstants,
    onTerm_relabel]

section FormulasAndTheories

variable {L'' : Language} {α : Type*} {n : ℕ}

/-- A language homomorphism commutes with negation on bounded formulas. -/
theorem onBoundedFormula_not (g : L →ᴸ L') (φ : L.BoundedFormula α n) :
    g.onBoundedFormula φ.not = (g.onBoundedFormula φ).not :=
  (rfl)

/-- A language homomorphism commutes with negation on formulas. -/
@[simp]
theorem onFormula_not (g : L →ᴸ L') (φ : L.Formula α) :
    g.onFormula φ.not = (g.onFormula φ).not :=
  (rfl)

/-- A language homomorphism commutes with negation on sentences. -/
@[simp]
theorem onSentence_not (g : L →ᴸ L') (φ : L.Sentence) :
    g.onSentence φ.not = (g.onSentence φ).not :=
  (rfl)

/-- The identity language homomorphism fixes every sentence. -/
@[simp]
theorem id_onSentence (φ : L.Sentence) : (LHom.id L).onSentence φ = φ :=
  congrFun id_onBoundedFormula φ

/-- Composition of language homomorphisms acts by composition on sentences. -/
@[simp]
theorem comp_onSentence (h : L' →ᴸ L'') (g : L →ᴸ L') (φ : L.Sentence) :
    (h.comp g).onSentence φ = h.onSentence (g.onSentence φ) :=
  congrFun (comp_onBoundedFormula h g) φ

/-- Mapping the empty theory along a language homomorphism gives the empty theory. -/
@[simp]
theorem onTheory_empty (g : L →ᴸ L') : g.onTheory ∅ = ∅ :=
  Set.image_empty _

/-- Mapping a singleton theory along a language homomorphism maps its single sentence. -/
@[simp]
theorem onTheory_singleton (g : L →ᴸ L') (φ : L.Sentence) :
    g.onTheory {φ} = {g.onSentence φ} :=
  Set.image_singleton

/-- Mapping `insert φ T` along a language homomorphism inserts `g.onSentence φ` into
`g.onTheory T`. -/
@[simp]
theorem onTheory_insert (g : L →ᴸ L') (φ : L.Sentence) (T : L.Theory) :
    g.onTheory (insert φ T) = insert (g.onSentence φ) (g.onTheory T) :=
  Set.image_insert_eq

/-- Mapping a union of theories along a language homomorphism distributes over the union. -/
@[simp]
theorem onTheory_union (g : L →ᴸ L') (T₁ T₂ : L.Theory) :
    g.onTheory (T₁ ∪ T₂) = g.onTheory T₁ ∪ g.onTheory T₂ :=
  Set.image_union _ _ _

/-- `LHom.onTheory` is monotone with respect to inclusion of theories. -/
theorem onTheory_mono (g : L →ᴸ L') {T₁ T₂ : L.Theory} (h : T₁ ⊆ T₂) :
    g.onTheory T₁ ⊆ g.onTheory T₂ :=
  Set.image_mono h

/-- The identity language homomorphism acts as the identity on theories. -/
@[simp]
theorem id_onTheory (T : L.Theory) : (LHom.id L).onTheory T = T := by
  ext φ
  simp

/-- Composition of language homomorphisms acts by composition on theories. -/
theorem comp_onTheory (h : L' →ᴸ L'') (g : L →ᴸ L') (T : L.Theory) :
    (h.comp g).onTheory T = h.onTheory (g.onTheory T) := by
  ext φ
  simp [onTheory, Set.mem_image]

end FormulasAndTheories

end LHom

namespace Term

/-- Turning constants into variables on a term coming from `L` relabels its variables into the
right summand. -/
@[simp]
theorem constantsToVars_lhomWithConstants_onTerm {L : Language} {γ α : Type*} (t : L.Term α) :
    ((L.lhomWithConstants γ).onTerm t).constantsToVars = t.relabel Sum.inr := by
  induction t with
  | var => rfl
  | @func n F ts ih =>
    cases n <;> simp [LHom.onTerm, Term.constantsToVars, Term.relabel, ih]

/-- Left constant abstraction on a term coming from `L` relabels its left variables into the right
part of the left summand. -/
theorem constantsVarsEquivLeft_lhomWithConstants_onTerm {L : Language} {γ α β : Type*}
    (t : L.Term (α ⊕ β)) :
    constantsVarsEquivLeft ((L.lhomWithConstants γ).onTerm t) =
      t.relabel (Sum.map Sum.inr id) := by
  rw [constantsVarsEquivLeft_apply, constantsToVars_lhomWithConstants_onTerm, relabel_relabel]
  refine congrArg (fun h => t.relabel h) (funext fun x => ?_)
  cases x <;> rfl

/-- Turning constants into variables after mapping constants along `f` relabels the constant
summand by `f`. -/
@[simp]
theorem constantsToVars_lhomWithConstantsMap_onTerm {L : Language} {γ δ α : Type*}
    (t : L[[γ]].Term α) (f : γ → δ) :
    ((L.lhomWithConstantsMap f).onTerm t).constantsToVars =
      t.constantsToVars.relabel (Sum.map f id) := by
  induction t with
  | var => rfl
  | @func n F ts ih =>
    cases n <;> rcases F with F | c
    · simp only [LHom.onTerm, Term.constantsToVars, Term.relabel, ih]; simp [lhomWithConstantsMap]
    · rfl
    · simp only [LHom.onTerm, Term.constantsToVars, Term.relabel, ih]; simp [lhomWithConstantsMap]
    · exact isEmptyElim c

/-- Left constant abstraction after mapping constants along `f` relabels the constant summand by
`f`. -/
theorem constantsVarsEquivLeft_lhomWithConstantsMap_onTerm {L : Language} {γ δ α β : Type*}
    (t : L[[γ]].Term (α ⊕ β)) (f : γ → δ) :
    constantsVarsEquivLeft ((L.lhomWithConstantsMap f).onTerm t) =
      (constantsVarsEquivLeft t).relabel (Sum.map (Sum.map f id) id) := by
  rw [constantsVarsEquivLeft_apply, constantsVarsEquivLeft_apply,
    constantsToVars_lhomWithConstantsMap_onTerm, relabel_relabel, relabel_relabel]
  refine congrArg (fun h => t.constantsToVars.relabel h) (funext fun x => ?_)
  rcases x with c | (a | b) <;> rfl

end Term

namespace BoundedFormula

variable {L : Language} {α γ : Type*} {n : ℕ}

@[simp]
theorem constantsVarsEquiv_falsum :
    constantsVarsEquiv (.falsum : L[[γ]].BoundedFormula α n) = .falsum := (rfl)

@[simp]
theorem constantsVarsEquiv_equal (t₁ t₂ : L[[γ]].Term (α ⊕ Fin n)) :
    constantsVarsEquiv (.equal t₁ t₂ : L[[γ]].BoundedFormula α n) =
      .equal (Term.constantsVarsEquivLeft t₁) (Term.constantsVarsEquivLeft t₂) := (rfl)

@[simp]
theorem constantsVarsEquiv_rel {l : ℕ} (R : L[[γ]].Relations l)
    (ts : Fin l → L[[γ]].Term (α ⊕ Fin n)) :
    constantsVarsEquiv (.rel R ts : L[[γ]].BoundedFormula α n) =
      .rel ((Equiv.sumEmpty _ _) R) (fun i => Term.constantsVarsEquivLeft (ts i)) := (rfl)

@[simp]
theorem constantsVarsEquiv_imp (φ ψ : L[[γ]].BoundedFormula α n) :
    constantsVarsEquiv (φ.imp ψ) =
      (constantsVarsEquiv φ).imp (constantsVarsEquiv ψ) := (rfl)

@[simp]
theorem constantsVarsEquiv_all (φ : L[[γ]].BoundedFormula α (n + 1)) :
    constantsVarsEquiv φ.all = (constantsVarsEquiv φ).all := (rfl)

end BoundedFormula

namespace Formula

variable {L : Language} {α β : Type*}

/-- Relabelling the free variables of `falsum` yields `falsum`. -/
@[simp]
theorem relabel_falsum (g : α → β) : Formula.relabel g (.falsum : L.Formula α) = .falsum :=
  BoundedFormula.relabel_falsum (Sum.inl ∘ g)

/-- Relabelling the free variables of a formula commutes with implication. -/
@[simp]
theorem relabel_imp (g : α → β) (φ ψ : L.Formula α) :
    Formula.relabel g (φ.imp ψ) = (Formula.relabel g φ).imp (Formula.relabel g ψ) :=
  BoundedFormula.relabel_imp (Sum.inl ∘ g) φ ψ

/-- `Formula.equivSentence` sends `falsum` to `falsum`. -/
@[simp]
theorem equivSentence_falsum :
    equivSentence (.falsum : L.Formula α) = .falsum := (rfl)

/-- `Formula.equivSentence` commutes with implication. -/
@[simp]
theorem equivSentence_imp (φ ψ : L.Formula α) :
    equivSentence (φ.imp ψ) = (equivSentence φ).imp (equivSentence ψ) := (rfl)

end Formula

end Language

end FirstOrder
