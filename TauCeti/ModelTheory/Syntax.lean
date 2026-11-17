/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Syntax
public import TauCeti.ModelTheory.LanguageMap

/-!
# First-order terms under relabelling, substitution and language maps

Mathlib's `FirstOrder.Language.Term.varFinsetLeft` collects the variables of a term over `α ⊕ β`
that come from the left summand `α`. This file characterizes it through the full variable set
`Term.varFinset`, and computes it after `Term.relabel` and `Term.subst`. It also records that a
language map commutes with relabelling the variables of a term, and a language map that is
injective on function symbols acts injectively on terms. Constructor equations for
`BoundedFormula.constantsVarsEquiv` describe abstraction of constants in finitary formulas, and
lifting a language map via `LHom.addConstants` commutes with exchanging constants and variables in
terms and finitary formulas.

## Main results

* `FirstOrder.Language.Term.mem_varFinsetLeft_iff`: `a` is a left variable of `t` exactly when
  `Sum.inl a` is a variable of `t`.
* `FirstOrder.Language.Term.mem_varFinsetLeft_relabel`: the left variables of a relabelled term.
* `FirstOrder.Language.Term.mem_varFinsetLeft_subst`: the left variables of a substituted term.
* `FirstOrder.Language.Term.exists_eq_var_of_isRelational`: in a relational language, every term
  is a variable.
* `FirstOrder.Language.Term.exists_eq_var_inr_of_isRelational`: in a relational language, a term
  over `α ⊕ β` with `α` empty is a variable `Sum.inr b`.
* `FirstOrder.Language.LHom.onTerm_relabel`, `FirstOrder.Language.LHom.onTerm_constantsTerm`,
  `FirstOrder.Language.LHom.varFinset_onTerm` and
  `FirstOrder.Language.LHom.varFinsetLeft_onTerm`: language maps commute with variable
  relabelling and constant terms and preserve variable sets of terms.
* `FirstOrder.Language.LHom.onBoundedFormula_relabel` and
  `FirstOrder.Language.LHom.onBoundedFormula_toFormula`: language maps commute with free-variable
  relabelling and opening bound positions of finitary formulas.
* `FirstOrder.Language.LHom.onTerm_injective`: a language map that is injective on function
  symbols acts injectively on terms; `FirstOrder.Language.LHom.Injective.onTerm_injective`
  specializes it to injective language maps.
* `FirstOrder.Language.LHom.onBoundedFormula_not`, `FirstOrder.Language.LHom.onFormula_not`,
  `FirstOrder.Language.LHom.onSentence_not`, `FirstOrder.Language.LHom.id_onSentence`,
  `FirstOrder.Language.LHom.comp_onSentence`: language maps commute with negation and act
  functorially on sentences.
* `FirstOrder.Language.LHom.onTheory_empty`, `FirstOrder.Language.LHom.onTheory_singleton`,
  `FirstOrder.Language.LHom.onTheory_insert`, `FirstOrder.Language.LHom.onTheory_union`,
  `FirstOrder.Language.LHom.onTheory_mono`, `FirstOrder.Language.LHom.id_onTheory`,
  `FirstOrder.Language.LHom.comp_onTheory`: set-operation and functoriality laws for
  `LHom.onTheory`.
* `FirstOrder.Language.Term.constantsToVars_addConstants_onTerm`,
  `FirstOrder.Language.LHom.addConstants_onTerm_varsToConstants` and
  `FirstOrder.Language.BoundedFormula.constantsVarsEquiv_addConstants_onBoundedFormula`:
  `LHom.addConstants` commutes with exchanging constants and variables in terms and finitary
  formulas.
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

/-- A language map sends the term of a constant symbol to the term of its image. -/
@[simp]
theorem onTerm_constantsTerm {β : Type*} (g : L →ᴸ L') (c : L.Constants) :
    g.onTerm (c.term : L.Term β) = Constants.term (g.onFunction c) := by
  simp [Constants.term, onTerm, Subsingleton.elim (fun _ : Fin 0 => _) default]

/-- Mapping a term along a language homomorphism preserves its finite set of variables. -/
@[simp]
theorem varFinset_onTerm {β : Type*} [DecidableEq β] (g : L →ᴸ L') (t : L.Term β) :
    (g.onTerm t).varFinset = t.varFinset := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [onTerm, Term.varFinset, ih]

/-- Mapping a term over `β ⊕ γ` along a language homomorphism preserves its left variables. -/
@[simp]
theorem varFinsetLeft_onTerm {β γ : Type*} [DecidableEq β] (g : L →ᴸ L')
    (t : L.Term (β ⊕ γ)) :
    (g.onTerm t).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var x => cases x <;> rfl
  | func _ _ ih => simp [onTerm, Term.varFinsetLeft, ih]

/-- A language map commutes with relabelling the free variables of a finitary bounded formula. -/
@[simp]
theorem onBoundedFormula_relabel {α β : Type*} {m n : ℕ} (g : L →ᴸ L') (f : α → β ⊕ Fin m)
    (φ : L.BoundedFormula α n) :
    g.onBoundedFormula (φ.relabel f) = (g.onBoundedFormula φ).relabel f := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel, Term.bdEqual]
  | rel R ts =>
    simp [BoundedFormula.relabel, BoundedFormula.mapTermRel, Relations.boundedFormula,
      Function.comp_def]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

/-- Opening the in-scope bound positions of a finitary formula commutes with a language map. -/
@[simp]
theorem onBoundedFormula_toFormula {α : Type*} {n : ℕ} (g : L →ᴸ L')
    (φ : L.BoundedFormula α n) :
    g.onBoundedFormula φ.toFormula = (g.onBoundedFormula φ).toFormula := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [Term.equal, Term.bdEqual]
  | rel R ts => simp [Relations.formula, Relations.boundedFormula, Function.comp_def]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [BoundedFormula.toFormula, ih]

/-- `LHom.onFormula` form of `FirstOrder.Language.LHom.onBoundedFormula_toFormula`. -/
@[simp]
theorem onFormula_toFormula {α : Type*} {n : ℕ} (g : L →ᴸ L') (φ : L.BoundedFormula α n) :
    g.onFormula φ.toFormula = (g.onBoundedFormula φ).toFormula :=
  g.onBoundedFormula_toFormula φ

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

namespace Term

variable {L : Language} {L' : Language} {α β γ : Type*}

/-- Abstracting constants out of a term commutes with lifting a language map by
`LHom.addConstants`. -/
@[simp]
theorem constantsToVars_addConstants_onTerm (g : L →ᴸ L') (t : L[[γ]].Term α) :
    ((g.addConstants γ).onTerm t).constantsToVars = g.onTerm t.constantsToVars := by
  induction t with
  | var _ => rfl
  | @func n f ts ih =>
    cases n with
    | zero =>
      rcases f with f | c
      · simp [constantsToVars, LHom.onTerm, ih]
      · rfl
    | succ n =>
      rcases f with f | c
      · simp [constantsToVars, LHom.onTerm, ih]
      · exact isEmptyElim c

/-- `Term.constantsVarsEquiv` form of `constantsToVars_addConstants_onTerm`. -/
theorem constantsVarsEquiv_addConstants_onTerm (g : L →ᴸ L') (t : L[[γ]].Term α) :
    constantsVarsEquiv ((g.addConstants γ).onTerm t) = g.onTerm (constantsVarsEquiv t) := by
  simp

/-- `Term.constantsVarsEquivLeft` commutes with lifting a language map by `LHom.addConstants`. -/
theorem constantsVarsEquivLeft_addConstants_onTerm (g : L →ᴸ L') (t : L[[γ]].Term (α ⊕ β)) :
    constantsVarsEquivLeft ((g.addConstants γ).onTerm t) =
      g.onTerm (constantsVarsEquivLeft t) := by
  simp

end Term

namespace BoundedFormula

variable {L : Language} {L' : Language} {α γ : Type*} {n : ℕ}

/-- Abstracting constants in a finitary formula commutes with lifting a language map by
`LHom.addConstants`. -/
@[simp]
theorem constantsVarsEquiv_addConstants_onBoundedFormula
    (g : L →ᴸ L') (φ : L[[γ]].BoundedFormula α n) :
    constantsVarsEquiv ((g.addConstants γ).onBoundedFormula φ) =
      g.onBoundedFormula (constantsVarsEquiv φ) := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [Term.bdEqual]
  | rel R ts => simp [LHom.onBoundedFormula, Relations.boundedFormula, Function.comp_def]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

end BoundedFormula

namespace LHom

variable {L : Language} {L' : Language} {α β γ : Type*}

/-- `LHom.addConstants` sends the constant term `(L.con c).term` to `(L'.con c).term`. -/
theorem addConstants_onTerm_con (g : L →ᴸ L') (c : γ) :
    (g.addConstants γ).onTerm ((L.con c).term : L[[γ]].Term α) = (L'.con c).term := by
  simp

/-- `Term.constantsVarsEquiv.symm` commutes with lifting a language map by `LHom.addConstants`. -/
theorem addConstants_onTerm_constantsVarsEquiv_symm (g : L →ᴸ L') (t : L.Term (γ ⊕ α)) :
    (g.addConstants γ).onTerm (Term.constantsVarsEquiv.symm t) =
      Term.constantsVarsEquiv.symm (g.onTerm t) := by
  apply Term.constantsVarsEquiv.injective
  rw [Term.constantsVarsEquiv_addConstants_onTerm, Term.constantsVarsEquiv.apply_symm_apply,
    Term.constantsVarsEquiv.apply_symm_apply]

/-- Restoring constants in a term commutes with lifting a language map by `LHom.addConstants`. -/
@[simp]
theorem addConstants_onTerm_varsToConstants (g : L →ᴸ L') (t : L.Term (γ ⊕ α)) :
    (g.addConstants γ).onTerm t.varsToConstants = (g.onTerm t).varsToConstants := by
  simpa only [Term.constantsVarsEquiv_symm_apply] using
    addConstants_onTerm_constantsVarsEquiv_symm g t

/-- `Term.constantsVarsEquivLeft.symm` commutes with lifting a language map by
`LHom.addConstants`. -/
theorem addConstants_onTerm_constantsVarsEquivLeft_symm (g : L →ᴸ L')
    (t : L.Term ((γ ⊕ α) ⊕ β)) :
    (g.addConstants γ).onTerm (Term.constantsVarsEquivLeft.symm t) =
      Term.constantsVarsEquivLeft.symm (g.onTerm t) := by
  simp

/-- Restoring constants in a finitary formula commutes with lifting a language map by
`LHom.addConstants`. -/
@[simp]
theorem addConstants_onBoundedFormula_constantsVarsEquiv_symm {n : ℕ} (g : L →ᴸ L')
    (φ : L.BoundedFormula (γ ⊕ α) n) :
    (g.addConstants γ).onBoundedFormula (BoundedFormula.constantsVarsEquiv.symm φ) =
      BoundedFormula.constantsVarsEquiv.symm (g.onBoundedFormula φ) := by
  apply BoundedFormula.constantsVarsEquiv.injective
  simp

end LHom

end Language

end FirstOrder
