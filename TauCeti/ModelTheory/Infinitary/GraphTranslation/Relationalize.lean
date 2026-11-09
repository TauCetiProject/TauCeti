/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Language
public import TauCeti.ModelTheory.Infinitary.Symbols

/-!
# Translating infinitary formulas into the graph language

`BoundedFormulaInf.relationalize` translates an `L_{ω₁ω}` formula of `L` into a formula of the
relational graph language `L.graphLanguage`. Connectives and quantifiers are translated
structurally. An atom is flattened through its terms: an equation `t₁ = t₂` becomes
`∃ y, (t₁ = y) ∧ (t₂ = y)`, and a relational atom `R(t₀, …, t_{l-1})` becomes
`∃ y₀ … y_{l-1}, (⋀ᵢ tᵢ = yᵢ) ∧ R(y₀, …, y_{l-1})`, where each statement `t = y` about the value
of a term is its term graph `Term.graphFormula`. The term graph of a variable is an equation, and
the term graph of `f(s₀, …, s_{k-1})` existentially quantifies one witness for the value of each
argument, states the term graphs of the arguments at these witnesses, and applies the graph
relation of `f` to the witnesses and the value.

Over the graph expansion of an `L`-structure the translation is realized exactly when the
original formula is (`BoundedFormulaInf.realize_relationalize`). The translation mentions no
function symbol, and its relation symbols are exactly the graph-language symbols of the symbols of
the original formula (`BoundedFormulaInf.relationsIn_relationalize`). Combined with
`relSym_inter`, this bounds the shared vocabulary of two translated formulas by the translation of
their shared vocabulary.

## Main definitions

* `FirstOrder.Language.Term.graphFormula`: the term graph `t = y` of a term, with the variables
  of the term read through a map into the variables of the formula.
* `FirstOrder.Language.BoundedFormulaInf.relationalize`: the translation of formulas.

## Main results

* `FirstOrder.Language.Term.realize_graphFormula`,
  `FirstOrder.Language.BoundedFormulaInf.realize_relationalize`: over the graph expansion, the
  term graph states the value of the term, and the translation of a formula is realized exactly
  when the formula is.
* `FirstOrder.Language.BoundedFormulaInf.relationsIn_relationalize`: the exact occurrence identity
  `(relationalize φ).relationsIn = relSym φ.functionsIn φ.relationsIn`, with
  `FirstOrder.Language.BoundedFormulaInf.functionsIn_relationalize`.

## References

* The term graph and the translation follow `termGraphAux`, `equalGraph`, `relGraph` and
  `relationalizeFormula` of `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/Interpolation/TermGraph.lean` and `Relationalize.lean`.
  Divergences from that source: languages, variables and structures live in arbitrary universes;
  the term graph reads the variables of a term through a map into variables rather than into
  graph-language terms; finite conjunctions are coded conjunctions `iInfAlong`; and the atomic
  translations are not separate declarations.
-/

public section

universe u v u' uβ w

namespace FirstOrder

namespace Language

open TauCeti

variable {L : Language.{u, v}} {α : Type u'}

/-- Weakening of variables along the first `n` of `n + k` bound-variable slots. -/
private abbrev liftVar {n : ℕ} (k : ℕ) : α ⊕ Fin n → α ⊕ Fin (n + k) :=
  Sum.map id (Fin.castAdd k)

/-- The variable for the `i`-th of `k` new bound-variable slots after the first `n`. -/
private abbrev newVar (n : ℕ) {k : ℕ} (i : Fin k) : α ⊕ Fin (n + k) :=
  Sum.inr (Fin.natAdd n i)

section Realize

variable {M : Type w} {n k : ℕ} (v : α → M) (xs : Fin n → M) (ys : Fin k → M)

private theorem sumElim_append_liftVar (z : α ⊕ Fin n) :
    Sum.elim v (Fin.append xs ys) (liftVar k z) = Sum.elim v xs z := by
  rcases z with a | i <;> simp

private theorem sumElim_append_comp_liftVar :
    Sum.elim v (Fin.append xs ys) ∘ liftVar k = Sum.elim v xs :=
  funext (sumElim_append_liftVar v xs ys)

private theorem sumElim_append_newVar (i : Fin k) :
    Sum.elim v (Fin.append xs ys) (newVar n i) = ys i := by
  simp

end Realize

namespace Term

variable {β : Type uβ}

/-- The **term graph** of a term `t` of `L`: the formula of the graph language stating that the
value of `t`, whose variables are read through `ρ`, is the value of the variable `y`. A variable
gives an equation; an application `f(s₀, …, s_{k-1})` quantifies `k` new slots existentially,
states the term graph of each `sᵢ` at the `i`-th new slot, and applies the graph relation of `f`
to the new slots and `y`. -/
def graphFormula : ∀ {n : ℕ}, L.Term β → (β → α ⊕ Fin n) → α ⊕ Fin n →
    L.graphLanguage.BoundedFormulaω α n
  | _, var b, ρ, y => .equal (var (ρ b)) (var y)
  | n, func (l := k) f ts, ρ, y =>
      BoundedFormulaInf.exsLast
        (BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodable (Fin k))
            (fun i => graphFormula (ts i) (liftVar k ∘ ρ) (newVar n i)) ⊓
          .rel (GraphRelation.graph f) (Fin.snoc (fun i => var (newVar n i)) (var (liftVar k y))))

/-- The term graph of a variable is an equation. -/
@[simp]
theorem graphFormula_var {n : ℕ} (b : β) (ρ : β → α ⊕ Fin n) (y : α ⊕ Fin n) :
    (var b : L.Term β).graphFormula ρ y = .equal (var (ρ b)) (var y) := (rfl)

/-- The term graph of an application quantifies one new slot for the value of each argument. -/
theorem graphFormula_func {n k : ℕ} (f : L.Functions k) (ts : Fin k → L.Term β)
    (ρ : β → α ⊕ Fin n) (y : α ⊕ Fin n) :
    (func f ts).graphFormula ρ y =
      BoundedFormulaInf.exsLast
        (BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodable (Fin k))
            (fun i => (ts i).graphFormula (Sum.map id (Fin.castAdd k) ∘ ρ)
              (Sum.inr (Fin.natAdd n i))) ⊓
          .rel (GraphRelation.graph f)
            (Fin.snoc (fun i => var (Sum.inr (Fin.natAdd n i)))
              (var (Sum.map id (Fin.castAdd k) y)))) := (rfl)

variable {M : Type w} [L.Structure M]

/-- Over the graph expansion, the term graph of `t` holds exactly when the value of `t`, with its
variables read through `ρ`, is the value of `y`. -/
@[simp]
theorem realize_graphFormula {n : ℕ} (t : L.Term β) (ρ : β → α ⊕ Fin n) (y : α ⊕ Fin n)
    (v : α → M) (xs : Fin n → M) :
    letI := graphExpansion L M
    (t.graphFormula ρ y).Realize v xs ↔ t.realize (Sum.elim v xs ∘ ρ) = Sum.elim v xs y := by
  let := graphExpansion L M
  induction t generalizing n with
  | var b => simp
  | @func k f ts ih =>
    simp only [graphFormula_func, BoundedFormulaInf.realize_exsLast, BoundedFormulaInf.realize_inf,
      BoundedFormulaInf.realize_iInfAlong, ih, BoundedFormulaInf.realize_rel,
      graphExpansion_relMap_graph, ← Function.comp_assoc, sumElim_append_comp_liftVar,
      sumElim_append_newVar, Fin.init_def, Fin.snoc_castSucc, Fin.snoc_last, realize_var,
      sumElim_append_liftVar, ← funext_iff, exists_eq_left', realize_func]

/-- The relation symbols of a term graph are exactly the graph relations of the function symbols
of the term. -/
@[simp]
theorem relationsIn_graphFormula {n : ℕ} (t : L.Term β) (ρ : β → α ⊕ Fin n) (y : α ⊕ Fin n) :
    (t.graphFormula ρ y).relationsIn = graphRelSym '' t.functionsIn := by
  induction t generalizing n with
  | var b => simp
  | @func k f ts ih =>
    simp only [graphFormula_func, BoundedFormulaInf.relationsIn_exsLast,
      BoundedFormulaInf.relationsIn_inf, BoundedFormulaInf.relationsIn_iInfAlong, ih,
      BoundedFormulaInf.relationsIn_rel, functionsIn_func, Set.image_union, Set.image_iUnion,
      Set.image_singleton, graphRelSym_mk, Set.union_comm]

end Term

namespace BoundedFormulaInf

/-- The **translation into the graph language** of an `L_{ω₁ω}` formula of `L`. Connectives and
quantifiers are translated structurally. An equation `t₁ = t₂` becomes
`∃ y, (t₁ = y) ∧ (t₂ = y)`, and a relational atom `R(t₀, …, t_{l-1})` becomes
`∃ y₀ … y_{l-1}, (⋀ᵢ tᵢ = yᵢ) ∧ R(y₀, …, y_{l-1})`, where each `t = y` is a term graph. -/
def relationalize : ∀ {n : ℕ}, L.BoundedFormulaω α n → L.graphLanguage.BoundedFormulaω α n
  | _, falsum => falsum
  | n, equal t₁ t₂ =>
      exsLast (k := 1)
        (t₁.graphFormula (liftVar 1) (newVar n 0) ⊓ t₂.graphFormula (liftVar 1) (newVar n 0))
  | n, rel (l := l) R ts =>
      exsLast
        (iInfAlong (IndexCoding.ofEncodable (Fin l))
            (fun i => (ts i).graphFormula (liftVar l) (newVar n i)) ⊓
          rel (GraphRelation.base R) fun i => Term.var (newVar n i))
  | _, imp φ ψ => φ.relationalize.imp ψ.relationalize
  | _, all φ => φ.relationalize.all
  | _, iSup φs => iSup fun i => (φs i).relationalize
  | _, iInf φs => iInf fun i => (φs i).relationalize

variable {n : ℕ}

@[simp]
theorem relationalize_falsum : (falsum : L.BoundedFormulaω α n).relationalize = falsum := (rfl)

/-- The translation of an equation `t₁ = t₂` is `∃ y, (t₁ = y) ∧ (t₂ = y)`. -/
theorem relationalize_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaω α n).relationalize =
      exsLast (k := 1)
        (t₁.graphFormula (Sum.map id (Fin.castAdd 1)) (Sum.inr (Fin.natAdd n 0)) ⊓
          t₂.graphFormula (Sum.map id (Fin.castAdd 1)) (Sum.inr (Fin.natAdd n 0))) := (rfl)

/-- The translation of a relational atom `R(t₀, …, t_{l-1})` is
`∃ y₀ … y_{l-1}, (⋀ᵢ tᵢ = yᵢ) ∧ R(y₀, …, y_{l-1})`. -/
theorem relationalize_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaω α n).relationalize =
      exsLast
        (iInfAlong (IndexCoding.ofEncodable (Fin l))
            (fun i => (ts i).graphFormula (Sum.map id (Fin.castAdd l)) (Sum.inr (Fin.natAdd n i))) ⊓
          rel (GraphRelation.base R) fun i => Term.var (Sum.inr (Fin.natAdd n i))) := (rfl)

@[simp]
theorem relationalize_imp (φ ψ : L.BoundedFormulaω α n) :
    (φ.imp ψ).relationalize = φ.relationalize.imp ψ.relationalize := (rfl)

@[simp]
theorem relationalize_all (φ : L.BoundedFormulaω α (n + 1)) :
    φ.all.relationalize = φ.relationalize.all := (rfl)

@[simp]
theorem relationalize_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    (iSup φs).relationalize = iSup fun i => (φs i).relationalize := (rfl)

@[simp]
theorem relationalize_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    (iInf φs).relationalize = iInf fun i => (φs i).relationalize := (rfl)

@[simp]
theorem relationalize_not (φ : L.BoundedFormulaω α n) :
    φ.not.relationalize = φ.relationalize.not := (rfl)

@[simp]
theorem relationalize_bot : (⊥ : L.BoundedFormulaω α n).relationalize = ⊥ := (rfl)

@[simp]
theorem relationalize_top : (⊤ : L.BoundedFormulaω α n).relationalize = ⊤ := by
  simp only [top_def, relationalize_not, relationalize_falsum]

@[simp]
theorem relationalize_inf (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊓ ψ).relationalize = φ.relationalize ⊓ ψ.relationalize := (rfl)

@[simp]
theorem relationalize_sup (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊔ ψ).relationalize = φ.relationalize ⊔ ψ.relationalize := (rfl)

@[simp]
theorem relationalize_ex (φ : L.BoundedFormulaω α (n + 1)) :
    φ.ex.relationalize = φ.relationalize.ex := (rfl)

@[simp]
theorem relationalize_iff (φ ψ : L.BoundedFormulaω α n) :
    (φ.iff ψ).relationalize = φ.relationalize.iff ψ.relationalize := by
  simp only [iff_def, relationalize_inf, relationalize_imp]

section Realize

variable {M : Type w} [L.Structure M]

/-- Over the graph expansion of an `L`-structure, the translation of an equation is realized
exactly when the equation is. -/
private theorem realize_relationalize_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) (v : α → M)
    (xs : Fin n → M) :
    letI := graphExpansion L M
    (equal t₁ t₂ : L.BoundedFormulaω α n).relationalize.Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) := by
  let := graphExpansion L M
  simp only [relationalize_equal, realize_exsLast, realize_inf, Term.realize_graphFormula,
    sumElim_append_comp_liftVar, sumElim_append_newVar]
  exact ⟨fun ⟨_, h₁, h₂⟩ => h₁.trans h₂.symm,
    fun h => ⟨fun _ => t₂.realize (Sum.elim v xs), h, rfl⟩⟩

/-- Over the graph expansion of an `L`-structure, the translation of a relational atom is realized
exactly when the atom is. -/
private theorem realize_relationalize_rel {l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) :
    letI := graphExpansion L M
    (rel R ts : L.BoundedFormulaω α n).relationalize.Realize v xs ↔
      Structure.RelMap R fun i => (ts i).realize (Sum.elim v xs) := by
  let := graphExpansion L M
  simp only [relationalize_rel, realize_exsLast, realize_inf, realize_iInfAlong,
    Term.realize_graphFormula, realize_rel, graphExpansion_relMap_base, Term.realize_var,
    sumElim_append_comp_liftVar, sumElim_append_newVar, ← funext_iff, exists_eq_left']

/-- **The translation preserves truth**: over the graph expansion of an `L`-structure, the
translation of a formula is realized exactly when the formula is. -/
@[simp]
theorem realize_relationalize (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    letI := graphExpansion L M
    φ.relationalize.Realize v xs ↔ φ.Realize v xs := by
  let := graphExpansion L M
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => exact realize_relationalize_equal t₁ t₂ v xs
  | rel R ts => exact realize_relationalize_rel R ts v xs
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

end Realize

/-- **The exact occurrence identity**: the relation symbols of the translation of `φ` are exactly
the graph-language symbols of the function and relation symbols of `φ`. -/
@[simp]
theorem relationsIn_relationalize (φ : L.BoundedFormulaω α n) :
    φ.relationalize.relationsIn = relSym φ.functionsIn φ.relationsIn := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [relationalize_equal, relSym_def, Set.image_union]
  | rel R ts => simp [relationalize_rel, relSym_def, Set.union_comm, Set.image_iUnion]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ, relSym_union]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih, relSym_iUnion]
  | iInf φs ih => simp [ih, relSym_iUnion]

/-- No function symbol occurs in the translation of a formula: the graph language has none. -/
@[simp]
theorem functionsIn_relationalize (φ : L.BoundedFormulaω α n) :
    φ.relationalize.functionsIn = ∅ :=
  Set.eq_empty_of_isEmpty _

end BoundedFormulaInf

end Language

end FirstOrder
