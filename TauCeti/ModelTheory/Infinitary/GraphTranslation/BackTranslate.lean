/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Relationalize

/-!
# Translating formulas of the graph language back into the original language

`BoundedFormulaInf.backTranslate` sends an infinitary formula of the graph language
`L.graphLanguage` to a formula of `L`: an atom `G_f(x₀, …, x_{k-1}, y)` of the graph relation of
a function symbol `f` becomes the equation `f(x₀, …, x_{k-1}) = y`, a base atom `R(xs)` becomes
`R(xs)`, and connectives and quantifiers are translated structurally. The graph language has no
function symbols, so its terms are variables and are sent to the same variables
(`Term.backTranslate`). The translation works over any branching carrier.

Over the graph expansion of an `L`-structure, the back-translation of a formula is realized
exactly when the formula is (`BoundedFormulaInf.realize_backTranslate`). The function symbols of
the back-translation are the `f` whose graph relation occurs in the formula, and its relation
symbols are the base symbols occurring in it (`BoundedFormulaInf.functionsIn_backTranslate`,
`BoundedFormulaInf.relationsIn_backTranslate`). So a formula of the graph language all of whose
relation symbols lie in `relSym F R` back-translates to a formula of `L` whose function symbols
lie in `F` and whose relation symbols lie in `R`.

This is how a formula found in the graph language, for example an interpolant produced by a
theorem about relational languages, returns to `L` with control of its symbols. Composed with the
translation `BoundedFormulaInf.relationalize`, it gives back a formula with the same realization
as the original in every `L`-structure (`BoundedFormulaInf.realize_backTranslate_relationalize`)
and, by the occurrence calculus with `relationsIn_relationalize`, the same symbols; the two
formulas are not claimed to be syntactically equal.

## Main definitions

* `FirstOrder.Language.Term.backTranslate`: a term of the graph language as a term of `L`.
* `FirstOrder.Language.BoundedFormulaInf.backTranslate`: the back-translation of formulas.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.realize_backTranslate`: over the graph expansion, the
  back-translation of a formula is realized exactly when the formula is.
* `FirstOrder.Language.BoundedFormulaInf.functionsIn_backTranslate` and
  `FirstOrder.Language.BoundedFormulaInf.relationsIn_backTranslate`: the occurrence calculus of
  the back-translation.
* `FirstOrder.Language.BoundedFormulaInf.realize_backTranslate_relationalize`: translating into
  the graph language and back preserves realization in every `L`-structure.

## References

* The back-translation corresponds to `InfinitaryLogic/Methods/Interpolation/BackTranslate.lean`
  of `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, the
  companion of the graph language and translation ported in
  `TauCeti.ModelTheory.Infinitary.GraphTranslation.Language` and `Relationalize`.
  Divergences: the back-translation is defined over an arbitrary branching carrier, with
  languages, variables and structures in arbitrary universes.
-/

public section

universe u v u' uι uβ w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

namespace Term

variable {β : Type uβ}

/-- A term of the graph language as a term of `L`. The graph language has no function symbols, so
every one of its terms is a variable, and it is sent to the same variable. -/
def backTranslate : L.graphLanguage.Term β → L.Term β
  | var b => var b
  | func f _ => PEmpty.elim f

@[simp]
theorem backTranslate_var (b : β) : (var b : L.graphLanguage.Term β).backTranslate = var b :=
  (rfl)

variable {M : Type w} [L.Structure M]

/-- A term of the graph language takes the same value as its back-translation, over the graph
expansion. -/
@[simp]
theorem realize_backTranslate (t : L.graphLanguage.Term β) (v : β → M) :
    letI := graphExpansion L M
    t.backTranslate.realize v = t.realize v := by
  cases t with
  | var b => rfl
  | func f _ => exact PEmpty.elim f

/-- The back-translation of a term of the graph language mentions no function symbol. -/
@[simp]
theorem functionsIn_backTranslate (t : L.graphLanguage.Term β) :
    t.backTranslate.functionsIn = ∅ := by
  cases t with
  | var b => simp
  | func f _ => exact PEmpty.elim f

end Term

namespace BoundedFormulaInf

variable {ι : Type uι} {α : Type u'} {n : ℕ}

/-- The **back-translation** of an infinitary formula of the graph language of `L` into `L`. The
graph relation `G_f` of a `k`-ary function symbol `f`, applied to `x₀, …, x_{k-1}, y`, becomes the
equation `f(x₀, …, x_{k-1}) = y`; base atoms and equations keep their symbols, and connectives
and quantifiers are translated structurally. -/
def backTranslate : ∀ {n : ℕ}, L.graphLanguage.BoundedFormulaInf ι α n → L.BoundedFormulaInf ι α n
  | _, falsum => falsum
  | _, equal t₁ t₂ => equal t₁.backTranslate t₂.backTranslate
  | _, rel (.base R) ts => rel R fun i => (ts i).backTranslate
  | _, rel (.graph f) ts =>
      equal (Term.func f fun i => (ts (Fin.castSucc i)).backTranslate)
        (ts (Fin.last _)).backTranslate
  | _, imp φ ψ => φ.backTranslate.imp ψ.backTranslate
  | _, all φ => φ.backTranslate.all
  | _, iSup φs => iSup fun i => (φs i).backTranslate
  | _, iInf φs => iInf fun i => (φs i).backTranslate

@[simp]
theorem backTranslate_falsum :
    (falsum : L.graphLanguage.BoundedFormulaInf ι α n).backTranslate = falsum := (rfl)

@[simp]
theorem backTranslate_equal (t₁ t₂ : L.graphLanguage.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.graphLanguage.BoundedFormulaInf ι α n).backTranslate =
      equal t₁.backTranslate t₂.backTranslate := (rfl)

/-- A base atom `R(ts)` back-translates to the atom `R(ts)` of `L`. -/
@[simp]
theorem backTranslate_rel_base {l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.graphLanguage.Term (α ⊕ Fin n)) :
    (rel (GraphRelation.base R) ts : L.graphLanguage.BoundedFormulaInf ι α n).backTranslate =
      rel R fun i => (ts i).backTranslate := (rfl)

/-- A graph atom `G_f(t₀, …, t_{k-1}, t_k)` back-translates to the equation
`f(t₀, …, t_{k-1}) = t_k`. -/
@[simp]
theorem backTranslate_rel_graph {k : ℕ} (f : L.Functions k)
    (ts : Fin (k + 1) → L.graphLanguage.Term (α ⊕ Fin n)) :
    (rel (GraphRelation.graph f) ts : L.graphLanguage.BoundedFormulaInf ι α n).backTranslate =
      equal (Term.func f fun i => (ts (Fin.castSucc i)).backTranslate)
        (ts (Fin.last k)).backTranslate := (rfl)

@[simp]
theorem backTranslate_imp (φ ψ : L.graphLanguage.BoundedFormulaInf ι α n) :
    (φ.imp ψ).backTranslate = φ.backTranslate.imp ψ.backTranslate := (rfl)

@[simp]
theorem backTranslate_all (φ : L.graphLanguage.BoundedFormulaInf ι α (n + 1)) :
    φ.all.backTranslate = φ.backTranslate.all := (rfl)

@[simp]
theorem backTranslate_iSup (φs : ι → L.graphLanguage.BoundedFormulaInf ι α n) :
    (iSup φs).backTranslate = iSup fun i => (φs i).backTranslate := (rfl)

@[simp]
theorem backTranslate_iInf (φs : ι → L.graphLanguage.BoundedFormulaInf ι α n) :
    (iInf φs).backTranslate = iInf fun i => (φs i).backTranslate := (rfl)

@[simp]
theorem backTranslate_not (φ : L.graphLanguage.BoundedFormulaInf ι α n) :
    φ.not.backTranslate = φ.backTranslate.not := (rfl)

@[simp]
theorem backTranslate_bot : (⊥ : L.graphLanguage.BoundedFormulaInf ι α n).backTranslate = ⊥ :=
  (rfl)

@[simp]
theorem backTranslate_top : (⊤ : L.graphLanguage.BoundedFormulaInf ι α n).backTranslate = ⊤ := by
  simp only [top_def, backTranslate_not, backTranslate_falsum]

@[simp]
theorem backTranslate_inf (φ ψ : L.graphLanguage.BoundedFormulaInf ι α n) :
    (φ ⊓ ψ).backTranslate = φ.backTranslate ⊓ ψ.backTranslate := by
  simp only [inf_def, backTranslate_not, backTranslate_imp]

@[simp]
theorem backTranslate_sup (φ ψ : L.graphLanguage.BoundedFormulaInf ι α n) :
    (φ ⊔ ψ).backTranslate = φ.backTranslate ⊔ ψ.backTranslate := by
  simp only [sup_def, backTranslate_not, backTranslate_imp]

@[simp]
theorem backTranslate_ex (φ : L.graphLanguage.BoundedFormulaInf ι α (n + 1)) :
    φ.ex.backTranslate = φ.backTranslate.ex := (rfl)

@[simp]
theorem backTranslate_iff (φ ψ : L.graphLanguage.BoundedFormulaInf ι α n) :
    (φ.iff ψ).backTranslate = φ.backTranslate.iff ψ.backTranslate := by
  simp only [iff_def, backTranslate_inf, backTranslate_imp]

section Realize

variable {M : Type w} [L.Structure M]

/-- **The back-translation preserves truth**: over the graph expansion of an `L`-structure, the
back-translation of a formula of the graph language is realized exactly when the formula is. -/
@[simp]
theorem realize_backTranslate (φ : L.graphLanguage.BoundedFormulaInf ι α n) (v : α → M)
    (xs : Fin n → M) :
    letI := graphExpansion L M
    φ.backTranslate.Realize v xs ↔ φ.Realize v xs := by
  let := graphExpansion L M
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp
  | rel R ts =>
    cases R with
    | base R => simp
    | graph f => simp [Fin.init_def]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- Translating a formula of `L` into the graph language and back preserves its realization in
every `L`-structure. -/
theorem realize_backTranslate_relationalize (φ : L.BoundedFormulaω α n) (v : α → M)
    (xs : Fin n → M) : φ.relationalize.backTranslate.Realize v xs ↔ φ.Realize v xs := by
  rw [realize_backTranslate, realize_relationalize]

end Realize

/-- The function symbols of the back-translation of a formula are the function symbols whose
graph relation occurs in it. -/
@[simp]
theorem functionsIn_backTranslate (φ : L.graphLanguage.BoundedFormulaInf ι α n) :
    φ.backTranslate.functionsIn = graphRelSym ⁻¹' φ.relationsIn := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts =>
    ext g
    cases R with
    | base R => simpa using (baseRelSym_ne_graphRelSym ⟨_, R⟩ g).symm
    | graph f => simpa using (graphRelSym_injective.eq_iff (a := g) (b := ⟨_, f⟩)).symm
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

/-- The relation symbols of the back-translation of a formula are the relation symbols whose base
symbol occurs in it. Graph atoms become equations, which contribute no relation symbol. -/
@[simp]
theorem relationsIn_backTranslate (φ : L.graphLanguage.BoundedFormulaInf ι α n) :
    φ.backTranslate.relationsIn = baseRelSym ⁻¹' φ.relationsIn := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts =>
    ext r
    cases R with
    | base R => simpa using (baseRelSym_injective.eq_iff (a := r) (b := ⟨_, R⟩)).symm
    | graph f => simpa using baseRelSym_ne_graphRelSym r ⟨_, f⟩
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]
  | iSup φs ih => simp [ih]
  | iInf φs ih => simp [ih]

end BoundedFormulaInf

end Language

end FirstOrder
