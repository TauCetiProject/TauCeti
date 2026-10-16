/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Syntax

/-!
# Infinitary first-order formulas

This file defines the syntax of `L_{∞ω}`: first-order formulas with conjunctions and
disjunctions indexed by a *fixed branching carrier* `ι`, one per formula. `L_{ω₁ω}` is the
definitional specialization `ι := ℕ`.

## Design

The infinitary constructors `iSup`/`iInf` branch over the single type parameter `ι` rather than
quantifying over a fresh index type at every node. Consequently
`BoundedFormulaInf L ι α n : Type (max u v u' uι)` lives in the `max` of its parameters'
universes, with no `+ 1` bump; in particular `BoundedFormulaω L α n := BoundedFormulaInf L ℕ α n`
has exactly the universe `Type (max u v u')` of the finitary `BoundedFormula`.

Terms are Mathlib's `Term`, and bound variables are the slots `Fin n`, as for the finitary
`BoundedFormula`. A quantifier binds the last slot. The derived binary connectives follow
Mathlib's finitary conventions: `φ ⊓ ψ` is `(φ.imp ψ.not).not`, `φ ⊔ ψ` is `φ.not.imp ψ`, and
`φ.iff ψ` is `φ.imp ψ ⊓ ψ.imp φ`.

Infinitary formulas are not modelled by extending Mathlib's finitary `BoundedFormula`, whose
`iInf`/`iSup` range over finite index types. The two syntaxes are related only by the embedding
`BoundedFormula.toInf`. Structural recursion and induction use the recursor
`BoundedFormulaInf.rec`, with one case per constructor.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf`: infinitary formulas with carrier `ι`, free variables
  in `α`, and `n` bound-variable slots.
* `FirstOrder.Language.BoundedFormulaω`: the `ι := ℕ` specialization, an abbreviation, so all
  `BoundedFormulaInf` API applies definitionally; `FormulaInf`, `SentenceInf`, `Formulaω` and
  `Sentenceω`.
* The derived connectives `not`, `⊤`, `⊥`, `⊓`, `⊔`, `iff` and `ex`, and the quantifier closures
  `alls` and `exs`.
* `FirstOrder.Language.BoundedFormula.toInf`: the carrier-generic embedding of finitary formulas,
  with its `ι := ℕ` case `BoundedFormula.toOmega`.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, whose infinitary syntax is
  `Mathlib/ModelTheory/Infinitary/Syntax.lean` in `leanprover-community/mathlib4#42758`
  (Apache 2.0) at commit `2264c2c872bb642ab519aa2288d53110f07af37d`.
* Divergences from these sources: the binary connectives `⊓`, `⊔` and `iff` are added; the
  definition bodies are not exposed, except those of the match patterns `not` and `ex`, and are
  used through the defining equations `bot_def`, `top_def`, `inf_def`, `sup_def`, `iff_def`,
  `alls_zero`, `alls_succ`, `exs_zero`, `exs_succ` and the `toInf_*` equations.
-/

public section

universe u v u' uι

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

/-- An infinitary bounded formula of `L_{∞ω}`, with infinitary conjunctions and disjunctions
branching over the fixed carrier `ι`, free variables indexed by `α`, and `n` additional bound
variables available. -/
inductive BoundedFormulaInf (ι : Type uι) (α : Type u') : ℕ → Type (max u v u' uι) where
  /-- The false formula. -/
  | falsum {n} : BoundedFormulaInf ι α n
  /-- Equality of two terms. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaInf ι α n
  /-- A relation symbol applied to terms. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      BoundedFormulaInf ι α n
  /-- Implication. -/
  | imp {n} (φ ψ : BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n
  /-- Universal quantification over the last bound variable. -/
  | all {n} (φ : BoundedFormulaInf ι α (n + 1)) : BoundedFormulaInf ι α n
  /-- Infinitary disjunction over the carrier. -/
  | iSup {n} (φs : ι → BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n
  /-- Infinitary conjunction over the carrier. -/
  | iInf {n} (φs : ι → BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n

/-- A bounded formula of `L_{ω₁ω}`: the definitional `ι := ℕ` specialization of
`BoundedFormulaInf`. Its universe is exactly that of the finitary `BoundedFormula`. -/
abbrev BoundedFormulaω (α : Type u') (n : ℕ) := L.BoundedFormulaInf ℕ α n

/-- An `L_{∞ω}` formula: a bounded formula with no bound-variable slots. -/
abbrev FormulaInf (ι : Type uι) (α : Type u') := L.BoundedFormulaInf ι α 0

/-- An `L_{∞ω}` sentence: a formula with no free variables at all. -/
abbrev SentenceInf (ι : Type uι) := L.FormulaInf ι Empty

/-- An `L_{ω₁ω}` formula.

It is routed through `BoundedFormulaω` rather than stated as `FormulaInf ℕ α`, although the two
are the same type: dot-notation resolution unfolds an abbreviation chain one step at a time,
trying each head constant's namespace, so declarations in a `BoundedFormulaω` namespace stay
reachable as `φ.op` on an `L_{ω₁ω}` formula. -/
abbrev Formulaω (α : Type u') := L.BoundedFormulaω α 0

/-- An `L_{ω₁ω}` sentence, routed through `Formulaω` for the reason given there. -/
abbrev Sentenceω := L.Formulaω Empty

variable {L} {ι : Type uι} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- The negation of an infinitary formula. -/
@[expose, match_pattern]
protected def not (φ : L.BoundedFormulaInf ι α n) : L.BoundedFormulaInf ι α n :=
  φ.imp .falsum

/-- The true formula. -/
protected def verum : L.BoundedFormulaInf ι α n :=
  BoundedFormulaInf.not .falsum

instance : Bot (L.BoundedFormulaInf ι α n) :=
  ⟨.falsum⟩

instance : Top (L.BoundedFormulaInf ι α n) :=
  ⟨BoundedFormulaInf.verum⟩

instance : Inhabited (L.BoundedFormulaInf ι α n) :=
  ⟨⊥⟩

/-- The conjunction of two infinitary formulas, `(φ.imp ψ.not).not`, as for finitary formulas. -/
instance : Min (L.BoundedFormulaInf ι α n) :=
  ⟨fun φ ψ => (φ.imp ψ.not).not⟩

/-- The disjunction of two infinitary formulas, `φ.not.imp ψ`, as for finitary formulas. -/
instance : Max (L.BoundedFormulaInf ι α n) :=
  ⟨fun φ ψ => φ.not.imp ψ⟩

/-- The biconditional of two infinitary formulas. -/
protected def iff (φ ψ : L.BoundedFormulaInf ι α n) : L.BoundedFormulaInf ι α n :=
  φ.imp ψ ⊓ ψ.imp φ

/-- Existential quantification over the last bound variable. -/
@[expose, match_pattern]
protected def ex (φ : L.BoundedFormulaInf ι α (n + 1)) : L.BoundedFormulaInf ι α n :=
  φ.not.all.not

/-- Places universal quantifiers on all bound-variable slots of an infinitary bounded formula,
as `BoundedFormula.alls` does for finitary formulas. -/
def alls : ∀ {n}, L.BoundedFormulaInf ι α n → L.FormulaInf ι α
  | 0, φ => φ
  | _ + 1, φ => φ.all.alls

/-- Places existential quantifiers on all bound-variable slots of an infinitary bounded formula,
as `BoundedFormula.exs` does for finitary formulas. -/
def exs : ∀ {n}, L.BoundedFormulaInf ι α n → L.FormulaInf ι α
  | 0, φ => φ
  | _ + 1, φ => φ.ex.exs

/-! ### Defining equations -/

/-- `⊥` is the false formula. -/
theorem bot_def : (⊥ : L.BoundedFormulaInf ι α n) = falsum := (rfl)

/-- `⊤` is the negation of the false formula. -/
theorem top_def : (⊤ : L.BoundedFormulaInf ι α n) = BoundedFormulaInf.not falsum := (rfl)

/-- The conjunction `φ ⊓ ψ` is `(φ.imp ψ.not).not`. -/
theorem inf_def (φ ψ : L.BoundedFormulaInf ι α n) : φ ⊓ ψ = (φ.imp ψ.not).not := (rfl)

/-- The disjunction `φ ⊔ ψ` is `φ.not.imp ψ`. -/
theorem sup_def (φ ψ : L.BoundedFormulaInf ι α n) : φ ⊔ ψ = φ.not.imp ψ := (rfl)

/-- The biconditional `φ.iff ψ` is `φ.imp ψ ⊓ ψ.imp φ`. -/
theorem iff_def (φ ψ : L.BoundedFormulaInf ι α n) : φ.iff ψ = φ.imp ψ ⊓ ψ.imp φ := (rfl)

/-- With no bound-variable slots, `alls` leaves a formula unchanged. -/
@[simp]
theorem alls_zero (φ : L.BoundedFormulaInf ι α 0) : φ.alls = φ := (rfl)

/-- `alls` quantifies the last slot universally, then closes the remaining slots. -/
@[simp]
theorem alls_succ (φ : L.BoundedFormulaInf ι α (n + 1)) : φ.alls = φ.all.alls := (rfl)

/-- With no bound-variable slots, `exs` leaves a formula unchanged. -/
@[simp]
theorem exs_zero (φ : L.BoundedFormulaInf ι α 0) : φ.exs = φ := (rfl)

/-- `exs` quantifies the last slot existentially, then closes the remaining slots. -/
@[simp]
theorem exs_succ (φ : L.BoundedFormulaInf ι α (n + 1)) : φ.exs = φ.ex.exs := (rfl)

end BoundedFormulaInf

namespace BoundedFormula

/-- The embedding of finitary bounded formulas into the infinitary syntax. Finitary formulas have
no infinitary nodes, so the target carrier is arbitrary: one embedding serves every carrier and
universe. -/
def toInf : ∀ {n}, L.BoundedFormula α n → L.BoundedFormulaInf ι α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel R ts => .rel R ts
  | _, .imp φ ψ => (toInf φ).imp (toInf ψ)
  | _, .all φ => (toInf φ).all

/-- The embedding sends the finitary false formula to the false formula. -/
@[simp]
theorem toInf_falsum :
    (falsum : L.BoundedFormula α n).toInf = (.falsum : L.BoundedFormulaInf ι α n) :=
  (rfl)

/-- The embedding sends an equation to the same equation. -/
@[simp]
theorem toInf_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormula α n).toInf = (.equal t₁ t₂ : L.BoundedFormulaInf ι α n) :=
  (rfl)

/-- The embedding sends a relational atom to the same atom. -/
@[simp]
theorem toInf_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormula α n).toInf = (.rel R ts : L.BoundedFormulaInf ι α n) :=
  (rfl)

/-- The embedding commutes with implication. -/
@[simp]
theorem toInf_imp (φ ψ : L.BoundedFormula α n) :
    (φ.imp ψ).toInf = (φ.toInf.imp ψ.toInf : L.BoundedFormulaInf ι α n) :=
  (rfl)

/-- The embedding commutes with universal quantification. -/
@[simp]
theorem toInf_all (φ : L.BoundedFormula α (n + 1)) :
    φ.all.toInf = (φ.toInf.all : L.BoundedFormulaInf ι α n) :=
  (rfl)

/-- The embedding of finitary bounded formulas into `L_{ω₁ω}`. -/
abbrev toOmega (φ : L.BoundedFormula α n) : L.BoundedFormulaω α n :=
  toInf φ

end BoundedFormula

end Language

end FirstOrder
