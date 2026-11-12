/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics

/-!
# Substitution and free-variable relabelling of infinitary formulas

`BoundedFormulaInf.subst` substitutes terms for free variables, leaving bound slots unchanged.
`BoundedFormulaInf.relabel` can instead send free variables to free variables or to newly
introduced bound slots. These operations preserve the branching carrier and work without
countability assumptions. Their realization laws describe the resulting valuations, including
under quantifiers and infinitary connectives.

Relabelling follows Mathlib's `FirstOrder.Language.BoundedFormula.relabel`: the new slots come
before the old slots. In particular, a map `α → β ⊕ Fin m` sends a formula with `n` slots to one
with `m + n` slots. We reuse Mathlib's `BoundedFormula.relabelAux` and its valuation law rather
than implementing the finite-index arithmetic again. Substitution similarly follows
`BoundedFormula.subst` and reuses `Term.subst`.

The corresponding operations in Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/Lomega1omega/Operations.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, are specialized to the carrier `ℕ`. Here both
operations and their realization laws are carrier-generic, and relabelling allows an arbitrary
map into free variables and bound slots, not just a free-variable map.
-/

public section

universe u v uι uα uβ w

namespace TauCeti

open FirstOrder Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {β : Type uβ}
variable {m n : ℕ}

/-- Substitute terms for the free variables of an infinitary formula. The substituted terms
have only free variables, so no bound variable can capture one of their variables. -/
def subst : ∀ {n}, L.BoundedFormulaInf ι α n → (α → L.Term β) → L.BoundedFormulaInf ι β n
  | _, .falsum, _ => .falsum
  | _, .equal t₁ t₂, f =>
    .equal (t₁.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)))
      (t₂.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)))
  | _, .rel R ts, f =>
    .rel R fun i => (ts i).subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))
  | _, .imp φ ψ, f => (subst φ f).imp (subst ψ f)
  | _, .all φ, f => (subst φ f).all
  | _, .iSup φs, f => .iSup fun i => subst (φs i) f
  | _, .iInf φs, f => .iInf fun i => subst (φs i) f

@[simp]
theorem subst_falsum (f : α → L.Term β) :
    subst (.falsum : L.BoundedFormulaInf ι α n) f = .falsum := (rfl)

@[simp]
theorem subst_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) (f : α → L.Term β) :
    subst (.equal t₁ t₂ : L.BoundedFormulaInf ι α n) f =
      .equal (t₁.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)))
        (t₂.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))) := (rfl)

@[simp]
theorem subst_rel {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n))
    (f : α → L.Term β) :
    subst (.rel R ts : L.BoundedFormulaInf ι α n) f =
      .rel R fun i => (ts i).subst
        (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)) := (rfl)

@[simp]
theorem subst_imp (φ ψ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    subst (φ.imp ψ) f = (subst φ f).imp (subst ψ f) := (rfl)

@[simp]
theorem subst_all (φ : L.BoundedFormulaInf ι α (n + 1)) (f : α → L.Term β) :
    subst φ.all f = (subst φ f).all := (rfl)

@[simp]
theorem subst_iSup (φs : ι → L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    subst (.iSup φs) f = .iSup fun i => subst (φs i) f := (rfl)

@[simp]
theorem subst_iInf (φs : ι → L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    subst (.iInf φs) f = .iInf fun i => subst (φs i) f := (rfl)

@[simp]
theorem subst_not (φ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    subst φ.not f = (subst φ f).not := by
  simp [Language.BoundedFormulaInf.not]

@[simp]
theorem subst_ex (φ : L.BoundedFormulaInf ι α (n + 1)) (f : α → L.Term β) :
    subst φ.ex f = (subst φ f).ex := by
  simp [Language.BoundedFormulaInf.ex]

@[simp]
theorem subst_bot (f : α → L.Term β) :
    subst (⊥ : L.BoundedFormulaInf ι α n) f = ⊥ := by
  simp [Language.BoundedFormulaInf.bot_def]

@[simp]
theorem subst_top (f : α → L.Term β) :
    subst (⊤ : L.BoundedFormulaInf ι α n) f = ⊤ := by
  simp [Language.BoundedFormulaInf.top_def]

@[simp]
theorem subst_inf (φ ψ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    subst (φ ⊓ ψ) f = subst φ f ⊓ subst ψ f := by
  simp [Language.BoundedFormulaInf.inf_def]

@[simp]
theorem subst_sup (φ ψ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    subst (φ ⊔ ψ) f = subst φ f ⊔ subst ψ f := by
  simp [Language.BoundedFormulaInf.sup_def]

@[simp]
theorem subst_iff (φ ψ : L.BoundedFormulaInf ι α n) (f : α → L.Term β) :
    subst (φ.iff ψ) f = (subst φ f).iff (subst ψ f) := by
  simp [Language.BoundedFormulaInf.iff_def]

/-- Substitution is realized by assigning to each original free variable the value of its
substituted term. The bound-variable valuation is unchanged. -/
@[simp]
theorem realize_subst {M : Type w} [L.Structure M] (φ : L.BoundedFormulaInf ι α n)
    (f : α → L.Term β) (v : β → M) (xs : Fin n → M) :
    (subst φ f).Realize v xs ↔ φ.Realize (fun a => (f a).realize v) xs := by
  have hterm {k : ℕ} (t : L.Term (α ⊕ Fin k)) (ys : Fin k → M) :
      (t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))).realize
        (Sum.elim v ys) = t.realize (Sum.elim (fun a => (f a).realize v) ys) := by
    rw [Term.realize_subst]
    congr 1
    funext a
    cases a <;> simp
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [hterm]
  | rel R ts => simp [hterm]
  | imp φ ψ ihφ ihψ => simp only [subst_imp, Language.BoundedFormulaInf.realize_imp, ihφ, ihψ]
  | all φ ih => simp only [subst_all, Language.BoundedFormulaInf.realize_all, ih]
  | iSup φs ih => simp only [subst_iSup, Language.BoundedFormulaInf.realize_iSup, ih]
  | iInf φs ih => simp only [subst_iInf, Language.BoundedFormulaInf.realize_iInf, ih]

/-- Relabel free variables by free variables or new bound slots. The `m` new slots are placed
before the original `n` slots, and quantifiers continue to bind the last slot. -/
def relabel (g : α → β ⊕ Fin m) :
    ∀ {n}, L.BoundedFormulaInf ι α n → L.BoundedFormulaInf ι β (m + n)
  | _, .falsum => .falsum
  | n, .equal t₁ t₂ => .equal (t₁.relabel (BoundedFormula.relabelAux g n))
      (t₂.relabel (BoundedFormula.relabelAux g n))
  | n, .rel R ts => .rel R fun i => (ts i).relabel (BoundedFormula.relabelAux g n)
  | _, .imp φ ψ => (relabel g φ).imp (relabel g ψ)
  | _, .all φ => (relabel g φ).all
  | _, .iSup φs => .iSup fun i => relabel g (φs i)
  | _, .iInf φs => .iInf fun i => relabel g (φs i)

@[simp]
theorem relabel_falsum (g : α → β ⊕ Fin m) :
    relabel g (.falsum : L.BoundedFormulaInf ι α n) = .falsum := (rfl)

@[simp]
theorem relabel_equal (g : α → β ⊕ Fin m) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    relabel g (.equal t₁ t₂ : L.BoundedFormulaInf ι α n) =
      .equal (t₁.relabel (BoundedFormula.relabelAux g n))
        (t₂.relabel (BoundedFormula.relabelAux g n)) := (rfl)

@[simp]
theorem relabel_rel (g : α → β ⊕ Fin m) {k : ℕ} (R : L.Relations k)
    (ts : Fin k → L.Term (α ⊕ Fin n)) :
    relabel g (.rel R ts : L.BoundedFormulaInf ι α n) =
      .rel R fun i => (ts i).relabel (BoundedFormula.relabelAux g n) := (rfl)

@[simp]
theorem relabel_imp (g : α → β ⊕ Fin m) (φ ψ : L.BoundedFormulaInf ι α n) :
    relabel g (φ.imp ψ) = (relabel g φ).imp (relabel g ψ) := (rfl)

@[simp]
theorem relabel_all (g : α → β ⊕ Fin m) (φ : L.BoundedFormulaInf ι α (n + 1)) :
    relabel g φ.all = (relabel g φ).all := (rfl)

@[simp]
theorem relabel_iSup (g : α → β ⊕ Fin m) (φs : ι → L.BoundedFormulaInf ι α n) :
    relabel g (.iSup φs) = .iSup fun i => relabel g (φs i) := (rfl)

@[simp]
theorem relabel_iInf (g : α → β ⊕ Fin m) (φs : ι → L.BoundedFormulaInf ι α n) :
    relabel g (.iInf φs) = .iInf fun i => relabel g (φs i) := (rfl)

@[simp]
theorem relabel_not (g : α → β ⊕ Fin m) (φ : L.BoundedFormulaInf ι α n) :
    relabel g φ.not = (relabel g φ).not := by
  simp [Language.BoundedFormulaInf.not]

@[simp]
theorem relabel_ex (g : α → β ⊕ Fin m) (φ : L.BoundedFormulaInf ι α (n + 1)) :
    relabel g φ.ex = (relabel g φ).ex := by
  simp [Language.BoundedFormulaInf.ex]

@[simp]
theorem relabel_bot (g : α → β ⊕ Fin m) :
    relabel g (⊥ : L.BoundedFormulaInf ι α n) = ⊥ := by
  simp [Language.BoundedFormulaInf.bot_def]

@[simp]
theorem relabel_top (g : α → β ⊕ Fin m) :
    relabel g (⊤ : L.BoundedFormulaInf ι α n) = ⊤ := by
  simp [Language.BoundedFormulaInf.top_def]

@[simp]
theorem relabel_inf (g : α → β ⊕ Fin m) (φ ψ : L.BoundedFormulaInf ι α n) :
    relabel g (φ ⊓ ψ) = relabel g φ ⊓ relabel g ψ := by
  simp [Language.BoundedFormulaInf.inf_def]

@[simp]
theorem relabel_sup (g : α → β ⊕ Fin m) (φ ψ : L.BoundedFormulaInf ι α n) :
    relabel g (φ ⊔ ψ) = relabel g φ ⊔ relabel g ψ := by
  simp [Language.BoundedFormulaInf.sup_def]

@[simp]
theorem relabel_iff (g : α → β ⊕ Fin m) (φ ψ : L.BoundedFormulaInf ι α n) :
    relabel g (φ.iff ψ) = (relabel g φ).iff (relabel g ψ) := by
  simp [Language.BoundedFormulaInf.iff_def]

/-- Relabelling evaluates each original free variable at its image under `g`. The first `m`
slots evaluate newly bound variables and the remaining `n` slots evaluate the original slots. -/
@[simp]
theorem realize_relabel {M : Type w} [L.Structure M] (g : α → β ⊕ Fin m)
    (φ : L.BoundedFormulaInf ι α n) (v : β → M) (xs : Fin (m + n) → M) :
    (relabel g φ).Realize v xs ↔
      φ.Realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ => simp only [relabel_imp, Language.BoundedFormulaInf.realize_imp, ihφ, ihψ]
  | all φ ih =>
    simp only [relabel_all, Language.BoundedFormulaInf.realize_all, ih,
      Fin.snoc_comp_castAdd, Fin.snoc_comp_natAdd]
  | iSup φs ih => simp only [relabel_iSup, Language.BoundedFormulaInf.realize_iSup, ih]
  | iInf φs ih => simp only [relabel_iInf, Language.BoundedFormulaInf.realize_iInf, ih]

/-- Embedding a substituted finitary formula is the same as substituting in its embedding. -/
@[simp]
theorem subst_toInf (φ : L.BoundedFormula α n) (f : α → L.Term β) :
    subst (φ.toInf : L.BoundedFormulaInf ι α n) f = (φ.subst f).toInf := by
  induction φ with
  | falsum => simp [BoundedFormula.subst, BoundedFormula.mapTermRel]
  | equal => simp [BoundedFormula.subst, BoundedFormula.mapTermRel]
  | rel => simp [BoundedFormula.subst, BoundedFormula.mapTermRel]
  | imp φ ψ ihφ ihψ => simp [BoundedFormula.subst, BoundedFormula.mapTermRel, ihφ, ihψ]
  | all φ ih => simp [BoundedFormula.subst, BoundedFormula.mapTermRel, ih]

/-- Embedding a relabelled finitary formula is the same as relabelling its embedding. -/
@[simp]
theorem relabel_toInf (g : α → β ⊕ Fin m) (φ : L.BoundedFormula α n) :
    relabel g (φ.toInf : L.BoundedFormulaInf ι α n) = (φ.relabel g).toInf := by
  induction φ with
  | falsum => simp
  | equal => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel]
  | rel => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

end BoundedFormulaInf

end TauCeti
