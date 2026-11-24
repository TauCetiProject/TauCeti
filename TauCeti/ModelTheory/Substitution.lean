/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FreeVarSupport
public import TauCeti.ModelTheory.Term.Substitution

/-!
# Substitution in first-order formulas

Mathlib's `FirstOrder.Language.BoundedFormula.subst` replaces the free variables of a bounded
formula by terms and leaves its bound variables alone. This file records how it composes with
itself and with `FirstOrder.Language.BoundedFormula.toFormula`, which turns the bound positions in
scope into free variables, and computes the free variables of a substituted, relabelled or opened
formula.

The free-variable computations are transported from the infinitary free-variable support along
the embedding `FirstOrder.Language.BoundedFormula.toInf`, where substitution and relabelling are
already computed.

## Main results

* `FirstOrder.Language.BoundedFormula.subst_falsum`, `subst_equal`, `subst_rel`, `subst_imp` and
  `subst_all`: substitution on each constructor.
* `FirstOrder.Language.BoundedFormula.subst_subst`: two substitutions compose to one.
* `FirstOrder.Language.BoundedFormula.relabelAux_inl`: `relabelAux` on a free variable.
* `FirstOrder.Language.Term.relabel_subst_eq_subst_relabel`,
  `FirstOrder.Language.BoundedFormula.relabel_subst_eq_subst_relabel`: substitution commutes with
  relabelling when the two agree on each variable, for terms under bound positions and for
  formulas.
* `FirstOrder.Language.BoundedFormula.toFormula_subst`: opening the bound positions of a
  substituted formula is substituting in the opened formula.
* `FirstOrder.Language.BoundedFormula.freeVarFinset_subst`: the free variables after a
  substitution are the variables of the terms substituted for the free variables.
* `FirstOrder.Language.BoundedFormula.mem_freeVarFinset_relabel`: the free variables after a
  relabelling.
* `FirstOrder.Language.BoundedFormula.inl_mem_freeVarFinset_toFormula`: opening the bound
  positions keeps the free variables, as the left summand.
-/

public section

namespace FirstOrder.Language.BoundedFormula

variable {L : Language} {α β γ : Type*} {n : ℕ}

/-! ### Constructor equations -/

@[simp]
theorem subst_falsum (f : α → L.Term β) : (falsum : L.BoundedFormula α n).subst f = falsum :=
  (rfl)

@[simp]
theorem subst_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) (f : α → L.Term β) :
    (equal t₁ t₂).subst f =
      equal (t₁.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)))
        (t₂.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))) :=
  (rfl)

@[simp]
theorem subst_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n))
    (f : α → L.Term β) :
    (rel R ts).subst f =
      rel R fun i => (ts i).subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)) :=
  (rfl)

@[simp]
theorem subst_imp (φ ψ : L.BoundedFormula α n) (f : α → L.Term β) :
    (φ.imp ψ).subst f = (φ.subst f).imp (ψ.subst f) :=
  (rfl)

@[simp]
theorem subst_all (φ : L.BoundedFormula α (n + 1)) (f : α → L.Term β) :
    φ.all.subst f = (φ.subst f).all :=
  (rfl)

/-! ### Composition laws -/

/-- Two successive substitutions of terms for the free variables are one substitution, by the
substituted terms. -/
@[simp]
theorem subst_subst (φ : L.BoundedFormula α n) (f : α → L.Term β) (g : β → L.Term γ) :
    (φ.subst f).subst g = φ.subst fun a => (f a).subst g := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [subst_equal, Term.subst_subst]
    congr 2 <;> funext x <;> rcases x with a | i <;> simp [Function.comp_def]
  | rel R ts =>
    simp only [subst_rel, Term.subst_subst]
    congr 2
    funext j
    congr 1
    funext x
    rcases x with a | i <;> simp [Function.comp_def]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

/-- `BoundedFormula.relabelAux` sends a free variable `x` where `g` sends it, with the old bound
positions placed after the new ones. -/
@[simp]
theorem relabelAux_inl {δ ε : Type*} {m : ℕ} (g : δ → ε ⊕ Fin m) (k : ℕ) (x : δ) :
    relabelAux g k (Sum.inl x) = Sum.map id (Fin.castAdd k) (g x) := by
  rcases hx : g x with y | j <;> simp [relabelAux, hx]

end FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.Term

variable {L : Language} {γ : Type*}

/-- The term step of `BoundedFormula.relabel_subst_eq_subst_relabel`: in a term under `k` bound
positions, substituting `F` for the free variables and then relabelling along
`BoundedFormula.relabelAux g k` is relabelling along `BoundedFormula.relabelAux g' k` and then
substituting `F'`, provided the two agree on each variable. -/
theorem relabel_subst_eq_subst_relabel {δ ε γ' : Type*} {m : ℕ} (F : γ → L.Term δ)
    (g : δ → ε ⊕ Fin m) (g' : γ → γ' ⊕ Fin m) (F' : γ' → L.Term ε)
    (h : ∀ c, (F c).relabel g =
      Sum.elim (fun c' => (F' c').relabel Sum.inl) (fun j => var (Sum.inr j)) (g' c))
    {k : ℕ} (t : L.Term (γ ⊕ Fin k)) :
    (t.subst (Sum.elim (relabel Sum.inl ∘ F) (var ∘ Sum.inr))).relabel
        (BoundedFormula.relabelAux g k) =
      (t.relabel (BoundedFormula.relabelAux g' k)).subst
        (Sum.elim (relabel Sum.inl ∘ F') (var ∘ Sum.inr)) := by
  rw [relabel_subst, subst_relabel]
  congr 1
  funext x
  rcases x with c | i
  · have hg : BoundedFormula.relabelAux g k ∘ Sum.inl = Sum.map id (Fin.castAdd k) ∘ g :=
      funext (BoundedFormula.relabelAux_inl g k)
    rw [Function.comp_apply, Sum.elim_inl, Function.comp_apply, relabel_relabel, hg,
      ← relabel_relabel, h c, BoundedFormula.relabelAux_inl]
    rcases g' c with c' | j
    · rw [Sum.elim_inl, Sum.map_inl, Sum.elim_inl, Function.comp_apply, relabel_relabel]
      rfl
    · rfl
  · simp [BoundedFormula.relabelAux]

end FirstOrder.Language.Term

namespace FirstOrder.Language.BoundedFormula

variable {L : Language} {α β γ : Type*} {n : ℕ}

/-- Substitution commutes with relabelling: substituting `F` and then relabelling along `g` is
relabelling along `g'` and then substituting `F'`, provided the two agree on each variable. A
variable that `g'` sends to a new bound position `j` must be sent by `F` to a term that `g`
relabels to that bound position. -/
theorem relabel_subst_eq_subst_relabel {δ ε γ' : Type*} {m : ℕ} (F : γ → L.Term δ)
    (g : δ → ε ⊕ Fin m) (g' : γ → γ' ⊕ Fin m) (F' : γ' → L.Term ε)
    (h : ∀ c, (F c).relabel g =
      Sum.elim (fun c' => (F' c').relabel Sum.inl) (fun j => Term.var (Sum.inr j)) (g' c)) :
    ∀ {k} (χ : L.BoundedFormula γ k), (χ.subst F).relabel g = (χ.relabel g').subst F' := by
  intro k χ
  induction χ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [subst, relabel, mapTermRel, Term.relabel_subst_eq_subst_relabel F g g' F' h]
  | rel R ts =>
    simp only [subst, relabel, mapTermRel, Term.relabel_subst_eq_subst_relabel F g g' F' h]
  | imp φ ψ ihφ ihψ => rw [subst_imp, relabel_imp, relabel_imp, subst_imp, ihφ, ihψ]
  | all φ ih => rw [subst_all, relabel_all, relabel_all, subst_all, ih]

/-- Opening the bound positions of a substituted formula is substituting in the opened formula,
with the bound positions kept as variables. -/
@[simp]
theorem toFormula_subst (φ : L.BoundedFormula α n) (f : α → L.Term β) :
    (φ.subst f).toFormula =
      φ.toFormula.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)) := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [Term.equal, Term.bdEqual, Function.comp_def]
  | rel R ts => simp [Relations.formula, Relations.boundedFormula, Function.comp_def]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih =>
    rw [subst_all, toFormula, toFormula, ih, subst_all, relabel_subst_eq_subst_relabel _ _ _
      (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))]
    rintro (a | i)
    · simp [Function.comp_def, Term.relabel_relabel]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- The free variables of a substituted formula are the variables of the terms substituted for
its free variables. -/
theorem freeVarFinset_subst [DecidableEq α] [DecidableEq β] (φ : L.BoundedFormula α n)
    (f : α → L.Term β) :
    (φ.subst f).freeVarFinset = φ.freeVarFinset.biUnion fun a => (f a).varFinset := by
  apply Finset.coe_injective
  rw [← freeVarSupport_toInf (ι := Empty), ← TauCeti.BoundedFormulaInf.subst_toInf,
    TauCeti.BoundedFormulaInf.freeVarSupport_subst, freeVarSupport_toInf, Finset.coe_biUnion]

/-- A free variable of a relabelled formula is the left value of the relabelling at a free
variable of the formula. -/
theorem mem_freeVarFinset_relabel [DecidableEq α] [DecidableEq β] {m : ℕ} (g : α → β ⊕ Fin m)
    (φ : L.BoundedFormula α n) {b : β} :
    b ∈ (φ.relabel g).freeVarFinset ↔ ∃ a ∈ φ.freeVarFinset, g a = Sum.inl b := by
  rw [← Finset.mem_coe, ← freeVarSupport_toInf (ι := Empty),
    ← TauCeti.BoundedFormulaInf.relabel_toInf, TauCeti.BoundedFormulaInf.freeVarSupport_relabel,
    freeVarSupport_toInf]
  simp

/-- Opening the bound positions of a formula keeps its free variables, as the left summand. -/
@[simp]
theorem inl_mem_freeVarFinset_toFormula [DecidableEq α] (φ : L.BoundedFormula α n) {a : α} :
    Sum.inl a ∈ φ.toFormula.freeVarFinset ↔ a ∈ φ.freeVarFinset := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [toFormula, Term.equal, Term.bdEqual, freeVarFinset, Finset.mem_union,
      Term.mem_varFinsetLeft_relabel]
    simp [Term.mem_varFinsetLeft_iff]
  | rel R ts =>
    simp only [toFormula, Relations.formula, Relations.boundedFormula, freeVarFinset,
      Finset.mem_biUnion, Term.mem_varFinsetLeft_relabel]
    simp [Term.mem_varFinsetLeft_iff]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih =>
    simp only [toFormula, freeVarFinset, mem_freeVarFinset_relabel]
    constructor
    · rintro ⟨x | i, hx, h⟩
      · simp only [Sum.elim_inl, Function.comp_apply, Sum.inl.injEq] at h
        exact (ih.1 (h ▸ hx))
      · revert h
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    · intro ha
      exact ⟨Sum.inl a, ih.2 ha, rfl⟩

end FirstOrder.Language.BoundedFormula
