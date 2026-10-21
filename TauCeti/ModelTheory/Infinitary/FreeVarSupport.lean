/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics

/-!
# The free-variable support of an infinitary formula

The free-variable support `φ.freeVarSupport` of an infinitary formula `φ` is the set of free
variables occurring in one of its atoms. It is a set rather than a `Finset`: an infinitary
conjunction or disjunction may mention infinitely many free variables, one in each branch.
For a finitary formula it is the coercion of Mathlib's `BoundedFormula.freeVarFinset`, and over a
countable carrier, in particular in `L_{ω₁ω}`, it is countable.

The main result `realize_congr_freeVarSupport` says that the realization of a formula depends
only on the values of the free-variable valuation on the support. This is the infinitary
analogue of the finitary fact that a formula only sees the variables it mentions.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.freeVarSupport`: the set of free variables of an
  infinitary formula.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.realize_congr_freeVarSupport`: valuations of the free
  variables that agree on the support give the same realization.
* `FirstOrder.Language.BoundedFormula.freeVarSupport_toInf`: on finitary formulas the support is
  `BoundedFormula.freeVarFinset`.
* `FirstOrder.Language.BoundedFormulaInf.countable_freeVarSupport`: over a countable carrier the
  support is countable.
* `FirstOrder.Language.Term.realize_congr_varFinsetLeft`: the term-level congruence the atomic
  cases use.

## References

* The definition and the congruence law follow Mathlib's finitary
  `FirstOrder.Language.BoundedFormula.freeVarFinset` and its realization lemma
  `BoundedFormula.realize_restrictFreeVar` in `Mathlib/ModelTheory/Syntax.lean` and
  `Mathlib/ModelTheory/Semantics.lean`.
-/

public section

universe u v u' uι uβ w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'}

namespace Term

/-- A term over `α ⊕ β` has the same realization under two valuations of `α` that agree on the
variables `Term.varFinsetLeft` of `α` it mentions. -/
theorem realize_congr_varFinsetLeft [DecidableEq α] {β : Type uβ} {M : Type w} [L.Structure M]
    {t : L.Term (α ⊕ β)} {v v' : α → M} (h : Set.EqOn v v' t.varFinsetLeft) (xs : β → M) :
    t.realize (Sum.elim v xs) = t.realize (Sum.elim v' xs) := by
  rw [← realize_restrictVarLeft' subset_rfl (v := v),
    ← realize_restrictVarLeft' subset_rfl (v := v'), ← Set.domRestrict_eq, ← Set.domRestrict_eq,
    Set.domRestrict_eq_domRestrict_iff.2 h]

end Term

namespace BoundedFormulaInf

variable {ι : Type uι} {n : ℕ}

open scoped Classical in
/-- The **free-variable support** of an infinitary formula: the set of free variables that occur
in one of its atoms. Infinitary connectives take the union over all their branches, so the support
may be infinite. -/
noncomputable def freeVarSupport : ∀ {n}, L.BoundedFormulaInf ι α n → Set α
  | _, .falsum => ∅
  | _, .equal t₁ t₂ => ↑t₁.varFinsetLeft ∪ ↑t₂.varFinsetLeft
  | _, .rel _ ts => ⋃ i, ↑(ts i).varFinsetLeft
  | _, .imp φ ψ => freeVarSupport φ ∪ freeVarSupport ψ
  | _, .all φ => freeVarSupport φ
  | _, .iSup φs => ⋃ i, freeVarSupport (φs i)
  | _, .iInf φs => ⋃ i, freeVarSupport (φs i)

/-! ### Defining equations -/

/-- The false formula has no free variables. -/
@[simp]
theorem freeVarSupport_falsum : (falsum : L.BoundedFormulaInf ι α n).freeVarSupport = ∅ := by
  rw [freeVarSupport]

/-- The free variables of an equation are those of its two terms. -/
@[simp]
theorem freeVarSupport_equal [DecidableEq α] (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).freeVarSupport =
      ↑t₁.varFinsetLeft ∪ ↑t₂.varFinsetLeft := by
  rw [freeVarSupport]
  congr!

/-- The free variables of a relational atom are those of its argument terms. -/
@[simp]
theorem freeVarSupport_rel [DecidableEq α] {l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaInf ι α n).freeVarSupport = ⋃ i, ↑(ts i).varFinsetLeft := by
  rw [freeVarSupport]
  congr!

/-- The free variables of an implication are those of either side. -/
@[simp]
theorem freeVarSupport_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.imp ψ).freeVarSupport = φ.freeVarSupport ∪ ψ.freeVarSupport := by
  rw [freeVarSupport]

/-- Universal quantification binds a slot, not a free variable, so it keeps the support. -/
@[simp]
theorem freeVarSupport_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.all.freeVarSupport = φ.freeVarSupport := by
  rw [freeVarSupport]

/-- The free variables of a disjunction over the carrier are those of its branches. -/
@[simp]
theorem freeVarSupport_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    (iSup φs).freeVarSupport = ⋃ i, (φs i).freeVarSupport := by
  rw [freeVarSupport]

/-- The free variables of a conjunction over the carrier are those of its branches. -/
@[simp]
theorem freeVarSupport_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    (iInf φs).freeVarSupport = ⋃ i, (φs i).freeVarSupport := by
  rw [freeVarSupport]

/-! ### Derived connectives -/

/-- Negation keeps the support. -/
@[simp]
theorem freeVarSupport_not (φ : L.BoundedFormulaInf ι α n) :
    φ.not.freeVarSupport = φ.freeVarSupport := by
  simp [BoundedFormulaInf.not]

/-- `⊥` has no free variables. -/
@[simp]
theorem freeVarSupport_bot : (⊥ : L.BoundedFormulaInf ι α n).freeVarSupport = ∅ := by
  rw [bot_def, freeVarSupport_falsum]

/-- `⊤` has no free variables. -/
@[simp]
theorem freeVarSupport_top : (⊤ : L.BoundedFormulaInf ι α n).freeVarSupport = ∅ := by
  rw [top_def, freeVarSupport_not, freeVarSupport_falsum]

/-- The free variables of `φ ⊓ ψ` are those of `φ` or `ψ`. -/
@[simp]
theorem freeVarSupport_inf (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊓ ψ).freeVarSupport = φ.freeVarSupport ∪ ψ.freeVarSupport := by
  rw [inf_def, freeVarSupport_not, freeVarSupport_imp, freeVarSupport_not]

/-- The free variables of `φ ⊔ ψ` are those of `φ` or `ψ`. -/
@[simp]
theorem freeVarSupport_sup (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ ⊔ ψ).freeVarSupport = φ.freeVarSupport ∪ ψ.freeVarSupport := by
  rw [sup_def, freeVarSupport_imp, freeVarSupport_not]

/-- The free variables of `φ.iff ψ` are those of `φ` or `ψ`. -/
@[simp]
theorem freeVarSupport_iff (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.iff ψ).freeVarSupport = φ.freeVarSupport ∪ ψ.freeVarSupport := by
  rw [iff_def, freeVarSupport_inf, freeVarSupport_imp, freeVarSupport_imp, Set.union_comm
    ψ.freeVarSupport, Set.union_self]

/-- Existential quantification keeps the support. -/
@[simp]
theorem freeVarSupport_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    φ.ex.freeVarSupport = φ.freeVarSupport := by
  simp [BoundedFormulaInf.ex]

/-- Universally closing the bound-variable slots keeps the support. -/
@[simp]
theorem freeVarSupport_alls (φ : L.BoundedFormulaInf ι α n) :
    φ.alls.freeVarSupport = φ.freeVarSupport := by
  induction n with
  | zero => rw [alls_zero]
  | succ n ih => rw [alls_succ, ih, freeVarSupport_all]

/-- Existentially closing the bound-variable slots keeps the support. -/
@[simp]
theorem freeVarSupport_exs (φ : L.BoundedFormulaInf ι α n) :
    φ.exs.freeVarSupport = φ.freeVarSupport := by
  induction n with
  | zero => rw [exs_zero]
  | succ n ih => rw [exs_succ, ih, freeVarSupport_ex]

/-! ### Countability -/

/-- Over a countable carrier, in particular in `L_{ω₁ω}`, an infinitary formula has countably many
free variables. -/
theorem countable_freeVarSupport [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    φ.freeVarSupport.Countable := by
  classical
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simpa using (t₁.varFinsetLeft ∪ t₂.varFinsetLeft).countable_toSet
  | rel R ts => simpa using Set.countable_iUnion fun i => (ts i).varFinsetLeft.countable_toSet
  | imp φ ψ ihφ ihψ => simpa using ihφ.union ihψ
  | all φ ih => simpa using ih
  | iSup φs ih => simpa using Set.countable_iUnion ih
  | iInf φs ih => simpa using Set.countable_iUnion ih

/-! ### Realization depends only on the support -/

/-- **Realization depends only on the free-variable support**: two valuations of the free
variables that agree on `φ.freeVarSupport` realize `φ` at the same bound-variable valuations. -/
theorem realize_congr_freeVarSupport {M : Type w} [L.Structure M]
    {φ : L.BoundedFormulaInf ι α n} {v v' : α → M} (h : Set.EqOn v v' φ.freeVarSupport)
    (xs : Fin n → M) : φ.Realize v xs ↔ φ.Realize v' xs := by
  classical
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    rw [freeVarSupport_equal] at h
    rw [realize_equal, realize_equal,
      Term.realize_congr_varFinsetLeft (h.mono Set.subset_union_left),
      Term.realize_congr_varFinsetLeft (h.mono Set.subset_union_right)]
  | rel R ts =>
    rw [freeVarSupport_rel] at h
    simp only [realize_rel]
    congr! 2 with i
    exact Term.realize_congr_varFinsetLeft (h.mono (Set.subset_iUnion_of_subset i subset_rfl)) xs
  | imp φ ψ ihφ ihψ =>
    rw [freeVarSupport_imp] at h
    simp only [realize_imp, ihφ (h.mono Set.subset_union_left),
      ihψ (h.mono Set.subset_union_right)]
  | all φ ih =>
    rw [freeVarSupport_all] at h
    simp only [realize_all, ih h]
  | iSup φs ih =>
    rw [freeVarSupport_iSup] at h
    simp only [realize_iSup]
    exact exists_congr fun i => ih i (h.mono (Set.subset_iUnion_of_subset i subset_rfl)) xs
  | iInf φs ih =>
    rw [freeVarSupport_iInf] at h
    simp only [realize_iInf]
    exact forall_congr' fun i => ih i (h.mono (Set.subset_iUnion_of_subset i subset_rfl)) xs

end BoundedFormulaInf

namespace BoundedFormula

/-- On a finitary formula, embedded at any carrier, the free-variable support is the coercion of
Mathlib's `BoundedFormula.freeVarFinset`. In particular it is finite. -/
@[simp]
theorem freeVarSupport_toInf [DecidableEq α] {ι : Type uι} {n : ℕ} (φ : L.BoundedFormula α n) :
    (φ.toInf : L.BoundedFormulaInf ι α n).freeVarSupport = ↑φ.freeVarFinset := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp [freeVarFinset]
  | rel R ts => simp [freeVarFinset]
  | imp φ ψ ihφ ihψ => simp [freeVarFinset, ihφ, ihψ]
  | all φ ih => simp [freeVarFinset, ih]

end BoundedFormula

end Language

end FirstOrder
