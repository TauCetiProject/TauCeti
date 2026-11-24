/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Complexity
public import TauCeti.ModelTheory.Substitution

/-!
# Instances and depth of first-order formulas

In Mathlib's first-order syntax, a formula `φ : L.BoundedFormula α k` has free variables in `α`
and `k` bound positions, the quantifier `∀'` binding the last one. The *instance* `φ.inst ts` of
`φ` at a tuple `ts : Fin k → L.Term α` replaces the bound positions by the terms and keeps the free
variables. Since bound variables are positions rather than names, no variable of the terms can be
captured, and no renaming is needed. Instances are the formulas that the quantifier rules of a
sequent calculus put into their premises: from `∀'φ` the left rule passes to `φ.inst ![t]`.

The *depth* of a formula counts nested implications and universal quantifiers, atomic formulas
and `⊥` having depth `0`. Since Mathlib defines negation, disjunction, conjunction and the
existential quantifier through implication, `⊥` and `∀'`, these connectives cost depth. Depth is
the measure on cut formulas that drives syntactic cut elimination; it is Gallier's degree of a
formula, adapted to these primitives.

This file computes the meaning, the free variables, the depth and the complexity class of an
instance, and shows that instances commute with substitution of terms for free variables.

## Main definitions

* `FirstOrder.Language.BoundedFormula.inst`: the instance of a formula at a tuple of terms.
* `FirstOrder.Language.BoundedFormula.depth`: the depth of a formula.

## Main results

* `FirstOrder.Language.BoundedFormula.realize_inst`: an instance holds under an assignment exactly
  when the formula holds with the values of the terms at the bound positions.
* `FirstOrder.Language.BoundedFormula.subst_inst`: substituting terms for the free variables of
  an instance gives the instance of the substituted formula at the substituted terms.
* `FirstOrder.Language.BoundedFormula.mem_freeVarFinset_inst`: the free variables of an instance
  are those of the formula together with those of the terms at the bound positions that occur in
  the formula.
* `FirstOrder.Language.BoundedFormula.depth_inst`: an instance has the depth of the formula.
* `FirstOrder.Language.BoundedFormula.IsAtomic.inst`,
  `FirstOrder.Language.BoundedFormula.IsQF.inst`: instances of atomic and quantifier-free formulas
  are atomic and quantifier-free.

## References

* Jean H. Gallier, *Logic for Computer Science: Foundations of Automatic Theorem Proving*, second
  edition, Dover, 2015, Definition 6.4.3 (the degree of a formula).
-/

public section

namespace FirstOrder.Language.BoundedFormula

variable {L : Language} {α β : Type*} {n k : ℕ}

/-! ### Instances -/

/-- The instance of a formula `φ` with `k` bound positions at a tuple `ts` of `k` terms: each bound
position `i` is replaced by the term `ts i`, and the free variables are kept. For one bound
position this is the formula usually written `φ[t]`. -/
def inst (φ : L.BoundedFormula α k) (ts : Fin k → L.Term α) : L.Formula α :=
  φ.toFormula.subst (Sum.elim Term.var ts)

theorem inst_def (φ : L.BoundedFormula α k) (ts : Fin k → L.Term α) :
    φ.inst ts = φ.toFormula.subst (Sum.elim Term.var ts) :=
  (rfl)

/-- An instance holds under an assignment exactly when the formula holds with the values of the
terms at the bound positions. -/
@[simp]
theorem realize_inst {M : Type*} [L.Structure M] (φ : L.BoundedFormula α k)
    (ts : Fin k → L.Term α) (v : α → M) :
    (φ.inst ts).Realize v ↔ φ.Realize v fun i => (ts i).realize v := by
  rw [inst_def, Formula.Realize, realize_subst, ← Formula.Realize, realize_toFormula]
  congr! with x

@[simp]
theorem inst_falsum (ts : Fin k → L.Term α) : (falsum : L.BoundedFormula α k).inst ts = falsum :=
  (rfl)

@[simp]
theorem inst_bot (ts : Fin k → L.Term α) : (⊥ : L.BoundedFormula α k).inst ts = ⊥ :=
  (rfl)

/-- The instance of an equation is the equation of the instances of its two terms. -/
@[simp]
theorem inst_bdEqual (t₁ t₂ : L.Term (α ⊕ Fin k)) (ts : Fin k → L.Term α) :
    (t₁.bdEqual t₂).inst ts =
      (t₁.subst (Sum.elim Term.var ts)).equal (t₂.subst (Sum.elim Term.var ts)) := by
  simp [inst_def, Term.bdEqual, Term.equal, Function.comp_def]

/-- The instance of an equation is the equation of the instances of its two terms. -/
@[simp]
theorem inst_equal (t₁ t₂ : L.Term (α ⊕ Fin k)) (ts : Fin k → L.Term α) :
    (equal t₁ t₂).inst ts =
      (t₁.subst (Sum.elim Term.var ts)).equal (t₂.subst (Sum.elim Term.var ts)) :=
  inst_bdEqual t₁ t₂ ts

/-- The instance of a relation atom applies the relation to the instances of its terms. -/
@[simp]
theorem inst_boundedFormula {l : ℕ} (R : L.Relations l) (us : Fin l → L.Term (α ⊕ Fin k))
    (ts : Fin k → L.Term α) :
    (R.boundedFormula us).inst ts = R.formula fun i => (us i).subst (Sum.elim Term.var ts) := by
  simp [inst_def, Relations.boundedFormula, Relations.formula, Function.comp_def]

/-- The instance of a relation atom applies the relation to the instances of its terms. -/
@[simp]
theorem inst_rel {l : ℕ} (R : L.Relations l) (us : Fin l → L.Term (α ⊕ Fin k))
    (ts : Fin k → L.Term α) :
    (rel R us).inst ts = R.formula fun i => (us i).subst (Sum.elim Term.var ts) :=
  inst_boundedFormula R us ts

@[simp]
theorem inst_imp (φ ψ : L.BoundedFormula α k) (ts : Fin k → L.Term α) :
    (φ.imp ψ).inst ts = (φ.inst ts).imp (ψ.inst ts) :=
  (rfl)

@[simp]
theorem inst_not (φ : L.BoundedFormula α k) (ts : Fin k → L.Term α) :
    φ.not.inst ts = (φ.inst ts).not :=
  (rfl)

/-- Substituting terms for the free variables of an instance gives the instance of the
substituted formula at the substituted terms. -/
theorem subst_inst (φ : L.BoundedFormula α k) (ts : Fin k → L.Term α) (f : α → L.Term β) :
    (φ.inst ts).subst f = (φ.subst f).inst fun i => (ts i).subst f := by
  simp only [inst_def, toFormula_subst, subst_subst]
  congr 1
  funext x
  rcases x with a | i <;> simp [Function.comp_def]

/-- The free variables of an instance are the free variables of the formula together with the
variables of the terms at those bound positions that occur in the formula, that is, become free
variables when the bound positions are opened. -/
theorem mem_freeVarFinset_inst [DecidableEq α] (φ : L.BoundedFormula α k)
    (ts : Fin k → L.Term α) {x : α} :
    x ∈ (φ.inst ts).freeVarFinset ↔
      x ∈ φ.freeVarFinset ∨ ∃ i, Sum.inr i ∈ φ.toFormula.freeVarFinset ∧ x ∈ (ts i).varFinset := by
  simp only [inst_def, freeVarFinset_subst, Finset.mem_biUnion, Sum.exists, Sum.elim_inl,
    Sum.elim_inr, Term.varFinset, Finset.mem_singleton, inl_mem_freeVarFinset_toFormula]
  exact or_congr ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨x, h, rfl⟩⟩ Iff.rfl

/-! ### Depth -/

/-- The depth of a formula: `0` for `⊥` and atomic formulas, one more than the larger depth of the
two sides for an implication, and one more than the depth of the body for a universal
quantifier. -/
def depth : ∀ {n}, L.BoundedFormula α n → ℕ
  | _, falsum => 0
  | _, equal _ _ => 0
  | _, rel _ _ => 0
  | _, imp φ ψ => max φ.depth ψ.depth + 1
  | _, all φ => φ.depth + 1

@[simp]
theorem depth_falsum : (falsum : L.BoundedFormula α n).depth = 0 :=
  (rfl)

@[simp]
theorem depth_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : (equal t₁ t₂).depth = 0 :=
  (rfl)

@[simp]
theorem depth_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).depth = 0 :=
  (rfl)

@[simp]
theorem depth_bdEqual (t₁ t₂ : L.Term (α ⊕ Fin n)) : (t₁.bdEqual t₂).depth = 0 :=
  (rfl)

@[simp]
theorem depth_boundedFormula {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (R.boundedFormula ts).depth = 0 :=
  (rfl)

@[simp]
theorem depth_imp (φ ψ : L.BoundedFormula α n) : (φ.imp ψ).depth = max φ.depth ψ.depth + 1 :=
  (rfl)

@[simp]
theorem depth_all (φ : L.BoundedFormula α (n + 1)) : φ.all.depth = φ.depth + 1 :=
  (rfl)

@[simp]
theorem depth_bot : (⊥ : L.BoundedFormula α n).depth = 0 :=
  (rfl)

/-- Negation `¬φ`, which is `φ → ⊥`, adds one to the depth. -/
@[simp]
theorem depth_not (φ : L.BoundedFormula α n) : φ.not.depth = φ.depth + 1 := by
  simp [BoundedFormula.not]

@[simp]
theorem depth_top : (⊤ : L.BoundedFormula α n).depth = 1 := by
  simp [top_def]

/-- Disjunction `φ ⊔ ψ`, which is `¬φ → ψ`. -/
@[simp]
theorem depth_sup (φ ψ : L.BoundedFormula α n) :
    (φ ⊔ ψ).depth = max (φ.depth + 1) ψ.depth + 1 := by
  simp [sup_def]

/-- Conjunction `φ ⊓ ψ`, which is `¬(φ → ¬ψ)`. -/
@[simp]
theorem depth_inf (φ ψ : L.BoundedFormula α n) :
    (φ ⊓ ψ).depth = max φ.depth (ψ.depth + 1) + 2 := by
  simp [inf_def]

/-- The existential quantifier `∃'φ`, which is `¬∀'¬φ`, adds three to the depth. -/
@[simp]
theorem depth_ex (φ : L.BoundedFormula α (n + 1)) : φ.ex.depth = φ.depth + 3 := by
  simp [BoundedFormula.ex]

/-- Atomic formulas have depth `0`. -/
theorem IsAtomic.depth_eq_zero {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : φ.depth = 0 := by
  cases h <;> simp

/-- Mapping the terms and relation symbols of a formula keeps its depth, provided the map applied
under each quantifier does. -/
theorem depth_mapTermRel {L' : Language} {g : ℕ → ℕ}
    (ft : ∀ n, L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin (g n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1))
    (hh : ∀ n ψ, (h n ψ).depth = ψ.depth) (φ : L.BoundedFormula α n) :
    (φ.mapTermRel ft fr h).depth = φ.depth := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ihφ ihψ => simp [mapTermRel, ihφ, ihψ]
  | all φ ih => simp [mapTermRel, hh, ih]

@[simp]
theorem depth_castLE {m : ℕ} (h : m ≤ n) (φ : L.BoundedFormula α m) :
    (φ.castLE h).depth = φ.depth := by
  induction φ generalizing n with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

@[simp]
theorem depth_relabel {m : ℕ} (g : α → β ⊕ Fin m) (φ : L.BoundedFormula α n) :
    (φ.relabel g).depth = φ.depth :=
  depth_mapTermRel _ _ _ (fun _ _ => depth_castLE _ _) φ

@[simp]
theorem depth_subst (φ : L.BoundedFormula α n) (f : α → L.Term β) :
    (φ.subst f).depth = φ.depth := by
  rw [subst]
  apply depth_mapTermRel
  exact fun _ _ => rfl

@[simp]
theorem depth_toFormula (φ : L.BoundedFormula α n) : φ.toFormula.depth = φ.depth := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

/-- An instance has the depth of the formula. -/
@[simp]
theorem depth_inst (φ : L.BoundedFormula α k) (ts : Fin k → L.Term α) :
    (φ.inst ts).depth = φ.depth := by
  simp [inst_def]

/-! ### Complexity classes of instances -/

/-- An instance of an atomic formula is atomic. -/
theorem IsAtomic.inst {φ : L.BoundedFormula α k} (h : φ.IsAtomic) (ts : Fin k → L.Term α) :
    (φ.inst ts).IsAtomic :=
  h.toFormula.subst _

/-- An instance of a quantifier-free formula is quantifier-free. -/
theorem IsQF.inst {φ : L.BoundedFormula α k} (h : φ.IsQF) (ts : Fin k → L.Term α) :
    (φ.inst ts).IsQF :=
  h.toFormula.subst _

end FirstOrder.Language.BoundedFormula
