/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Complexity

/-!
# Truth assignments and tautologies of first-order formulas

A first-order formula built from `⊥`, atoms, implication and the universal quantifier can be read
propositionally: give every atomic formula and every universal formula a truth value, let `⊥` be
false and let implication be material. A *truth assignment* `τ` gives every formula a truth value,
and `φ.PropRealize τ` is the truth value this reading assigns to `φ`; the values `τ` gives to
`⊥` and to implications are ignored. A formula is a *tautology* when it is true under every truth
assignment.

Every tautology holds in every structure under every assignment, since the actual truth values of
the atomic and universal formulas form a truth assignment. For a quantifier-free formula without
equations the converse holds as well: given a truth assignment, the structure on the terms in
which function symbols build terms and relation atoms take their values from the truth assignment
realizes such a formula exactly when the truth assignment makes it true. Equations must be
excluded, because a structure interprets an equation `t = t` as true while a truth assignment may
make it false.

This propositional reading is what turns Herbrand's theorem, which speaks of a valid disjunction
of instances of a quantifier-free formula, into a statement about tautologies when the formula has
no equations. Finite disjunctions of formulas, given by a list, are defined here for that purpose.

## Main definitions

* `FirstOrder.Language.BoundedFormula.PropRealize`: the truth value of a formula under a truth
  assignment.
* `FirstOrder.Language.BoundedFormula.IsTautology`: a formula true under every truth assignment.
* `FirstOrder.Language.BoundedFormula.disjunction`: the disjunction of a list of formulas.
* `FirstOrder.Language.Term.freeStructure`: the structure on the terms, lifted to any universe, in
  which function symbols build terms and relations are given by a predicate on tuples of terms.

## Main results

* `FirstOrder.Language.BoundedFormula.IsTautology.realize`: a tautology holds in every structure
  under every assignment.
* `FirstOrder.Language.BoundedFormula.IsQF.realize_freeStructure_iff`: a quantifier-free,
  equality-free formula holds in the free structure of a truth assignment, at the assignment
  sending each variable to itself, exactly when the truth assignment makes it true.
* `FirstOrder.Language.BoundedFormula.IsQF.isTautology_iff_forall_realize`: a quantifier-free,
  equality-free formula is a tautology exactly when it holds in every structure under every
  assignment.

## References

* Samuel R. Buss, *An introduction to proof theory*, in *Handbook of Proof Theory*, Elsevier,
  1998, the paragraph after the proof of Theorem 2.5.1: a quantifier-free consequence that does
  not involve equality is tautologically valid.
-/

public section

universe u v w uα uβ

namespace FirstOrder.Language

variable {L : Language.{u, v}} {α : Type uα} {β : Type uβ} {n : ℕ}

namespace BoundedFormula

/-! ### Truth assignments -/

/-- The truth value of a formula under a truth assignment `τ`, which gives every formula with `m`
bound positions a truth value `τ m`: `⊥` is false, an implication is material implication, and an
atomic or universal formula takes the value `τ` gives it. -/
def PropRealize : ∀ {n : ℕ}, L.BoundedFormula α n → ((m : ℕ) → L.BoundedFormula α m → Prop) →
    Prop
  | _, falsum, _ => False
  | n, equal t₁ t₂, τ => τ n (equal t₁ t₂)
  | n, rel R ts, τ => τ n (rel R ts)
  | _, imp φ ψ, τ => φ.PropRealize τ → ψ.PropRealize τ
  | n, all φ, τ => τ n (all φ)

variable {τ : (m : ℕ) → L.BoundedFormula α m → Prop} {φ ψ : L.BoundedFormula α n}

@[simp]
theorem propRealize_falsum : (falsum : L.BoundedFormula α n).PropRealize τ ↔ False :=
  Iff.rfl

@[simp]
theorem propRealize_bot : (⊥ : L.BoundedFormula α n).PropRealize τ ↔ False :=
  Iff.rfl

@[simp]
theorem propRealize_bdEqual (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁.bdEqual t₂).PropRealize τ ↔ τ n (t₁.bdEqual t₂) :=
  Iff.rfl

@[simp]
theorem propRealize_boundedFormula {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (R.boundedFormula ts).PropRealize τ ↔ τ n (R.boundedFormula ts) :=
  Iff.rfl

@[simp]
theorem propRealize_equal (t₁ t₂ : L.Term α) {τ : (m : ℕ) → L.BoundedFormula α m → Prop} :
    (t₁.equal t₂).PropRealize τ ↔ τ 0 (t₁.equal t₂) :=
  Iff.rfl

@[simp]
theorem propRealize_formula {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term α)
    {τ : (m : ℕ) → L.BoundedFormula α m → Prop} :
    (R.formula ts).PropRealize τ ↔ τ 0 (R.formula ts) :=
  Iff.rfl

@[simp]
theorem propRealize_imp : (φ.imp ψ).PropRealize τ ↔ (φ.PropRealize τ → ψ.PropRealize τ) :=
  Iff.rfl

@[simp]
theorem propRealize_all (φ : L.BoundedFormula α (n + 1)) : φ.all.PropRealize τ ↔ τ n φ.all :=
  Iff.rfl

/-- An atomic formula takes the value the truth assignment gives it. -/
theorem IsAtomic.propRealize_iff (h : φ.IsAtomic) : φ.PropRealize τ ↔ τ n φ := by
  cases h <;> rfl

@[simp]
theorem propRealize_not : φ.not.PropRealize τ ↔ ¬φ.PropRealize τ :=
  Iff.rfl

@[simp]
theorem propRealize_top : (⊤ : L.BoundedFormula α n).PropRealize τ :=
  propRealize_not.2 id

@[simp]
theorem propRealize_sup : (φ ⊔ ψ).PropRealize τ ↔ φ.PropRealize τ ∨ ψ.PropRealize τ :=
  propRealize_imp.trans <| by rw [propRealize_not, or_iff_not_imp_left]

@[simp]
theorem propRealize_inf : (φ ⊓ ψ).PropRealize τ ↔ φ.PropRealize τ ∧ ψ.PropRealize τ :=
  propRealize_not.trans <| by rw [propRealize_imp, propRealize_not, Classical.not_imp, not_not]

/-- When a truth assignment gives each formula with `n` bound positions its actual truth value
under an assignment, every formula with `n` bound positions has its actual truth value. -/
theorem propRealize_iff_realize {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}
    (hτ : ∀ ψ : L.BoundedFormula α n, τ n ψ ↔ ψ.Realize v xs) (φ : L.BoundedFormula α n) :
    φ.PropRealize τ ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => exact hτ _
  | rel R ts => exact hτ _
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ hτ) (ihψ hτ)
  | all φ _ => exact hτ _

/-! ### Tautologies -/

/-- A formula is a tautology when it is true under every truth assignment, that is, under every
assignment of truth values to its atomic and universal subformulas. -/
def IsTautology (φ : L.BoundedFormula α n) : Prop :=
  ∀ τ : (m : ℕ) → L.BoundedFormula α m → Prop, φ.PropRealize τ

theorem isTautology_iff : φ.IsTautology ↔ ∀ τ : (m : ℕ) → L.BoundedFormula α m → Prop,
    φ.PropRealize τ :=
  Iff.rfl

/-- A tautology holds in every structure under every assignment. -/
theorem IsTautology.realize (h : φ.IsTautology) {M : Type w} [L.Structure M] (v : α → M)
    (xs : Fin n → M) : φ.Realize v xs :=
  -- The truth assignment of actual truth values, at the level `n` of `φ`; at that level the
  -- cast `h ▸ ψ` along `h : n = n` reduces to `ψ`.
  (propRealize_iff_realize (τ := fun m ψ => ∃ h : m = n, (h ▸ ψ).Realize v xs)
    (fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩) φ).1 (h _)

/-! ### Disjunctions of lists -/

/-- The disjunction `φ₁ ⊔ (φ₂ ⊔ ⋯ ⊔ (φₘ ⊔ ⊥))` of a list of formulas; the empty disjunction is
`⊥`. -/
def disjunction (l : List (L.BoundedFormula α n)) : L.BoundedFormula α n :=
  l.foldr (· ⊔ ·) ⊥

theorem disjunction_def (l : List (L.BoundedFormula α n)) :
    disjunction l = l.foldr (· ⊔ ·) ⊥ :=
  (rfl)

@[simp]
theorem disjunction_nil : disjunction ([] : List (L.BoundedFormula α n)) = ⊥ :=
  (rfl)

@[simp]
theorem disjunction_cons (φ : L.BoundedFormula α n) (l : List (L.BoundedFormula α n)) :
    disjunction (φ :: l) = φ ⊔ disjunction l :=
  (rfl)

/-- A disjunction holds exactly when one of its disjuncts does. -/
@[simp]
theorem realize_disjunction {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}
    {l : List (L.BoundedFormula α n)} :
    (disjunction l).Realize v xs ↔ ∃ φ ∈ l, φ.Realize v xs :=
  realize_foldr_sup l v xs

/-- A disjunction is true under a truth assignment exactly when one of its disjuncts is. -/
@[simp]
theorem propRealize_disjunction {l : List (L.BoundedFormula α n)} :
    (disjunction l).PropRealize τ ↔ ∃ φ ∈ l, φ.PropRealize τ := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

/-- The disjunction of a list of quantifier-free formulas is quantifier-free. -/
theorem IsQF.disjunction {l : List (L.BoundedFormula α n)} (hl : ∀ φ ∈ l, φ.IsQF) :
    (disjunction l).IsQF :=
  IsQF.foldr_sup hl

/-- A disjunction is equality-free exactly when each of its disjuncts is. -/
@[simp]
theorem isEqualityFree_disjunction_iff {l : List (L.BoundedFormula α n)} :
    (disjunction l).IsEqualityFree ↔ ∀ φ ∈ l, φ.IsEqualityFree := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

end BoundedFormula

/-- A disjunction of formulas holds exactly when one of its disjuncts does. -/
@[simp]
theorem Formula.realize_disjunction {M : Type w} [L.Structure M] {v : α → M}
    {l : List (L.Formula α)} :
    Formula.Realize (BoundedFormula.disjunction l) v ↔ ∃ φ ∈ l, φ.Realize v :=
  BoundedFormula.realize_disjunction

/-! ### The free structure on terms -/

namespace Term

/-- The structure on the terms `L.Term β`, lifted to the universe `max u uβ w`, in which each
function symbol builds terms and the relations hold of the tuples of terms selected by `r`. -/
@[instance_reducible]
def freeStructure (r : ∀ ⦃l : ℕ⦄, L.Relations l → (Fin l → L.Term β) → Prop) :
    L.Structure (ULift.{w} (L.Term β)) where
  funMap f xs := ⟨func f fun i => (xs i).down⟩
  RelMap R xs := r R fun i => (xs i).down

variable (r : ∀ ⦃l : ℕ⦄, L.Relations l → (Fin l → L.Term β) → Prop)

@[simp]
theorem funMap_freeStructure {l : ℕ} (f : L.Functions l) (xs : Fin l → ULift.{w} (L.Term β)) :
    (freeStructure r).funMap f xs = ⟨func f fun i => (xs i).down⟩ :=
  (rfl)

@[simp]
theorem relMap_freeStructure {l : ℕ} (R : L.Relations l) (xs : Fin l → ULift.{w} (L.Term β)) :
    (freeStructure r).RelMap R xs ↔ r R fun i => (xs i).down :=
  Iff.rfl

/-- In the free structure, a term takes itself as its value when each variable is sent to
itself. -/
@[simp]
theorem realize_freeStructure (t : L.Term β) :
    letI := freeStructure.{u, v, w} r
    t.realize (fun b => ULift.up.{w} (var b)) = ULift.up.{w} t := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [realize, funMap_freeStructure, ih]

end Term

namespace BoundedFormula

variable {φ : L.BoundedFormula α n}

/-- A quantifier-free, equality-free formula holds in the free structure of a truth assignment
`τ`, under the assignment sending every free and every bound variable to itself, exactly when `τ`
makes it true. The relations of the free structure hold of the tuples whose relation atoms `τ`
makes true. -/
theorem IsQF.realize_freeStructure_iff (hφ : φ.IsQF) (he : φ.IsEqualityFree)
    (τ : (m : ℕ) → L.BoundedFormula α m → Prop) :
    letI := Term.freeStructure.{u, v, w} fun _ R ts => τ n (R.boundedFormula ts)
    φ.Realize (fun a => ULift.up.{w} (Term.var (Sum.inl a) : L.Term (α ⊕ Fin n)))
        (fun i => ULift.up.{w} (Term.var (Sum.inr i) : L.Term (α ⊕ Fin n))) ↔
      φ.PropRealize τ := by
  have hv : (Sum.elim (fun a => ULift.up.{w} (Term.var (Sum.inl a))) fun i =>
      ULift.up.{w} (Term.var (Sum.inr i)) : α ⊕ Fin n → ULift.{w} (L.Term (α ⊕ Fin n))) =
      fun b => ULift.up.{w} (Term.var b) := by
    ext (_ | _) <;> rfl
  induction hφ with
  | falsum => rfl
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ => exact absurd he (not_isEqualityFree_bdEqual t₁ t₂)
    | rel R ts =>
      simp only [realize_rel, hv, Term.realize_freeStructure, Term.relMap_freeStructure,
        propRealize_boundedFormula]
  | imp _ _ ih₁ ih₂ =>
    rw [isEqualityFree_imp_iff] at he
    exact imp_congr (ih₁ he.1) (ih₂ he.2)

/-- A quantifier-free, equality-free formula is a tautology exactly when it holds in every
structure, on a carrier in the universe `max u uα w`, under every assignment. -/
theorem IsQF.isTautology_iff_forall_realize (hφ : φ.IsQF) (he : φ.IsEqualityFree) :
    φ.IsTautology ↔ ∀ (M : Type (max u uα w)) [L.Structure M] (v : α → M) (xs : Fin n → M),
      φ.Realize v xs :=
  ⟨fun h _ _ v xs => h.realize v xs, fun h τ =>
    (hφ.realize_freeStructure_iff he τ).1 (@h (ULift.{w} (L.Term (α ⊕ Fin n)))
      (Term.freeStructure fun _ R ts => τ n (R.boundedFormula ts)) _ _)⟩

end BoundedFormula

end FirstOrder.Language
