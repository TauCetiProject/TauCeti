/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.TermWord
public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem.Basic
public import TauCeti.ModelTheory.Complexity

/-!
# Group formulas as finite families of word systems

Every quantifier-free formula in the group language with named coefficients is equivalent,
in every group and for every interpretation of the coefficients, to a finite disjunction of
systems of word equations and inequations. The same finite family describes an existential
formula `∃ y₁ … ∃ y_k, φ`, once the witnesses `y₁, …, y_k` become variables of the systems.

The family is computed by `FirstOrder.Language.BoundedFormula.eqIneqSystems`, a disjunctive
normal form defined by structural recursion on the formula: an atomic equality `t = s` gives the
equation `toWord t * (toWord s)⁻¹ = 1`, its negation gives the corresponding inequation, and the
connectives are distributed over the resulting lists. The variables of the systems are the free
variables of the formula and the natural numbers, the bound variable with index `i` (Mathlib's
`&i`) becoming the variable `i`; a universal quantifier over the variable `n` keeps the systems of
the negated body, in which `n` is a free variable. So the systems of `∃ y, φ` are those of `φ`,
the witness `y` being one more variable, and the systems of `¬∀ y, φ` are those of `¬φ`. The
family depends only on the formula, not on the group or on the interpretation of the
coefficients.

## Main declarations

* `FirstOrder.Language.BoundedFormula.eqIneqSystems`: the finite list of equation–inequation
  systems of a group formula; the systems of `¬φ` are `φ.not.eqIneqSystems`.
* `FirstOrder.Language.group.quantifierFree_iff_systems`: a quantifier-free formula holds exactly
  when one of its systems is solved.

The equations-and-inequations normal form follows Kharlampovich and Myasnikov,
*Implicit function theorem over free groups*, §2.3.
-/

public section

namespace FirstOrder.Language.BoundedFormula

open FirstOrder TauCeti

variable {X A : Type*} {n : ℕ}

/-- The word `toWord t * (toWord s)⁻¹` of an atomic equality `t = s`, with the bound variable `i`
read as the variable `i : ℕ`. -/
private def atomWord (t s : Language.group[[A]].Term (X ⊕ Fin n)) : FreeGroup ((X ⊕ ℕ) ⊕ A) :=
  FreeGroup.map (Sum.map (Sum.map id Fin.val) id)
    (group.Term.toWord t * (group.Term.toWord s)⁻¹)

/-- Disjunctive normal forms of a group formula and of its negation, computed together by
structural recursion. A universal quantification `∀ y, φ` keeps the systems of `¬φ`, the bound
variable `y` becoming a free variable of the systems, and has no systems of its own. -/
private def eqIneqSystemsPair : ∀ {n : ℕ}, Language.group[[A]].BoundedFormula X n →
    List (EqIneqSystem (X ⊕ ℕ) A) × List (EqIneqSystem (X ⊕ ℕ) A)
  | _, falsum => ([], [EqIneqSystem.empty _ _])
  | _, equal t s => ([⟨[atomWord t s], []⟩], [⟨[], [atomWord t s]⟩])
  | _, rel (Sum.inl r) _ => nomatch r
  | _, rel (Sum.inr r) _ => nomatch r
  | _, imp φ ψ =>
    ((eqIneqSystemsPair φ).2 ++ (eqIneqSystemsPair ψ).1,
      EqIneqSystem.disjunctionProduct (eqIneqSystemsPair φ).1 (eqIneqSystemsPair ψ).2)
  | _, all φ => ([], (eqIneqSystemsPair φ).2)

/-- The equation–inequation systems of a group formula with named coefficients `A`: a finite
disjunctive normal form whose variables are the free variables of the formula and the natural
numbers, the bound variable `&i` being the variable `i`. An atomic equality `t = s` gives the
single equation `toWord t * (toWord s)⁻¹ = 1`; the systems of `¬φ` are `φ.not.eqIneqSystems`.
A quantifier-free or existential formula holds exactly when one of its systems is solved
(`FirstOrder.Language.group.quantifierFree_iff_systems`,
`FirstOrder.Language.group.existential_iff_systems`), and a universal formula exactly when none of
the systems of its negation is solved (`FirstOrder.Language.group.universal_iff_systems`). For
other formulas the list need not describe the formula: in `(∃ x, x = a) ∧ (∃ y, y = b)` both
witnesses are the variable `0`, so the single system `x = a, x = b` is unsolvable in `F(a, b)`
although the formula holds there. -/
def eqIneqSystems (φ : Language.group[[A]].BoundedFormula X n) :
    List (EqIneqSystem (X ⊕ ℕ) A) := (eqIneqSystemsPair φ).1

/-- The constructor `falsum` for the false formula has no systems. -/
@[simp] theorem eqIneqSystems_falsum :
    (falsum : Language.group[[A]].BoundedFormula X n).eqIneqSystems = [] := by rfl

/-- The false formula has no systems. -/
@[simp] theorem eqIneqSystems_bot :
    (⊥ : Language.group[[A]].BoundedFormula X n).eqIneqSystems = [] := by rfl

/-- The negation of `falsum` has a single system, the empty one. -/
@[simp] theorem eqIneqSystems_not_falsum :
    (falsum : Language.group[[A]].BoundedFormula X n).not.eqIneqSystems =
      [EqIneqSystem.empty _ _] := by
  simp [eqIneqSystems, eqIneqSystemsPair]

/-- The true formula has a single system, the empty one. -/
@[simp] theorem eqIneqSystems_top :
    (⊤ : Language.group[[A]].BoundedFormula X n).eqIneqSystems = [EqIneqSystem.empty _ _] := by
  simp [eqIneqSystems, eqIneqSystemsPair]

/-- An atomic equality `t = s` has the single equation `toWord t * (toWord s)⁻¹ = 1`, the bound
variable `&i` read as the variable `i`. -/
@[simp] theorem eqIneqSystems_bdEqual (t s : Language.group[[A]].Term (X ⊕ Fin n)) :
    (t.bdEqual s).eqIneqSystems = [⟨[FreeGroup.map (Sum.map (Sum.map id Fin.val) id)
      (group.Term.toWord t * (group.Term.toWord s)⁻¹)], []⟩] := by
  rfl

/-- A negated atomic equality `t ≠ s` has the single inequation
`toWord t * (toWord s)⁻¹ ≠ 1`, the bound variable `&i` read as the variable `i`. -/
@[simp] theorem eqIneqSystems_not_bdEqual (t s : Language.group[[A]].Term (X ⊕ Fin n)) :
    (t.bdEqual s).not.eqIneqSystems = [⟨[], [FreeGroup.map (Sum.map (Sum.map id Fin.val) id)
      (group.Term.toWord t * (group.Term.toWord s)⁻¹)]⟩] := by
  simp [eqIneqSystems, eqIneqSystemsPair, Term.bdEqual, atomWord]

/-- The systems of an implication `φ → ψ` are those of `¬φ` followed by those of `ψ`. -/
@[simp] theorem eqIneqSystems_imp (φ ψ : Language.group[[A]].BoundedFormula X n) :
    (φ.imp ψ).eqIneqSystems = φ.not.eqIneqSystems ++ ψ.eqIneqSystems := by
  simp [eqIneqSystems, eqIneqSystemsPair]

/-- The systems of a negated implication `¬(φ → ψ)` append a system of `φ` to a system of
`¬ψ` in every possible way. -/
@[simp] theorem eqIneqSystems_not_imp (φ ψ : Language.group[[A]].BoundedFormula X n) :
    (φ.imp ψ).not.eqIneqSystems =
      EqIneqSystem.disjunctionProduct φ.eqIneqSystems ψ.not.eqIneqSystems := by
  simp [eqIneqSystems, eqIneqSystemsPair]

/-- A double negation has the systems of the formula itself. -/
@[simp] theorem eqIneqSystems_not_not (φ : Language.group[[A]].BoundedFormula X n) :
    φ.not.not.eqIneqSystems = φ.eqIneqSystems := by
  simp [eqIneqSystems, eqIneqSystemsPair]

/-- The systems of a disjunction are those of the two disjuncts. -/
@[simp] theorem eqIneqSystems_sup (φ ψ : Language.group[[A]].BoundedFormula X n) :
    (φ ⊔ ψ).eqIneqSystems = φ.eqIneqSystems ++ ψ.eqIneqSystems := by
  simp [Max.max]

/-- The systems of a conjunction append a system of each conjunct in every possible way. -/
@[simp] theorem eqIneqSystems_inf (φ ψ : Language.group[[A]].BoundedFormula X n) :
    (φ ⊓ ψ).eqIneqSystems = EqIneqSystem.disjunctionProduct φ.eqIneqSystems ψ.eqIneqSystems := by
  simp [Min.min]

/-- A universal quantification `∀ y, φ` has no systems: a universal formula is described through
the systems of its negation, `eqIneqSystems_not_all`. -/
@[simp] theorem eqIneqSystems_all (φ : Language.group[[A]].BoundedFormula X (n + 1)) :
    φ.all.eqIneqSystems = [] := by rfl

/-- The systems of a negated universal quantification `¬∀ y, φ` are those of `¬φ`, the bound
variable `y` being a free variable of the systems. -/
@[simp] theorem eqIneqSystems_not_all (φ : Language.group[[A]].BoundedFormula X (n + 1)) :
    φ.all.not.eqIneqSystems = φ.not.eqIneqSystems := by
  simp [eqIneqSystems, eqIneqSystemsPair]

/-- The systems of an existential quantification `∃ y, φ` are those of `φ`, the bound variable `y`
being a free variable of the systems. -/
@[simp] theorem eqIneqSystems_ex (φ : Language.group[[A]].BoundedFormula X (n + 1)) :
    φ.ex.eqIneqSystems = φ.eqIneqSystems := by
  simp [eqIneqSystems, eqIneqSystemsPair]

end FirstOrder.Language.BoundedFormula

namespace FirstOrder.Language.group

open FirstOrder TauCeti

variable {X A : Type*} {n : ℕ}

/-- A quantifier-free formula and its negation each hold exactly when one of their systems is
solved. -/
private theorem realize_iff_and_not_realize_iff {φ : Language.group[[A]].BoundedFormula X n}
    (hφ : φ.IsQF) {G : Type*} [Group G] (v : X → G) (c : A → G) (w : ℕ → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    (φ.Realize v (fun i => w i) ↔ ∃ S ∈ φ.eqIneqSystems, S.IsSolution (Sum.elim v w) c) ∧
      (¬φ.Realize v (fun i => w i) ↔
        ∃ S ∈ φ.not.eqIneqSystems, S.IsSolution (Sum.elim v w) c) := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  induction hφ with
  | falsum => simp [BoundedFormula.Realize]
  | of_isAtomic h =>
    cases h with
    | equal t s =>
      have hcomp : Sum.elim v w ∘ Sum.map id Fin.val = Sum.elim v fun i : Fin n => w i :=
        Sum.elim_comp_map
      have heq := Term.realize_equal_iff c (Sum.elim v fun i : Fin _ => w i) t s
      rw [← EqIneqSystem.eval_eq_lift] at heq
      constructor
      · simpa [EqIneqSystem.isSolution_iff, hcomp] using heq
      · simpa [EqIneqSystem.isSolution_iff, hcomp] using not_congr heq
    | rel R _ =>
      -- The coefficient extension has two empty relation-symbol summands.
      rcases R with r | r <;> exact nomatch r
  | imp _ _ ih₁ ih₂ =>
    constructor
    · rw [BoundedFormula.realize_imp, BoundedFormula.eqIneqSystems_imp]
      simp [or_and_right, exists_or, ← ih₁.2, ← ih₂.1, imp_iff_not_or]
    · rw [BoundedFormula.realize_imp, BoundedFormula.eqIneqSystems_not_imp,
        EqIneqSystem.exists_isSolution_disjunctionProduct, ← ih₁.1, ← ih₂.2, not_imp]

/-- A quantifier-free group formula holds, at the values `v` of its free variables and
`w 0, …, w (n - 1)` of its bound variables, exactly when the assignment `Sum.elim v w` solves one
of its finitely many equation–inequation systems `φ.eqIneqSystems`. The systems depend only on
the formula, so the equivalence holds uniformly in every group and every interpretation `c` of the
coefficient names. -/
theorem quantifierFree_iff_systems {φ : Language.group[[A]].BoundedFormula X n} (hφ : φ.IsQF)
    {G : Type*} [Group G] (v : X → G) (c : A → G) (w : ℕ → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    φ.Realize v (fun i => w i) ↔ ∃ S ∈ φ.eqIneqSystems, S.IsSolution (Sum.elim v w) c :=
  (realize_iff_and_not_realize_iff hφ v c w).1

open scoped commutatorElement

/-- The quantifier-free formula `x ≠ a ∨ x * y = y * x`, with `a` a coefficient name and `x`, `y`
the bound variables `&0`, `&1`, has the two systems `([], [x a⁻¹])` and `([⁅x, y⁆], [])`. -/
example (a : A) :
    ((Term.bdEqual (&0 : Language.group[[A]].Term (Empty ⊕ Fin 2))
        (Constants.term (Sum.inr a))).not ⊔
      Term.bdEqual (&0 * &1 : Language.group[[A]].Term (Empty ⊕ Fin 2)) (&1 * &0)).eqIneqSystems =
      [⟨[], [FreeGroup.of (Sum.inl (Sum.inr 0)) * (FreeGroup.of (Sum.inr a))⁻¹]⟩,
        ⟨[⁅(FreeGroup.of (Sum.inl (Sum.inr 0)) : FreeGroup ((Empty ⊕ ℕ) ⊕ A)),
          FreeGroup.of (Sum.inl (Sum.inr 1))⁆], []⟩] := by
  simp [commutatorElement_def, mul_assoc]

end FirstOrder.Language.group
