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
# The formula of a finite system of equations and inequations

A finite system of word equations `S_j(X, A) = 1` and inequations `T_k(X, A) ≠ 1` is the
quantifier-free formula `⋀ (S_j = 1) ∧ ⋀ (T_k ≠ 1)` of the group language with coefficient
names `A`: each word is spelled by its canonical term, an equation becomes an atomic formula and
an inequation a negated atomic formula. In every group, and for every interpretation of the
coefficients, an assignment realizes this formula exactly when it solves the system.

## Main definitions and results

* `TauCeti.EqIneqSystem.toFormula`: the conjunction of the atomic formulas of the equations and
  the negated atomic formulas of the inequations.
* `TauCeti.EqIneqSystem.realize_toFormula`: the formula is realized exactly by the solutions.
* `TauCeti.EqIneqSystem.isQF_toFormula`: the formula is quantifier-free.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, §2.3: atomic
  formulas are equations `S(X, A) = 1`, and a conjunction of atomic formulas and their negations
  is a system `⋀ (S_j(X, A) = 1) & ⋀ (T_k(X, A) ≠ 1)`.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group II*,
  Definition 9: the matrices `⋀ u_i = 1 ∧ ⋀ v_j ≠ 1` of the existential theory of a group.
-/

public section

namespace TauCeti.EqIneqSystem

open FirstOrder FirstOrder.Language FirstOrder.Language.group

variable {X A : Type*}

/-- The formula of a system: the conjunction of the atomic formulas `S = 1` over its equations
and of the negated atomic formulas `¬(T = 1)` over its inequations, each word being spelled by
its canonical term. -/
noncomputable def toFormula (S : EqIneqSystem X A) : Language.group[[A]].Formula X :=
  (S.eqs.map fun w => (Term.ofWord w).equal 1).foldr (· ⊓ ·) ⊤ ⊓
    (S.ineqs.map fun w => ∼((Term.ofWord w).equal 1)).foldr (· ⊓ ·) ⊤

/-- The formula of a system is the conjunction of its equations, as atomic formulas, and of its
inequations, as negated atomic formulas. -/
theorem toFormula_def (S : EqIneqSystem X A) :
    S.toFormula = (S.eqs.map fun w => (Term.ofWord w).equal 1).foldr (· ⊓ ·) ⊤ ⊓
      (S.ineqs.map fun w => ∼((Term.ofWord w).equal 1)).foldr (· ⊓ ·) ⊤ := (rfl)

/-- The formula of a system is quantifier-free. -/
theorem isQF_toFormula (S : EqIneqSystem X A) : S.toFormula.IsQF := by
  refine .inf (.foldr_inf fun φ hφ => ?_) (.foldr_inf fun φ hφ => ?_) <;>
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hφ
  exacts [(BoundedFormula.IsAtomic.equal _ _).isQF, (BoundedFormula.IsAtomic.equal _ _).isQF.not]

/-- An assignment realizes the formula of a system exactly when it solves the system, in every
group and for every interpretation of the coefficients. -/
@[simp] theorem realize_toFormula {G : Type*} [Group G] (S : EqIneqSystem X A) (v : X → G)
    (c : A → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    S.toFormula.Realize v ↔ S.IsSolution v c := by
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  simp [toFormula_def, Formula.Realize, BoundedFormula.realize_foldr_inf, isSolution_iff,
    eval_eq_lift, Term.equal]

open FreeGroup (of)
open scoped commutatorElement

/-- Every assignment realizes the formula of the empty system. -/
example {G : Type*} [Group G] (v : X → G) (c : A → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    (empty X A).toFormula.Realize v := by
  simp

/-- The formula of the system `[x, a] = 1`, `x ≠ 1` with a coefficient letter `a` says that `x`
commutes with the value of `a` and is nontrivial. -/
example {G : Type*} [Group G] (x : X) (a : A) (v : X → G) (c : A → G) :
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    (⟨[⁅(of (Sum.inl x) : FreeGroup (X ⊕ A)), of (Sum.inr a)⁆],
      [of (Sum.inl x)]⟩ : EqIneqSystem X A).toFormula.Realize v ↔
      Commute (v x) (c a) ∧ v x ≠ 1 := by
  simp [isSolution_iff, map_commutatorElement, commutatorElement_eq_one_iff_commute]

/-- In the free group on `a` and `b`, the formula of the system `[x, a] = 1`, `x ≠ 1` is realized
by `x = a⁻¹`. -/
example :
    letI : Language.group.Structure (FreeGroup (Fin 2)) := TauCeti.Group.structureOfGroup _
    letI : (Language.constantsOn (Fin 2)).Structure (FreeGroup (Fin 2)) :=
      Language.constantsOn.structure FreeGroup.of
    (⟨[⁅(of (Sum.inl ()) : FreeGroup (Unit ⊕ Fin 2)), of (Sum.inr 0)⁆],
      [of (Sum.inl ())]⟩ : EqIneqSystem Unit (Fin 2)).toFormula.Realize
      fun _ => (of (0 : Fin 2))⁻¹ := by
  simp [isSolution_iff, map_commutatorElement, commutatorElement_eq_one_iff_commute,
    FreeGroup.of_ne_one]

/-- In the free group on `a` and `b`, the formula of the system `[x, a] = 1`, `x ≠ 1` is not
realized by `x = 1`, which satisfies the equation and violates the inequation. -/
example :
    letI : Language.group.Structure (FreeGroup (Fin 2)) := TauCeti.Group.structureOfGroup _
    letI : (Language.constantsOn (Fin 2)).Structure (FreeGroup (Fin 2)) :=
      Language.constantsOn.structure FreeGroup.of
    ¬(⟨[⁅(of (Sum.inl ()) : FreeGroup (Unit ⊕ Fin 2)), of (Sum.inr 0)⁆],
      [of (Sum.inl ())]⟩ : EqIneqSystem Unit (Fin 2)).toFormula.Realize
      fun _ => (1 : FreeGroup (Fin 2)) := by
  simp [isSolution_iff]

end TauCeti.EqIneqSystem
