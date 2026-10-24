/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Finite systems of equations and inequations over a free group

An equation or inequation with variables `X` and coefficient letters `A` is a word in
`FreeGroup (X ⊕ A)`. A solution assigns group elements to the variables and coefficients,
then evaluates each word by `FreeGroup.lift`. Keeping the two finite lists separate makes
their conjunction available to normal forms for quantifier-free group formulas.

The equation–inequation viewpoint follows Kharlampovich and Myasnikov, *Implicit function
theorem over free groups*, §2.3.
-/

public section

namespace TauCeti

/-- A finite conjunction of equations and inequations in variables `X` with coefficient
letters `A`. The lists need not be deduplicated: they are finite syntax, and their order has
no effect on solutions. -/
@[ext] structure EqIneqSystem (X A : Type*) where
  /-- Words required to evaluate to the identity. -/
  eqs : List (FreeGroup (X ⊕ A))
  /-- Words required to evaluate away from the identity. -/
  ineqs : List (FreeGroup (X ⊕ A))

namespace EqIneqSystem

variable {X A : Type*} {G H : Type*} [Group G] [Group H]

/-- Evaluation of a word under a variable assignment and a coefficient map. -/
def eval (v : X → G) (c : A → G) : FreeGroup (X ⊕ A) →* G :=
  FreeGroup.lift (Sum.elim v c)

/-- Evaluation is the lift of the assignments on variable and coefficient letters. -/
theorem eval_eq_lift (v : X → G) (c : A → G) :
    eval v c = FreeGroup.lift (Sum.elim v c) := by rfl

/-- Evaluation of a generator selects its variable or coefficient value. -/
@[simp] theorem eval_of (v : X → G) (c : A → G) (i : X ⊕ A) :
    eval v c (FreeGroup.of i) = Sum.elim v c i := by
  simp [eval]

/-- A variable assignment solves a system when all equations vanish and all inequations
remain nontrivial after evaluation. -/
def IsSolution (S : EqIneqSystem X A) (v : X → G) (c : A → G) : Prop :=
  (∀ w ∈ S.eqs, eval v c w = 1) ∧ (∀ w ∈ S.ineqs, eval v c w ≠ 1)

/-- Solving a system means satisfying every equation and every inequation. -/
theorem isSolution_iff (S : EqIneqSystem X A) (v : X → G) (c : A → G) :
    S.IsSolution v c ↔
      (∀ w ∈ S.eqs, eval v c w = 1) ∧ (∀ w ∈ S.ineqs, eval v c w ≠ 1) :=
  Iff.rfl

/-- Every equation in a solved system evaluates to the identity. -/
theorem IsSolution.eval_eq_one {S : EqIneqSystem X A} {v : X → G} {c : A → G}
    (h : S.IsSolution v c) {w : FreeGroup (X ⊕ A)} (hw : w ∈ S.eqs) :
    eval v c w = 1 := h.1 w hw

/-- Every inequation in a solved system evaluates away from the identity. -/
theorem IsSolution.eval_ne_one {S : EqIneqSystem X A} {v : X → G} {c : A → G}
    (h : S.IsSolution v c) {w : FreeGroup (X ⊕ A)} (hw : w ∈ S.ineqs) :
    eval v c w ≠ 1 := h.2 w hw

/-- Equations and inequations together establish that an assignment solves a system. -/
theorem isSolution_of_forall (S : EqIneqSystem X A) (v : X → G) (c : A → G)
    (he : ∀ w ∈ S.eqs, eval v c w = 1) (hi : ∀ w ∈ S.ineqs, eval v c w ≠ 1) :
    S.IsSolution v c := ⟨he, hi⟩

/-- The empty system places no conditions on an assignment. -/
def empty (X A : Type*) : EqIneqSystem X A := ⟨[], []⟩

/-- The empty system has no equations. -/
@[simp] theorem eqs_empty (X A : Type*) : (empty X A).eqs = [] := by rfl

/-- The empty system has no inequations. -/
@[simp] theorem ineqs_empty (X A : Type*) : (empty X A).ineqs = [] := by rfl

/-- Every assignment solves the empty system. -/
@[simp] theorem isSolution_empty (v : X → G) (c : A → G) :
    (empty X A).IsSolution v c := by
  simp [empty, IsSolution]

/-- Concatenating the two constraint lists forms the conjunction of two systems. -/
def append (S T : EqIneqSystem X A) : EqIneqSystem X A :=
  ⟨S.eqs ++ T.eqs, S.ineqs ++ T.ineqs⟩

/-- Appending systems concatenates their equations. -/
@[simp] theorem eqs_append (S T : EqIneqSystem X A) :
    (S.append T).eqs = S.eqs ++ T.eqs := by rfl

/-- Appending systems concatenates their inequations. -/
@[simp] theorem ineqs_append (S T : EqIneqSystem X A) :
    (S.append T).ineqs = S.ineqs ++ T.ineqs := by rfl

/-- An assignment solves an appended system exactly when it solves both systems. -/
@[simp] theorem isSolution_append (S T : EqIneqSystem X A) (v : X → G) (c : A → G) :
    (S.append T).IsSolution v c ↔ S.IsSolution v c ∧ T.IsSolution v c := by
  simp [IsSolution, append, List.mem_append, or_imp, forall_and, and_assoc,
    and_left_comm]

/-- Evaluation commutes with a group homomorphism when the variables and coefficients are
mapped along that homomorphism. -/
@[simp] theorem comp_eval (φ : G →* H) (v : X → G) (c : A → G) :
    φ.comp (eval v c) = eval (φ ∘ v) (φ ∘ c) := by
  apply FreeGroup.ext_hom
  intro i
  cases i <;> simp [Function.comp_def]

/-- Evaluation commutes pointwise with a group homomorphism. -/
@[simp] theorem map_eval (φ : G →* H) (v : X → G) (c : A → G)
    (w : FreeGroup (X ⊕ A)) :
    φ (eval v c w) = eval (φ ∘ v) (φ ∘ c) w := by
  rw [← comp_eval]
  rfl

/-- Equations remain solved after any group homomorphism. -/
theorem eqs_comp_eq_one (S : EqIneqSystem X A) (φ : G →* H)
    (v : X → G) (c : A → G) (h : ∀ w ∈ S.eqs, eval v c w = 1) :
    ∀ w ∈ S.eqs, eval (φ ∘ v) (φ ∘ c) w = 1 := by
  intro w hw
  rw [← map_eval, h w hw]
  simp

/-- Injective group homomorphisms preserve and reflect solutions, including inequations. -/
theorem isSolution_comp_iff_of_injective (S : EqIneqSystem X A) (φ : G →* H)
    (hφ : Function.Injective φ) (v : X → G) (c : A → G) :
    S.IsSolution (φ ∘ v) (φ ∘ c) ↔ S.IsSolution v c := by
  simp only [IsSolution, ← comp_eval, MonoidHom.coe_comp, Function.comp_apply,
    map_eq_one_iff φ hφ, ne_eq]

/-- A coefficient-preserving embedding can be used with a separately named coefficient map
in the target. -/
theorem isSolution_comp_iff_of_injective_coeff (S : EqIneqSystem X A) (φ : G →* H)
    (hφ : Function.Injective φ) (v : X → G) (c : A → G) (d : A → H)
    (hd : ∀ a, φ (c a) = d a) :
    S.IsSolution (φ ∘ v) d ↔ S.IsSolution v c := by
  have hcd : φ ∘ c = d := funext hd
  rw [← hcd]
  exact S.isSolution_comp_iff_of_injective φ hφ v c

/-- In a free group, equations have empty reduced words and inequations have nonempty
reduced words. -/
theorem isSolution_iff_toWord {B : Type*} [DecidableEq B]
    (S : EqIneqSystem X A) (v : X → FreeGroup B) (c : A → FreeGroup B) :
    S.IsSolution v c ↔
      (∀ w ∈ S.eqs, (eval v c w).toWord = []) ∧
      (∀ w ∈ S.ineqs, (eval v c w).toWord ≠ []) := by
  simp only [IsSolution, FreeGroup.toWord_eq_nil_iff, ne_eq]

/-- A single variable inequation is satisfied exactly when that variable is nontrivial. -/
theorem isSolution_singleton_ineq_iff (x : X) (v : X → G) (c : A → G) :
    (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution v c ↔
      v x ≠ 1 := by
  simp [IsSolution]

example (x : X) (c : A → G) :
    ¬ (⟨[], [FreeGroup.of (Sum.inl x)]⟩ : EqIneqSystem X A).IsSolution
      (fun _ => (1 : G)) c := by
  simp [isSolution_singleton_ineq_iff]

open scoped commutatorElement
/-- A commutator equation and a single variable inequation say that the variables commute
and that the first is nontrivial. -/
theorem isSolution_commutator_ineq_iff (x y : X) (v : X → G) (c : A → G) :
    (⟨[⁅FreeGroup.of (Sum.inl x : X ⊕ A), FreeGroup.of (Sum.inl y : X ⊕ A)⁆],
      [FreeGroup.of (Sum.inl x : X ⊕ A)]⟩ : EqIneqSystem X A).IsSolution v c ↔
      Commute (v x) (v y) ∧ v x ≠ 1 := by
  simp [IsSolution, map_commutatorElement, commutatorElement_eq_one_iff_commute]

/-- In a free group on two generators, `x = a` and `y = a²` solve the commutator
equation with the inequation `x ≠ 1`. -/
example :
    (⟨[⁅FreeGroup.of (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2),
        FreeGroup.of (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)⁆],
      [FreeGroup.of (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)]⟩ :
      EqIneqSystem (Fin 2) (Fin 2)).IsSolution
      (fun i => if i = 0 then FreeGroup.of (0 : Fin 2) else FreeGroup.of (0 : Fin 2) ^ 2)
      FreeGroup.of := by
  simp [isSolution_commutator_ineq_iff, FreeGroup.of_ne_one]

end EqIneqSystem

end TauCeti
