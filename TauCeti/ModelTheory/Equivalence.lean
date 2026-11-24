/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Equivalence

/-!
# Equivalence of first-order formulas

Facts about equivalence of bounded formulas modulo a theory (`FirstOrder.Language.Theory.Iff`)
beyond those in Mathlib.

* Equivalence is a congruence for conjunction and disjunction:
  `FirstOrder.Language.Theory.Iff.inf` and `FirstOrder.Language.Theory.Iff.sup` complement
  Mathlib's `Theory.Iff.not`, `Theory.Iff.imp`, `Theory.Iff.all` and `Theory.Iff.ex`.
* The prenex rules: a quantifier in one conjunct or disjunct can be moved in front of the
  conjunction or disjunction, once the bound variables of the other side are shifted past the new
  one (`FirstOrder.Language.BoundedFormula.all_inf_iff_all_inf_liftAt` and its seven variants
  for `∃`, `⊔` and the right-hand side). These are the steps that bring a formula built from `⊓`,
  `⊔`, `∀` and `∃` into prenex form.
* A fictitious existential quantifier, binding a variable that does not occur, can be added in
  front of a formula (`FirstOrder.Language.BoundedFormula.iff_ex_liftAt`), as Mathlib's
  `FirstOrder.Language.BoundedFormula.iff_all_liftAt` does for the universal quantifier.
-/

public section

namespace FirstOrder.Language

variable {L : Language} {T : L.Theory} {α : Type*} {n : ℕ}

namespace Theory.Iff

variable {φ ψ φ' ψ' : L.BoundedFormula α n}

/-- Conjunctions of equivalent formulas are equivalent. -/
protected theorem inf (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') : (φ ⊓ φ') ⇔[T] (ψ ⊓ ψ') :=
  fun M v xs => by
    simp [BoundedFormula.realize_iff, h.realize_bd_iff (M := M), h'.realize_bd_iff (M := M)]

/-- Disjunctions of equivalent formulas are equivalent. -/
protected theorem sup (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') : (φ ⊔ φ') ⇔[T] (ψ ⊔ ψ') :=
  fun M v xs => by
    simp [BoundedFormula.realize_iff, h.realize_bd_iff (M := M), h'.realize_bd_iff (M := M)]

end Theory.Iff

namespace BoundedFormula

/-- A fictitious existential quantifier can be added in front of a formula. -/
theorem iff_ex_liftAt (φ : L.BoundedFormula α n) : φ ⇔[T] (φ.liftAt 1 n).ex :=
  fun M v xs => by simp

/-- A universal quantifier in the left conjunct can be moved in front of the conjunction. -/
theorem all_inf_iff_all_inf_liftAt (φ : L.BoundedFormula α (n + 1)) (ψ : L.BoundedFormula α n) :
    (φ.all ⊓ ψ) ⇔[T] (φ ⊓ ψ.liftAt 1 n).all :=
  fun M v xs => by simp [forall_and]

/-- An existential quantifier in the left conjunct can be moved in front of the conjunction. -/
theorem ex_inf_iff_ex_inf_liftAt (φ : L.BoundedFormula α (n + 1)) (ψ : L.BoundedFormula α n) :
    (φ.ex ⊓ ψ) ⇔[T] (φ ⊓ ψ.liftAt 1 n).ex :=
  fun M v xs => by simp

/-- A universal quantifier in the right conjunct can be moved in front of the conjunction. -/
theorem inf_all_iff_all_liftAt_inf (φ : L.BoundedFormula α n) (ψ : L.BoundedFormula α (n + 1)) :
    (φ ⊓ ψ.all) ⇔[T] (φ.liftAt 1 n ⊓ ψ).all :=
  fun M v xs => by simp [forall_and]

/-- An existential quantifier in the right conjunct can be moved in front of the conjunction. -/
theorem inf_ex_iff_ex_liftAt_inf (φ : L.BoundedFormula α n) (ψ : L.BoundedFormula α (n + 1)) :
    (φ ⊓ ψ.ex) ⇔[T] (φ.liftAt 1 n ⊓ ψ).ex :=
  fun M v xs => by simp

/-- A universal quantifier in the left disjunct can be moved in front of the disjunction. -/
theorem all_sup_iff_all_sup_liftAt (φ : L.BoundedFormula α (n + 1)) (ψ : L.BoundedFormula α n) :
    (φ.all ⊔ ψ) ⇔[T] (φ ⊔ ψ.liftAt 1 n).all :=
  fun M v xs => by simp [forall_or_right]

/-- An existential quantifier in the left disjunct can be moved in front of the disjunction. -/
theorem ex_sup_iff_ex_sup_liftAt (φ : L.BoundedFormula α (n + 1)) (ψ : L.BoundedFormula α n) :
    (φ.ex ⊔ ψ) ⇔[T] (φ ⊔ ψ.liftAt 1 n).ex :=
  fun M v xs => by simp [exists_or]

/-- A universal quantifier in the right disjunct can be moved in front of the disjunction. -/
theorem sup_all_iff_all_liftAt_sup (φ : L.BoundedFormula α n) (ψ : L.BoundedFormula α (n + 1)) :
    (φ ⊔ ψ.all) ⇔[T] (φ.liftAt 1 n ⊔ ψ).all :=
  fun M v xs => by simp [forall_or_left]

/-- An existential quantifier in the right disjunct can be moved in front of the disjunction. -/
theorem sup_ex_iff_ex_liftAt_sup (φ : L.BoundedFormula α n) (ψ : L.BoundedFormula α (n + 1)) :
    (φ ⊔ ψ.ex) ⇔[T] (φ.liftAt 1 n ⊔ ψ).ex :=
  fun M v xs => by simp [exists_or]

end BoundedFormula

end FirstOrder.Language
