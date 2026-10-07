/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.ModelTheory.Order

/-!
# Terms of the language of ordered rings as polynomials

The first-order language of ordered rings is `Language.ring.sum Language.order`: the ring
operations `+`, `*`, `-`, `0`, `1` together with the single relation symbol `≤`. Its terms use
only the ring operations, so a term with variables in `α` is an integer polynomial in `α`.

This file defines that polynomial, `FirstOrder.Language.Term.toMvPolynomial`, with its equations
for variables and the ring operations, and proves:

* `FirstOrder.Language.Term.realize_eq_aeval_toMvPolynomial`: in a commutative ring whose ring
  symbols have their usual meaning (`FirstOrder.Ring.CompatibleRing`), realizing a term is
  evaluating its polynomial, and `FirstOrder.Language.Term.realize_eq_eval_map_toMvPolynomial`
  states the same with the polynomial mapped to `R`;
* `FirstOrder.Language.Term.toMvPolynomial_surjective`: every integer polynomial comes from a term;
* `MvPolynomial.exists_term_realize_eq_eval`: a polynomial with coefficients in `R` is realized by
  a term whose extra variables are assigned the coefficients, that is, by a term with parameters
  from `R`.

These are the term-level translation laws between formulas of ordered rings and polynomial sign
conditions, used to identify semialgebraic sets with quantifier-free definable sets.

## Implementation notes

The construction of a term realizing a given polynomial follows the corresponding construction
for `FreeCommRing` in Mathlib's `Mathlib/ModelTheory/Algebra/Ring/FreeCommRing.lean`, by Chris
Hughes.
-/

public section

open FirstOrder FirstOrder.Language MvPolynomial

namespace FirstOrder.Language.Term

variable {α β : Type*}

/-- The integer polynomial computed by a term of the language of ordered rings. -/
noncomputable def toMvPolynomial : (Language.ring.sum Language.order).Term α → MvPolynomial α ℤ
  | var a => X a
  | func (Sum.inl .add) ts => toMvPolynomial (ts 0) + toMvPolynomial (ts 1)
  | func (Sum.inl .mul) ts => toMvPolynomial (ts 0) * toMvPolynomial (ts 1)
  | func (Sum.inl .neg) ts => -toMvPolynomial (ts 0)
  | func (Sum.inl .zero) _ => 0
  | func (Sum.inl .one) _ => 1
  | func (Sum.inr f) _ => nomatch f

/-- The polynomial of a variable is that variable. -/
@[simp]
theorem toMvPolynomial_var (a : α) :
    (var a : (Language.ring.sum Language.order).Term α).toMvPolynomial = X a := by
  simp [toMvPolynomial]

/-- The polynomial of a sum of terms is the sum of their polynomials. -/
@[simp]
theorem toMvPolynomial_func_add (ts : Fin 2 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.addFunc) ts).toMvPolynomial =
      (ts 0).toMvPolynomial + (ts 1).toMvPolynomial := by
  simp [toMvPolynomial]

/-- The polynomial of a product of terms is the product of their polynomials. -/
@[simp]
theorem toMvPolynomial_func_mul (ts : Fin 2 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.mulFunc) ts).toMvPolynomial =
      (ts 0).toMvPolynomial * (ts 1).toMvPolynomial := by
  simp [toMvPolynomial]

/-- The polynomial of the negation of a term is the negation of its polynomial. -/
@[simp]
theorem toMvPolynomial_func_neg (ts : Fin 1 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.negFunc) ts).toMvPolynomial = -(ts 0).toMvPolynomial := by
  simp [toMvPolynomial]

/-- The polynomial of the constant `0` is `0`. -/
@[simp]
theorem toMvPolynomial_func_zero (ts : Fin 0 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.zeroFunc) ts).toMvPolynomial = 0 := by
  simp [toMvPolynomial]

/-- The polynomial of the constant `1` is `1`. -/
@[simp]
theorem toMvPolynomial_func_one (ts : Fin 0 → (Language.ring.sum Language.order).Term α) :
    (func (Sum.inl Ring.oneFunc) ts).toMvPolynomial = 1 := by
  simp [toMvPolynomial]

/-- Renaming the variables of a term renames the variables of its polynomial. -/
theorem toMvPolynomial_relabel (t : (Language.ring.sum Language.order).Term α) (g : α → β) :
    (t.relabel g).toMvPolynomial = rename g t.toMvPolynomial := by
  induction t with
  | var a => simp [Term.relabel]
  | func f ts ih =>
    rcases f with f | f
    · cases f <;> simp [Term.relabel, ih]
    · exact nomatch f

/-- Every integer polynomial is the polynomial of a term of the language of ordered rings. -/
theorem toMvPolynomial_surjective :
    Function.Surjective (toMvPolynomial : (Language.ring.sum Language.order).Term α → _) := by
  -- The polynomials of terms form a subring containing every variable.
  let S : Subring (MvPolynomial α ℤ) :=
    { carrier := Set.range toMvPolynomial
      add_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact ⟨func (Sum.inl Ring.addFunc) ![s, t], by simp⟩
      mul_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact ⟨func (Sum.inl Ring.mulFunc) ![s, t], by simp⟩
      neg_mem' := by
        rintro _ ⟨s, rfl⟩
        exact ⟨func (Sum.inl Ring.negFunc) ![s], by simp⟩
      zero_mem' := ⟨func (Sum.inl Ring.zeroFunc) ![], by simp⟩
      one_mem' := ⟨func (Sum.inl Ring.oneFunc) ![], by simp⟩ }
  intro p
  induction p using MvPolynomial.induction_on with
  | C n =>
    rw [eq_intCast]
    exact intCast_mem S n
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp => exact S.mul_mem hp ⟨var i, toMvPolynomial_var i⟩

variable {R : Type*} [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]

/-- In a commutative ring whose ring symbols have their usual meaning, realizing a term of the
language of ordered rings is evaluating its integer polynomial. -/
theorem realize_eq_aeval_toMvPolynomial (t : (Language.ring.sum Language.order).Term α)
    (v : α → R) : t.realize v = aeval v t.toMvPolynomial := by
  induction t with
  | var a => simp
  | func f ts ih =>
    rw [realize_func]
    rcases f with f | f
    · rw [funMap_sumInl]
      cases f <;> simp [ih]
    · exact nomatch f

/-- In a commutative ring whose ring symbols have their usual meaning, realizing a term of the
language of ordered rings is evaluating its integer polynomial mapped to `R`. -/
theorem realize_eq_eval_map_toMvPolynomial (t : (Language.ring.sum Language.order).Term α)
    (v : α → R) : t.realize v = eval v (t.toMvPolynomial.map (Int.castRingHom R)) := by
  rw [t.realize_eq_aeval_toMvPolynomial, aeval_eq_eval₂Hom, eval_map, algebraMap_int_eq,
    coe_eval₂Hom]

end FirstOrder.Language.Term

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]

/-- Every polynomial over `R` is realized by a term of the language of ordered rings with
parameters from `R`: the variables `Sum.inl r` of the term are assigned the values `r`. -/
theorem exists_term_realize_eq_eval (p : MvPolynomial σ R) :
    ∃ t : (Language.ring.sum Language.order).Term (R ⊕ σ),
      ∀ v : σ → R, t.realize (Sum.elim id v) = eval v p := by
  obtain ⟨q, hq⟩ : ∃ q : MvPolynomial (R ⊕ σ) ℤ, ∀ v : σ → R,
      aeval (Sum.elim id v) q = eval v p := by
    induction p using MvPolynomial.induction_on with
    | C a => exact ⟨X (Sum.inl a), by simp⟩
    | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      exact ⟨p' + q', by simp [hp', hq']⟩
    | mul_X p i hp =>
      obtain ⟨p', hp'⟩ := hp
      exact ⟨p' * X (Sum.inr i), by simp [hp']⟩
  obtain ⟨t, rfl⟩ := Term.toMvPolynomial_surjective q
  exact ⟨t, fun v => (t.realize_eq_aeval_toMvPolynomial _).trans (hq v)⟩

end MvPolynomial
