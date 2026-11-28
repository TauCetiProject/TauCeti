/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic

/-!
# Total Chern polynomials of finite coefficient families

`TauCeti.chernPolynomial c` is the normalized polynomial `1 + c₁ t + ⋯ + cₐ tᵃ`.
Its coefficients vanish above `a`, and coefficient homomorphisms preserve this construction.
Products of these polynomials express the relations between elementary generators of
Grassmannian-type quotient algebras.
-/

public section

noncomputable section

namespace TauCeti

/-- The total Chern polynomial `1 + c₁ t + ⋯ + cₐ tᵃ` of a finite coefficient family. -/
def chernPolynomial {R : Type*} [Semiring R] {a : ℕ} (c : Fin a → R) : Polynomial R :=
  open scoped Classical in Polynomial.ofFn (a + 1) (Fin.cons 1 c)

/-- The constant coefficient of a total Chern polynomial is one. -/
@[simp] theorem chernPolynomial_coeff_zero {R : Type*} [Semiring R] {a : ℕ}
    (c : Fin a → R) : (chernPolynomial c).coeff 0 = 1 := by
  classical
  simp [chernPolynomial]

/-- The positive coefficients are the entries of the defining family. -/
@[simp] theorem chernPolynomial_coeff_succ {R : Type*} [Semiring R] {a : ℕ}
    (c : Fin a → R) (i : Fin a) : (chernPolynomial c).coeff (i.val + 1) = c i := by
  classical
  rw [chernPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)]
  exact (Fin.cons_succ (α := fun _ ↦ R) 1 c i)

/-- Coefficients past the last Chern class vanish. -/
theorem chernPolynomial_coeff_eq_zero {R : Type*} [Semiring R] {a : ℕ}
    (c : Fin a → R) {i : ℕ} (hi : a < i) : (chernPolynomial c).coeff i = 0 := by
  classical
  exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)

/-- The total Chern polynomial of an empty family is one. -/
@[simp] theorem chernPolynomial_fin_zero {R : Type*} [Semiring R] (c : Fin 0 → R) :
    chernPolynomial c = 1 := by
  ext i
  cases i with
  | zero => simp
  | succ i => simp [chernPolynomial_coeff_eq_zero _ (Nat.succ_pos i), Polynomial.coeff_one]

/-- A total Chern polynomial has degree at most the length of its coefficient family. -/
theorem natDegree_chernPolynomial_le {R : Type*} [Semiring R] {a : ℕ}
    (c : Fin a → R) : (chernPolynomial c).natDegree ≤ a :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun _ hi ↦ chernPolynomial_coeff_eq_zero c hi

/-- Total Chern polynomials commute with coefficient homomorphisms. -/
@[simp] theorem _root_.RingHom.map_chernPolynomial {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) {a : ℕ} (c : Fin a → R) :
    (chernPolynomial c).map f = chernPolynomial (fun i ↦ f (c i)) := by
  ext i
  rcases i with _ | i
  · simp
  · by_cases hi : i < a
    · rw [Polynomial.coeff_map, chernPolynomial_coeff_succ c ⟨i, hi⟩,
        chernPolynomial_coeff_succ _ ⟨i, hi⟩]
    · simp [Polynomial.coeff_map, chernPolynomial_coeff_eq_zero _ (by omega : a < i + 1)]

end TauCeti
