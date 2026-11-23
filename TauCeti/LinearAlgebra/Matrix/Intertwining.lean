/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Matrices intertwined by a rectangular matrix

Let `E : Matrix m n R` intertwine square matrices `A` and `B`, that is `E * A = B * E`. When `E` is
square this is `SemiconjBy E A B`, and `SemiconjBy.pow_right` carries it to all powers. Here `E`
may be rectangular, as for the embedding of the root lattice of type `Aₙ` into `ℤⁿ⁺¹`.

* `Matrix.mul_prod_map_eq_prod_map_mul`: if `E * f i = g i * E` for every `i`, then `E`
  intertwines the products `(l.map f).prod` and `(l.map g).prod` of any word `l`.
* `Matrix.mul_pow_eq_pow_mul_of_mul_eq_mul`: `E * A ^ k = B ^ k * E`.
* `Matrix.orderOf_eq_orderOf_of_mul_eq_mul`: if moreover `E * A ^ k = E` forces `A ^ k = 1` and
  `B ^ k * E = E` forces `B ^ k = 1`, then `A` and `B` have the same order.
* `Matrix.orderOf_eq_orderOf_of_isLeftRegular`: the square case, where it suffices that `E` can be
  cancelled on the left (over a commutative ring it can then be cancelled on the right too).
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Semiring R]
  {E : Matrix m n R} {A : Matrix n n R} {B : Matrix m m R}

/-- Letterwise intertwinings `E * f i = g i * E` pass to the products of a word. -/
theorem mul_prod_map_eq_prod_map_mul {ι : Type*} {f : ι → Matrix n n R}
    {g : ι → Matrix m m R} (h : ∀ i, E * f i = g i * E) (l : List ι) :
    E * (l.map f).prod = (l.map g).prod * E := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, h]
    simp only [Matrix.mul_assoc, ih]

/-- An intertwining `E * A = B * E` passes to powers. -/
theorem mul_pow_eq_pow_mul_of_mul_eq_mul (h : E * A = B * E) (k : ℕ) : E * A ^ k = B ^ k * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, ← Matrix.mul_assoc, ih]
    simp only [Matrix.mul_assoc, h]

/-- **Intertwined matrices have the same order**, as long as the intertwiner detects the powers
of each of them that are the identity. -/
theorem orderOf_eq_orderOf_of_mul_eq_mul (h : E * A = B * E)
    (hA : ∀ k : ℕ, E * A ^ k = E → A ^ k = 1) (hB : ∀ k : ℕ, B ^ k * E = E → B ^ k = 1) :
    orderOf A = orderOf B :=
  orderOf_eq_orderOf_iff.2 fun k =>
    ⟨fun hk => hB k (by rw [← mul_pow_eq_pow_mul_of_mul_eq_mul h, hk, Matrix.mul_one]),
      fun hk => hA k (by rw [mul_pow_eq_pow_mul_of_mul_eq_mul h, hk, Matrix.one_mul])⟩

/-- **Matrices intertwined by a left-cancellable square matrix have the same order.** Over a
commutative ring, `E` can then also be cancelled on the right
(`Matrix.isLeftRegular_iff_isRightRegular`). -/
theorem orderOf_eq_orderOf_of_isLeftRegular {S : Type*} [CommRing S] {E A B : Matrix n n S}
    (h : E * A = B * E) (hE : IsLeftRegular E) : orderOf A = orderOf B :=
  orderOf_eq_orderOf_of_mul_eq_mul h (fun _ hk => hE (hk.trans (Matrix.mul_one _).symm))
    fun _ hk => isLeftRegular_iff_isRightRegular.mp hE (hk.trans (Matrix.one_mul _).symm)

end Matrix

end
