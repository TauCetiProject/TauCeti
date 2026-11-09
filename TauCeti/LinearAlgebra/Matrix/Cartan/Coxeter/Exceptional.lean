/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclotomic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import TauCeti.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Coxeter elements of the exceptional types

The Coxeter element `c = s₁ ⋯ sᵣ` of each exceptional Cartan matrix, in the numbering of
`TauCeti.DynkinType.cartanMatrix`. It has order the Coxeter number `h`, and its characteristic
polynomial is the product of the cyclotomic polynomials `Φ_d` over the orders `d = h / gcd(e, h)` of
the eigenvalues `exp (2πi e / h)`, `e` running over the exponents:

| type | `h` | exponents | characteristic polynomial |
|---|---|---|---|
| `E₆` | 12 | 1, 4, 5, 7, 8, 11 | `Φ₁₂ Φ₃` |
| `E₇` | 18 | 1, 5, 7, 9, 11, 13, 17 | `Φ₁₈ Φ₂` |
| `E₈` | 30 | 1, 7, 11, 13, 17, 19, 23, 29 | `Φ₃₀` |
| `F₄` | 12 | 1, 5, 7, 11 | `Φ₁₂` |
| `G₂` | 6 | 1, 5 | `Φ₆` |

TauCeti's Cartan matrix of type `G₂` is the transpose of Mathlib's `CartanMatrix.G₂`, and that is
the matrix used here.

## Main results

* `TauCeti.Coxeter.orderOf_coxE8` (and `E7`, `E6`, `F4`, `G2`): the order of the Coxeter element.
* `TauCeti.Coxeter.charpoly_coxE8` (and `E7`, `E6`, `F4`, `G2`): its characteristic polynomial.
* `TauCeti.Coxeter.isOneDegenerateOrder_E8` (and `E7`, `E6`, `F4`, `G2`): a one-degenerate order
  of the Dynkin diagram.
-/

public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-! ### `E₆` -/

/-- The Coxeter element of type `E₆`. -/
@[expose] def coxE6 : Matrix (Fin 6) (Fin 6) ℤ := coxeterElement (CartanMatrix.E 6)

/-- **The Coxeter number of `E₆` is 12**: the Coxeter element has order exactly `12`. -/
theorem orderOf_coxE6 : orderOf coxE6 = 12 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

/-- The characteristic polynomial of the `E₆` Coxeter element is `Φ₁₂ Φ₃`. -/
theorem charpoly_coxE6 : coxE6.charpoly = cyclotomic 12 ℤ * cyclotomic 3 ℤ := by
  refine charpoly_eq_cyclotomic_mul (by norm_num) (by norm_num) (by norm_num)
    (by rw [Fintype.card_fin]; decide) ?_ ?_ ?_ <;>
  simp only [cyclotomic_twelve, cyclotomic_three, map_mul, map_add, map_sub, map_pow,
    aeval_X, map_one] <;>
  decide +kernel

/-! ### `E₇` -/

/-- The Coxeter element of type `E₇`. -/
@[expose] def coxE7 : Matrix (Fin 7) (Fin 7) ℤ := coxeterElement (CartanMatrix.E 7)

/-- **The Coxeter number of `E₇` is 18**: the Coxeter element has order exactly `18`. -/
theorem orderOf_coxE7 : orderOf coxE7 = 18 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

/-- The characteristic polynomial of the `E₇` Coxeter element is `Φ₁₈ Φ₂`. -/
theorem charpoly_coxE7 : coxE7.charpoly = cyclotomic 18 ℤ * cyclotomic 2 ℤ := by
  refine charpoly_eq_cyclotomic_mul (by norm_num) (by norm_num) (by norm_num)
    (by rw [Fintype.card_fin]; decide) ?_ ?_ ?_ <;>
  simp only [cyclotomic_eighteen, cyclotomic_two, map_mul, map_add, map_sub, map_pow,
    aeval_X, map_one] <;>
  decide +kernel

/-! ### `E₈` -/

/-- The Coxeter element of type `E₈`. -/
@[expose] def coxE8 : Matrix (Fin 8) (Fin 8) ℤ := coxeterElement (CartanMatrix.E 8)

/-- **The Coxeter number of `E₈` is 30**: the Coxeter element has order exactly `30`. -/
theorem orderOf_coxE8 : orderOf coxE8 = 30 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

/-- The characteristic polynomial of the `E₈` Coxeter element is `Φ₃₀`. -/
theorem charpoly_coxE8 : coxE8.charpoly = cyclotomic 30 ℤ := by
  refine charpoly_eq_cyclotomic (by norm_num) (by rw [Fintype.card_fin]; decide) ?_
  simp only [cyclotomic_thirty, map_add, map_sub, map_pow, aeval_X, map_one]
  decide +kernel

/-! ### `F₄` -/

/-- The Coxeter element of type `F₄`. -/
@[expose] def coxF4 : Matrix (Fin 4) (Fin 4) ℤ := coxeterElement CartanMatrix.F₄

/-- **The Coxeter number of `F₄` is 12**: the Coxeter element has order exactly `12`. -/
theorem orderOf_coxF4 : orderOf coxF4 = 12 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

/-- The characteristic polynomial of the `F₄` Coxeter element is `Φ₁₂`. -/
theorem charpoly_coxF4 : coxF4.charpoly = cyclotomic 12 ℤ := by
  refine charpoly_eq_cyclotomic (by norm_num) (by rw [Fintype.card_fin]; decide) ?_
  simp only [cyclotomic_twelve, map_add, map_sub, map_pow, aeval_X, map_one]
  decide +kernel

/-! ### `G₂` -/

/-- The Coxeter element of type `G₂`. -/
@[expose] def coxG2 : Matrix (Fin 2) (Fin 2) ℤ := coxeterElement CartanMatrix.G₂ᵀ

/-- **The Coxeter number of `G₂` is 6**: the Coxeter element has order exactly `6`. -/
theorem orderOf_coxG2 : orderOf coxG2 = 6 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

/-- The characteristic polynomial of the `G₂` Coxeter element is `Φ₆`. -/
theorem charpoly_coxG2 : coxG2.charpoly = cyclotomic 6 ℤ := by
  refine charpoly_eq_cyclotomic (by norm_num) (by rw [Fintype.card_fin]; decide) ?_
  simp only [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one]
  decide +kernel

/-! ### One-degenerate orders of the exceptional diagrams (Bourbaki numbering, from 0) -/

/-- A one-degenerate order of the Dynkin diagram of type `E₈`. -/
theorem isOneDegenerateOrder_E8 :
    List.IsOneDegenerateOrder (fun i j : Fin 8 => CartanMatrix.E 8 i j ≠ 0)
      [0, 2, 3, 1, 4, 5, 6, 7] :=
  ((((((((List.isOneDegenerateOrder_nil.append_singleton (z := 0) (by decide)).append_singleton
    (z := 2) (by decide)).append_singleton (z := 3) (by decide)).append_singleton (z := 1)
    (by decide)).append_singleton (z := 4) (by decide)).append_singleton (z := 5)
    (by decide)).append_singleton (z := 6) (by decide)).append_singleton (z := 7) (by decide))

/-- A one-degenerate order of the Dynkin diagram of type `E₇`. -/
theorem isOneDegenerateOrder_E7 :
    List.IsOneDegenerateOrder (fun i j : Fin 7 => CartanMatrix.E 7 i j ≠ 0)
      [0, 2, 3, 1, 4, 5, 6] :=
  (((((((List.isOneDegenerateOrder_nil.append_singleton (z := 0) (by decide)).append_singleton
    (z := 2) (by decide)).append_singleton (z := 3) (by decide)).append_singleton (z := 1)
    (by decide)).append_singleton (z := 4) (by decide)).append_singleton (z := 5)
    (by decide)).append_singleton (z := 6) (by decide))

/-- A one-degenerate order of the Dynkin diagram of type `E₆`. -/
theorem isOneDegenerateOrder_E6 :
    List.IsOneDegenerateOrder (fun i j : Fin 6 => CartanMatrix.E 6 i j ≠ 0)
      [0, 2, 3, 1, 4, 5] :=
  ((((((List.isOneDegenerateOrder_nil.append_singleton (z := 0) (by decide)).append_singleton
    (z := 2) (by decide)).append_singleton (z := 3) (by decide)).append_singleton (z := 1)
    (by decide)).append_singleton (z := 4) (by decide)).append_singleton (z := 5) (by decide))

/-- A one-degenerate order of the Dynkin diagram of type `F₄`. -/
theorem isOneDegenerateOrder_F4 :
    List.IsOneDegenerateOrder (fun i j : Fin 4 => CartanMatrix.F₄ i j ≠ 0) [0, 1, 2, 3] :=
  ((((List.isOneDegenerateOrder_nil.append_singleton (z := 0) (by decide)).append_singleton (z := 1)
    (by decide)).append_singleton (z := 2) (by decide)).append_singleton (z := 3) (by decide))

/-- A one-degenerate order of the Dynkin diagram of type `G₂`. -/
theorem isOneDegenerateOrder_G2 :
    List.IsOneDegenerateOrder (fun i j : Fin 2 => CartanMatrix.G₂ᵀ i j ≠ 0) [0, 1] :=
  (List.isOneDegenerateOrder_nil.append_singleton (z := 0) (by decide)).append_singleton
    (z := 1) (by decide)

end TauCeti.Coxeter

end
