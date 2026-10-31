/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic

/-!
# Coxeter elements of types `E₆`, `E₇`, `F₄`, `G₂`

The exceptional types other than `E₈`, using Mathlib's Cartan matrices (Bourbaki numbering). For
each type the Coxeter element `c = s₁ ⋯ sᵣ` has order the Coxeter number `h`, and its characteristic
polynomial is the product of the cyclotomic polynomials `Φ_d` over the orders `d = h / gcd(e, h)` of
the eigenvalues `exp (2πi e / h)`, `e` running over the exponents:

| type | `h` | exponents | characteristic polynomial |
|---|---|---|---|
| `E₆` | 12 | 1, 4, 5, 7, 8, 11 | `Φ₁₂ Φ₃` |
| `E₇` | 18 | 1, 5, 7, 9, 11, 13, 17 | `Φ₁₈ Φ₂` |
| `F₄` | 12 | 1, 5, 7, 11 | `Φ₁₂` |
| `G₂` | 6 | 1, 5 | `Φ₆` |
-/

@[expose] public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-! ### `E₆` -/

/-- The Coxeter element of type `E₆`. -/
def coxE6 : Matrix (Fin 6) (Fin 6) ℤ := coxeterElement (CartanMatrix.E 6)

theorem orderOf_coxE6 : orderOf coxE6 = 12 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem charpoly_coxE6 : coxE6.charpoly = cyclotomic 12 ℤ * cyclotomic 3 ℤ := by
  refine charpoly_eq_cyclotomic_mul _ (by norm_num) (by norm_num) (by norm_num) (by decide)
    ?_ ?_ ?_ <;>
  simp only [cyclotomic_twelve_int, cyclotomic_three, map_mul, map_add, map_sub, map_pow,
    aeval_X, map_one] <;>
  decide +kernel

/-! ### `E₇` -/

/-- The Coxeter element of type `E₇`. -/
def coxE7 : Matrix (Fin 7) (Fin 7) ℤ := coxeterElement (CartanMatrix.E 7)

theorem orderOf_coxE7 : orderOf coxE7 = 18 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem charpoly_coxE7 : coxE7.charpoly = cyclotomic 18 ℤ * cyclotomic 2 ℤ := by
  refine charpoly_eq_cyclotomic_mul _ (by norm_num) (by norm_num) (by norm_num) (by decide)
    ?_ ?_ ?_ <;>
  simp only [cyclotomic_eighteen_int, cyclotomic_two, map_mul, map_add, map_sub, map_pow,
    aeval_X, map_one] <;>
  decide +kernel

/-! ### `F₄` -/

/-- The Coxeter element of type `F₄`. -/
def coxF4 : Matrix (Fin 4) (Fin 4) ℤ := coxeterElement CartanMatrix.F₄

theorem orderOf_coxF4 : orderOf coxF4 = 12 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem charpoly_coxF4 : coxF4.charpoly = cyclotomic 12 ℤ := by
  refine charpoly_eq_cyclotomic _ (by norm_num) (by decide) ?_
  simp only [cyclotomic_twelve_int, map_add, map_sub, map_pow, aeval_X, map_one]
  decide +kernel

/-! ### `G₂` -/

/-- The Coxeter element of type `G₂`. -/
def coxG2 : Matrix (Fin 2) (Fin 2) ℤ := coxeterElement CartanMatrix.G₂

theorem orderOf_coxG2 : orderOf coxG2 = 6 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem charpoly_coxG2 : coxG2.charpoly = cyclotomic 6 ℤ := by
  refine charpoly_eq_cyclotomic _ (by norm_num) (by decide) ?_
  simp only [cyclotomic_six_int, map_add, map_sub, map_pow, aeval_X, map_one]
  decide +kernel

end TauCeti.Coxeter

end
