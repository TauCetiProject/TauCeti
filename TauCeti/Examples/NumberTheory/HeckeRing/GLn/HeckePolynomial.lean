/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.HeckePolynomial
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Examples of the integral Hecke polynomial of `GL_n`

Concrete computations pinning down the normalization of `TauCeti.glnHeckePolynomial`:

* In ranks `0`, `1` and `2` with explicit operators, `P` is `1`, `X - 3` and `X² - 3X + 10`.
  The rank-one case carries no power of `q`, and the rank-two constant term is `q T_2`.
* Over `ZMod 2` with `q = 0` and `T = (1, 1, 1)` the polynomial is `X² + X`, and in rank zero
  with `T_0 = 0` over `ℤ` it is not monic.
* The Satake values `s = 2`, `z = (3, 5)` give `(X - 6)(X - 10) = X² - 16X + 60`, with constant
  term `60`, not `-60`.
* The inversion `T'_i = T_{2-i} / T_2` at `q = 2`, `T = (1, 5, 3)` turns `X² - 5X + 6` into
  `X² - (5/3)X + 2/3`.
-/

public section

open Polynomial TauCeti

-- Rank zero with `q = 0` and `T₀ = 1` is the constant `1`.
example : glnHeckePolynomial 0 (0 : ℤ) ![1] = 1 := by
  simp [glnHeckePolynomial_zero]

-- Rank one: `X - T₁`, with no power of `q` on the single nontrivial coefficient.
example : glnHeckePolynomial 1 (7 : ℤ) ![1, 3] = X - C 3 := by
  simp [glnHeckePolynomial_one]

-- Rank two: `X² - T₁X + qT₂`.
example : glnHeckePolynomial 2 (2 : ℤ) ![1, 3, 5] = X ^ 2 - C 3 * X + C 10 := by
  rw [glnHeckePolynomial_two]
  norm_num

-- The polynomial is integral in `q`: over `ZMod 2` with `q = 0` and `T = (1, 1, 1)`,
-- it is `X² + X`.
example : glnHeckePolynomial 2 (0 : ZMod 2) ![1, 1, 1] = X ^ 2 + X := by
  rw [glnHeckePolynomial_two]
  simp [CharTwo.sub_eq_add]

-- In rank zero with `T₀ = 0` over `ℤ` the polynomial is `0`, which is not monic.
example : ¬ (glnHeckePolynomial 0 (1 : ℤ) ![0]).Monic := by
  simp [glnHeckePolynomial_zero, Monic]

-- Satake: `s = 2`, `z = (3, 5)` gives `(X - 6)(X - 10)`, so `X² - 16X + 60`.
example : glnHeckePolynomial 2 (2 ^ 2 : ℤ)
    (fun i => 2 ^ ((i : ℕ) * (2 - i)) * (Finset.univ.val.map ![3, 5]).esymm i) =
      X ^ 2 - C 16 * X + C 60 := by
  rw [glnHeckePolynomial_pow_mul_esymm, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  ring

-- Inversion at `q = 2`, `T = (1, 5, 3)`: `P = X² - 5X + 6` has roots `2, 3`, and the generators
-- `T'_i = T_{2-i} / T_2 = (1, 5/3, 1/3)` satisfy the hypothesis of the inversion identity.
example : glnHeckePolynomial 2 (2 : ℚ) ![1, 5, 3] = X ^ 2 - C 5 * X + C 6 := by
  rw [glnHeckePolynomial_two]
  norm_num

example : ∀ i : Fin 3,
    (![1, 5 / 3, 1 / 3] : Fin 3 → ℚ) i * (![1, 5, 3] : Fin 3 → ℚ) (Fin.last 2) =
      (![1, 5, 3] : Fin 3 → ℚ) i.rev := by
  decide +kernel

-- The inverted polynomial is `X² - (5/3)X + 2/3 = (X - 1)(X - 2/3)`: its roots are `q / β`
-- for the roots `β = 2, 3` of `P`.
example : glnHeckePolynomial 2 (2 : ℚ) ![1, 5 / 3, 1 / 3] = (X - C 1) * (X - C (2 / 3)) := by
  have h : (X - C 1) * (X - C (2 / 3)) =
      C 1 * X ^ 2 - C (1 + 2 / 3) * X + C (1 * (2 / 3) : ℚ) := by
    rw [C_add, C_mul, C_1]
    ring
  rw [glnHeckePolynomial_two, h]
  norm_num
