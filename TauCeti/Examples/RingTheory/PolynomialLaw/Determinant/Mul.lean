/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.PolynomialLaw.Determinant.Mul
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Tactic.Ring

/-!
# Examples: direct sums of determinants

* Two copies of the identity character of `ℤ` at `3` give value `9`, characteristic polynomial
  `X² − 6X + 9` and trace `6`.
* The two projections `ℤ × ℤ → ℤ` at `(0, 3)` give value `0`, characteristic polynomial
  `X² − 3X` and trace `3`.
* Traces add, and multiplying by the determinant of dimension zero changes nothing.
-/

open TauCeti Determinant Polynomial

-- Two copies of the identity character of `ℤ` at `3`: value `9` ...
example : (algHomPow (AlgHom.id ℤ ℤ) 1).mul (algHomPow (AlgHom.id ℤ ℤ) 1) 3 = 9 := by
  simp

-- ... characteristic polynomial `X² − 6X + 9` ...
example : ((algHomPow (AlgHom.id ℤ ℤ) 1).mul (algHomPow (AlgHom.id ℤ ℤ) 1)).charpoly 3 =
    X ^ 2 - C 6 * X + C 9 := by
  simp only [charpoly_mul, charpoly_algHomPow, pow_one, map_ofNat]
  ring

-- ... and trace `6`.
example : ((algHomPow (AlgHom.id ℤ ℤ) 1).mul (algHomPow (AlgHom.id ℤ ℤ) 1)).trace 3 = 6 := by
  simp

-- The two projections `ℤ × ℤ → ℤ` at `(0, 3)`: value `0` ...
example : (algHomPow (AlgHom.fst ℤ ℤ ℤ) 1).mul (algHomPow (AlgHom.snd ℤ ℤ ℤ) 1) (0, 3) = 0 := by
  simp

-- ... characteristic polynomial `X² − 3X` ...
example : ((algHomPow (AlgHom.fst ℤ ℤ ℤ) 1).mul (algHomPow (AlgHom.snd ℤ ℤ ℤ) 1)).charpoly (0, 3) =
    X ^ 2 - C 3 * X := by
  simp only [charpoly_mul, charpoly_algHomPow, AlgHom.fst_apply, AlgHom.snd_apply, pow_one,
    map_zero, sub_zero, map_ofNat]
  ring

-- ... and trace `3`.
example : ((algHomPow (AlgHom.fst ℤ ℤ ℤ) 1).mul (algHomPow (AlgHom.snd ℤ ℤ ℤ) 1)).trace (0, 3) =
    3 := by
  simp

-- Traces add.
example {A R : Type*} [CommRing A] [Ring R] [Algebra A R] {d₁ d₂ : ℕ} (D₁ : Determinant A R d₁)
    (D₂ : Determinant A R d₂) (x : R) : (D₁.mul D₂).trace x = D₁.trace x + D₂.trace x :=
  trace_mul D₁ D₂ x

-- Multiplying by the determinant of dimension zero changes neither the law nor the value.
example {A R : Type*} [CommRing A] [Ring R] [Algebra A R] {d : ℕ} (D : Determinant A R d)
    (x : R) : (D.mul (default : Determinant A R 0)).toLaw = D.toLaw ∧
      D.mul (default : Determinant A R 0) x = D x :=
  ⟨toLaw_mul_default D, by simp⟩
