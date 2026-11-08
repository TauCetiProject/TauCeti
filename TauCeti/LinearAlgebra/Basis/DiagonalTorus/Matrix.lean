/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

/-!
# Weight-homogeneous matrices and diagonal tori

A matrix supported on entries whose row and column weights differ by `α` intertwines the
diagonal weight-torus action with its rescaling by the character `α`. This entrywise criterion
works over any commutative ring, so it also applies to polynomial root-group coefficients over
nonreduced value algebras.
-/

public section

namespace Matrix

/-- A matrix supported in weight difference `α` intertwines the diagonal torus action with
its rescaling through `α`. -/
theorem diagonal_torusCharacter_mul_of_support
    {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommRing A]
    (X : Matrix ι ι A) (wt : ι → κ → ℤ) (α : κ → ℤ)
    (hX : ∀ a b, X a b ≠ 0 → wt a = α + wt b) (s : κ → Aˣ) :
    diagonal (fun a => (TauCeti.torusCharacter s (wt a) : A)) * X =
      ((TauCeti.torusCharacter s α : A) • X) *
        diagonal (fun a => (TauCeti.torusCharacter s (wt a) : A)) := by
  ext a b
  rw [diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hx : X a b = 0
  · simp only [hx, mul_zero, zero_mul]
  · rw [hX a b hx, TauCeti.torusCharacter_add, Units.val_mul]
    exact mul_right_comm _ _ _

end Matrix
