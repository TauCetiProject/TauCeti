/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Translates of rows and columns under a matrix representation

A group homomorphism `π : G →* GL n k` moves a column `z` to `π(a) z` and a row `x` to
`x π(a)⁻¹`. Two translates of a column agree exactly when `π(a⁻¹ b)` fixes the column, and two
translates of a row agree exactly when `π(a⁻¹ b)` fixes the row; so the translates of a vector are
indexed by the cosets of its stabiliser.

## Main results

* `MonoidHom.val_map_mul`: for `π : G →* Mˣ`, `π (g * h) = π g * π h` in `M`.
* `MonoidHom.vecMul_inv_eq_vecMul_inv_iff`: `x π(a)⁻¹ = x π(b)⁻¹ ↔ x π(a⁻¹ b) = x`.
* `MonoidHom.mulVec_eq_mulVec_iff`: `π(a) z = π(b) z ↔ π(a⁻¹ b) z = z`.
-/

public section

open Matrix

namespace MonoidHom

variable {G : Type*} [Group G]

/-- The value of a homomorphism into the units of `M` at a product is the product in `M`. -/
theorem val_map_mul {M : Type*} [Monoid M] (π : G →* Mˣ) (g h : G) :
    ((π (g * h) : Mˣ) : M) = π g * π h := by
  rw [map_mul, Units.val_mul]

variable {n k : Type*} [Fintype n] [DecidableEq n] [CommRing k]

/-- The translates `x π(a)⁻¹` of a row agree exactly when `π(a⁻¹ b)` fixes the row. -/
theorem vecMul_inv_eq_vecMul_inv_iff (π : G →* GL n k) (x : n → k) (a b : G) :
    x ᵥ* (π a⁻¹ : Matrix n n k) = x ᵥ* (π b⁻¹ : Matrix n n k) ↔
      x ᵥ* (π (a⁻¹ * b) : Matrix n n k) = x := by
  have hvm (v : n → k) (g h : G) :
      v ᵥ* (π g : Matrix n n k) ᵥ* (π h : Matrix n n k) = v ᵥ* (π (g * h) : Matrix n n k) := by
    rw [vecMul_vecMul, π.val_map_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [hvm] using congrArg (· ᵥ* (π b : Matrix n n k)) h
  · simpa [hvm, h] using congrArg (· ᵥ* (π b⁻¹ : Matrix n n k)) h

/-- The translates `π(a) z` of a column agree exactly when `π(a⁻¹ b)` fixes the column. -/
theorem mulVec_eq_mulVec_iff (π : G →* GL n k) (z : n → k) (a b : G) :
    (π a : Matrix n n k) *ᵥ z = (π b : Matrix n n k) *ᵥ z ↔
      (π (a⁻¹ * b) : Matrix n n k) *ᵥ z = z := by
  have hmv (v : n → k) (g h : G) :
      (π g : Matrix n n k) *ᵥ (π h : Matrix n n k) *ᵥ v = (π (g * h) : Matrix n n k) *ᵥ v := by
    rw [mulVec_mulVec, π.val_map_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [hmv] using (congrArg ((π a⁻¹ : Matrix n n k) *ᵥ ·) h).symm
  · simpa [hmv, h] using (congrArg ((π a : Matrix n n k) *ᵥ ·) h).symm

end MonoidHom
