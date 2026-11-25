/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel

/-!
# Matrices over a forced unitization congruent to the identity

Let `A` be a possibly nonunital algebra over a commutative semiring `R`, and
`A⁺ = Unitization R A` its forced unitization. A square matrix `M` over `A⁺` splits entrywise into
a matrix of scalars `M.map fst` over `R` and a matrix of components `M.map snd` over `A`. When the
scalar part is the identity matrix, `M = 1 + x` for `x = M.map snd` read in `A ⊆ A⁺`, and these
matrices multiply through the quasi-product of `Mₙ(A)`:
`(1 + x) * (1 + y) = 1 + (y + x + x * y)`.

## Main results

* `Matrix.one_add_map_inr_map_snd`: a matrix with identity scalar part is `1 + x`.
* `Matrix.one_add_map_inr_mul_one_add_map_inr`: `(1 + x) * (1 + y) = 1 + (y + x + x * y)`.
* `Matrix.map_snd_mul_of_map_fst_eq_one`: the components in `A` of a product of matrices with
  identity scalar part form the quasi-product of their components.
* `Matrix.map_snd_add_map_snd_add_mul_eq_zero`: the components in `A` of mutually inverse
  matrices with identity scalar part are quasi-inverse.
-/

public section

open Unitization

namespace Matrix

variable {R A n : Type*} [CommSemiring R] [NonUnitalSemiring A] [DecidableEq n]

/-- A matrix over `A⁺` whose scalar part is the identity is `1 + x`, for `x` its matrix of
components in `A`. -/
theorem one_add_map_inr_map_snd {M : Matrix n n (Unitization R A)}
    (hM : M.map (fun x ↦ x.fst) = 1) :
    1 + (M.map fun x ↦ x.snd).map ((↑) : A → Unitization R A) = M := by
  ext i j : 1
  have h := congr_fun₂ hM i j
  simp only [map_apply, Matrix.one_apply] at h
  refine Unitization.ext ?_ ?_ <;> by_cases hij : i = j <;> simp_all

/-- The scalar part of `1 + x`, for a matrix `x` over `A`, is the identity matrix. -/
@[simp]
theorem map_fst_one_add_map_inr (x : Matrix n n A) :
    (1 + x.map ((↑) : A → Unitization R A)).map (fun x ↦ x.fst) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- The matrix of components in `A` of `1 + x`, for a matrix `x` over `A`, is `x`. -/
@[simp]
theorem map_snd_one_add_map_inr (x : Matrix n n A) :
    (1 + x.map ((↑) : A → Unitization R A)).map (fun x ↦ x.snd) = x := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- The identity matrix over `A⁺` has zero components in `A`. -/
@[simp]
theorem map_snd_one : (1 : Matrix n n (Unitization R A)).map (fun x ↦ x.snd) = 0 := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

variable [Fintype n] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- The product of `1 + x` and `1 + y`, for matrices `x` and `y` over `A`, is
`1 + (y + x + x * y)`, with the quasi-product of `x` and `y`. -/
theorem one_add_map_inr_mul_one_add_map_inr (x y : Matrix n n A) :
    (1 + x.map ((↑) : A → Unitization R A)) * (1 + y.map (↑)) =
      1 + (y + x + x * y).map (↑) := by
  -- `Matrix.map_mul` for `inrNonUnitalAlgHom R A`, whose underlying function is `inr` by
  -- definition (Mathlib states no `coe_inrNonUnitalAlgHom` lemma).
  have hmul : x.map ((↑) : A → Unitization R A) * y.map (↑) = (x * y).map (↑) :=
    (Matrix.map_mul (L := x) (M := y) (f := inrNonUnitalAlgHom R A)).symm
  rw [Matrix.map_add _ (inr_add R), Matrix.map_add _ (inr_add R), ← hmul]
  simp only [mul_add, add_mul, one_mul, mul_one]
  abel

/-- The components in `A` of a product of matrices with identity scalar part form the
quasi-product of the components. -/
theorem map_snd_mul_of_map_fst_eq_one {M N : Matrix n n (Unitization R A)}
    (hM : M.map (fun x ↦ x.fst) = 1) (hN : N.map (fun x ↦ x.fst) = 1) :
    (M * N).map (fun x ↦ x.snd) =
      N.map (fun x ↦ x.snd) + M.map (fun x ↦ x.snd) +
        M.map (fun x ↦ x.snd) * N.map (fun x ↦ x.snd) := by
  conv_lhs => rw [← one_add_map_inr_map_snd hM, ← one_add_map_inr_map_snd hN]
  rw [one_add_map_inr_mul_one_add_map_inr, map_snd_one_add_map_inr]

/-- If `M * N = 1` for matrices with identity scalar part, their components in `A` are
quasi-inverse: `y + x + x * y = 0` for `x = M.map snd` and `y = N.map snd`. -/
theorem map_snd_add_map_snd_add_mul_eq_zero {M N : Matrix n n (Unitization R A)}
    (hM : M.map (fun x ↦ x.fst) = 1) (hN : N.map (fun x ↦ x.fst) = 1) (hMN : M * N = 1) :
    N.map (fun x ↦ x.snd) + M.map (fun x ↦ x.snd) +
      M.map (fun x ↦ x.snd) * N.map (fun x ↦ x.snd) = 0 := by
  rw [← map_snd_mul_of_map_fst_eq_one hM hN, hMN, map_snd_one]

end Matrix
