/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut

/-!
# Examples for endomorphisms of matrix algebras over a local ring

These are examples for `AlgHom.exists_innerAut_eq_of_isLocalRing` in small dimensions and over
`ℤ₃`:

* for `d = 0` the only endomorphism is conjugation by the only element of `GL₀(R)`;
* for `d = 1` every endomorphism is the identity, as `M₁(R)` consists of scalars;
* over `ℤ₃`, conjugation by `!![1, 1; 0, 1]` sends `E₀₀` to `!![1, -1; 0, 0]`.
-/

public section

open Matrix Matrix.GeneralLinearGroup

namespace TauCeti.InnerAutExamples

variable {R : Type*} [CommRing R]

/-- For `d = 0` the only endomorphism of `M₀(R)` is conjugation by `1 ∈ GL₀(R)`. -/
example (σ : Matrix (Fin 0) (Fin 0) R →ₐ[R] Matrix (Fin 0) (Fin 0) R) :
    σ = (innerAut (1 : GL (Fin 0) R)).toAlgHom :=
  AlgHom.ext fun _ ↦ Subsingleton.elim _ _

/-- For `d = 1` every endomorphism of `M₁(R)` is the identity: every matrix is a scalar. -/
example (σ : Matrix (Fin 1) (Fin 1) R →ₐ[R] Matrix (Fin 1) (Fin 1) R) : σ = AlgHom.id R _ := by
  ext x : 1
  have hx : x = algebraMap R _ (x 0 0) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [algebraMap_eq_diagonal]
  rw [hx, AlgHom.commutes, AlgHom.id_apply]

/-- Over `ℤ₃`, conjugation by `!![1, 1; 0, 1]` sends `E₀₀` to `!![1, -1; 0, 0]`. -/
example : innerAut (upperRightHom (1 : ℤ_[3])) (single 0 0 1) = !![1, -1; 0, 0] := by
  have hE : (single 0 0 1 : Matrix (Fin 2) (Fin 2) ℤ_[3]) = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [innerAut_apply, upperRightHom_apply, Units.inv_mk, hE]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end TauCeti.InnerAutExamples
