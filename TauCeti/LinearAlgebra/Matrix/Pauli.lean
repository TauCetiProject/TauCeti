/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The Pauli matrices

The Pauli matrices

`σ₁ = !![0, 1; 1, 0]`, `σ₂ = !![0, -i; i, 0]`, `σ₃ = !![1, 0; 0, -1]`

form a real basis of the traceless Hermitian `2 × 2` complex matrices. This file packages them as
the real-linear **Pauli map** `TauCeti.pauli : ℝ³ → M₂(ℂ)`, `x ↦ x₀ σ₁ + x₁ σ₂ + x₂ σ₃`, which is
a linear isomorphism of `ℝ³` onto the traceless Hermitian matrices, with inverse
`TauCeti.pauliCoord` on that subspace.

The Pauli map turns the vector algebra of `ℝ³` into matrix multiplication:

`pauli x * pauli y = (x ⬝ᵥ y) • 1 + i • pauli (x ⨯₃ y)`.

Taking the trace, `tr (pauli x * pauli y) = 2 (x ⬝ᵥ y)`, so `σᵢ / √2` is an orthonormal basis of
the traceless Hermitian matrices for the real inner product `Re tr (A* B)`; taking the commutator,
`[pauli x, pauli y] = 2 i • pauli (x ⨯₃ y)`. These two identities are what make conjugation by a
unitary matrix act on `ℝ³` by a rotation (`TauCeti.RepresentationTheory.SU2.Adjoint`).

## Main definitions

* `TauCeti.pauli`: the Pauli map `x ↦ x₀ σ₁ + x₁ σ₂ + x₂ σ₃`.
* `TauCeti.pauliCoord`: the coordinates of a traceless Hermitian matrix in the Pauli basis.

## Main results

* `TauCeti.isHermitian_pauli` and `TauCeti.trace_pauli`: the Pauli map takes traceless Hermitian
  values.
* `TauCeti.pauli_pauliCoord` and `TauCeti.pauliCoord_pauli`: it is a bijection onto the traceless
  Hermitian matrices, and `TauCeti.exists_pauli_eq_iff` characterizes its range.
* `TauCeti.pauli_mul_pauli`: the product formula above.
* `TauCeti.trace_pauli_mul_pauli`: `tr (pauli x * pauli y) = 2 (x ⬝ᵥ y)`.
* `TauCeti.pauli_mul_sub_mul_pauli`: `[pauli x, pauli y] = 2 i • pauli (x ⨯₃ y)`.
* `TauCeti.det_pauli`: `det (pauli x) = -(x ⬝ᵥ x)`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics
  129, Springer, 1991, §7.3 (the double cover `SU(2) → SO(3)` through the traceless Hermitian
  matrices).
-/

public section

open Matrix Complex
open scoped ComplexConjugate

namespace TauCeti

/-- The **Pauli map** `x ↦ x₀ σ₁ + x₁ σ₂ + x₂ σ₃` from `ℝ³` to the `2 × 2` complex matrices, where
`σ₁ = !![0, 1; 1, 0]`, `σ₂ = !![0, -i; i, 0]` and `σ₃ = !![1, 0; 0, -1]` are the Pauli matrices.
It is a real-linear isomorphism onto the traceless Hermitian matrices (`TauCeti.pauli_pauliCoord`,
`TauCeti.pauliCoord_pauli`). -/
def pauli : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun x := !![(x 2 : ℂ), x 0 - x 1 * I; x 0 + x 1 * I, -(x 2 : ℂ)]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The entries of the Pauli map. -/
theorem pauli_apply (x : Fin 3 → ℝ) :
    pauli x = !![(x 2 : ℂ), x 0 - x 1 * I; x 0 + x 1 * I, -(x 2 : ℂ)] :=
  (rfl)

/-- The coordinates `(Re A₁₀, Im A₁₀, Re A₀₀)` of a `2 × 2` complex matrix `A`. On the traceless
Hermitian matrices these are the coordinates in the Pauli basis, so that
`pauli (pauliCoord A) = A` (`TauCeti.pauli_pauliCoord`); on other matrices they forget the
remaining entries. -/
def pauliCoord : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun A := ![(A 1 0).re, (A 1 0).im, (A 0 0).re]
  map_add' A B := by
    ext i
    fin_cases i <;> simp
  map_smul' c A := by
    ext i
    fin_cases i <;> simp

/-- The entries of `TauCeti.pauliCoord`. -/
theorem pauliCoord_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliCoord A = ![(A 1 0).re, (A 1 0).im, (A 0 0).re] :=
  (rfl)

/-- The Pauli coordinates of `pauli x` are `x`. -/
@[simp]
theorem pauliCoord_pauli (x : Fin 3 → ℝ) : pauliCoord (pauli x) = x := by
  ext i
  fin_cases i <;> simp [pauliCoord_apply, pauli_apply]

/-- The Pauli map is injective. -/
theorem pauli_injective : Function.Injective pauli :=
  Function.LeftInverse.injective pauliCoord_pauli

/-- The Pauli map takes Hermitian values. -/
theorem isHermitian_pauli (x : Fin 3 → ℝ) : (pauli x).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli_apply, Complex.ext_iff]

/-- The Pauli map takes traceless values. -/
@[simp]
theorem trace_pauli (x : Fin 3 → ℝ) : (pauli x).trace = 0 := by
  simp [pauli_apply, trace_fin_two]

/-- A traceless Hermitian `2 × 2` matrix is the image under the Pauli map of its Pauli
coordinates. -/
theorem pauli_pauliCoord {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian)
    (htr : A.trace = 0) : pauli (pauliCoord A) = A := by
  have h01 : A 0 1 = conj (A 1 0) := by simpa using (congrFun₂ hA 0 1).symm
  have h00 : (A 0 0).im = 0 := by
    have := congrArg Complex.im (congrFun₂ hA 0 0)
    simp only [conjTranspose_apply, star_def, conj_im] at this
    linarith
  have h11 : A 1 1 = -A 0 0 := by
    rw [trace_fin_two] at htr
    linear_combination htr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli_apply, pauliCoord_apply, Complex.ext_iff, h01, h11, h00]

/-- The range of the Pauli map is the traceless Hermitian matrices. -/
theorem exists_pauli_eq_iff {A : Matrix (Fin 2) (Fin 2) ℂ} :
    (∃ x, pauli x = A) ↔ A.IsHermitian ∧ A.trace = 0 := by
  refine ⟨?_, fun h => ⟨_, pauli_pauliCoord h.1 h.2⟩⟩
  rintro ⟨x, rfl⟩
  exact ⟨isHermitian_pauli x, trace_pauli x⟩

/-- The **product formula** of the Pauli map:
`pauli x * pauli y = (x ⬝ᵥ y) • 1 + i • pauli (x ⨯₃ y)`. -/
theorem pauli_mul_pauli (x y : Fin 3 → ℝ) :
    pauli x * pauli y = ((x ⬝ᵥ y : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      I • pauli (x ⨯₃ y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pauli_apply, cross_apply, dotProduct, Fin.sum_univ_three] <;> ring

/-- The square of `pauli x` is `x ⬝ᵥ x` times the identity. -/
theorem pauli_mul_self (x : Fin 3 → ℝ) :
    pauli x * pauli x = ((x ⬝ᵥ x : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pauli_mul_pauli, cross_self, map_zero, smul_zero, add_zero]

/-- The trace form of the Pauli map is twice the dot product: the matrices `σᵢ / √2` are
orthonormal for the real inner product `Re tr (A* B)` on the Hermitian matrices. -/
theorem trace_pauli_mul_pauli (x y : Fin 3 → ℝ) :
    (pauli x * pauli y).trace = 2 * ((x ⬝ᵥ y : ℝ) : ℂ) := by
  rw [pauli_mul_pauli, trace_add, trace_smul, trace_smul, trace_pauli, trace_one]
  simp [mul_comm]

/-- The commutator of two values of the Pauli map is `2 i` times the Pauli map of the cross
product. -/
theorem pauli_mul_sub_mul_pauli (x y : Fin 3 → ℝ) :
    pauli x * pauli y - pauli y * pauli x = (2 * I) • pauli (x ⨯₃ y) := by
  rw [pauli_mul_pauli, pauli_mul_pauli, dotProduct_comm y x, ← cross_anticomm, map_neg]
  module

/-- The determinant of `pauli x` is `-(x ⬝ᵥ x)`. -/
theorem det_pauli (x : Fin 3 → ℝ) : (pauli x).det = -((x ⬝ᵥ x : ℝ) : ℂ) := by
  simp only [pauli_apply, det_fin_two_of, dotProduct, Fin.sum_univ_three]
  push_cast
  linear_combination (x 1 : ℂ) ^ 2 * I_sq

end TauCeti
