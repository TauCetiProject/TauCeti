/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# How a matrix interacts with the cross product

A `3 × 3` matrix `M` acts on `R³`, and the cross product is a bilinear map `R³ × R³ → R³`, so one
may ask how the two compose. The answer is the infinitesimal form of the Cauchy--Binet identity
`(M u) ⨯₃ (M w) = (adj M)ᵀ (u ⨯₃ w)`: replacing `M` by `1 + ε M` and reading off the linear term in
`ε`,

`(M u) ⨯₃ w + u ⨯₃ (M w) = (tr M) • (u ⨯₃ w) - Mᵀ (u ⨯₃ w)`.

So the cross product is *not* preserved by an arbitrary matrix, but a trace-zero matrix acts on it
as a derivation with `-Mᵀ` in the target slot, which is the form the identity is used in.

The **hat map** `u ↦ û` (`TauCeti.crossProductMatrix`) sends `u` to the matrix of the linear map
`v ↦ u ⨯₃ v`. The matrix `û` is skew-symmetric, and the commutator of two such matrices is the
matrix of the cross product of their vectors: `[û, v̂] = (u ⨯₃ v)^`.

## Main definitions

* `TauCeti.crossProductMatrix R`: the hat map `u ↦ û`, the matrix of `v ↦ u ⨯₃ v`.

## Main results

* `Matrix.mulVec_cross_add_cross_mulVec`: the identity above.
* `Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero`: its trace-zero case.
* `TauCeti.transpose_crossProductMatrix`: the matrix `û` is skew-symmetric.
* `TauCeti.crossProductMatrix_cross`: `(u ⨯₃ v)^ = û v̂ - v̂ û`.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **A matrix acting on a cross product.** Applying `M` to one factor at a time and adding gives
the trace of `M` times the cross product, corrected by `-Mᵀ` applied to it. This is the derivative
at the identity of the Cauchy--Binet identity `(M u) ⨯₃ (M w) = (adj M)ᵀ (u ⨯₃ w)`. -/
theorem _root_.Matrix.mulVec_cross_add_cross_mulVec (M : Matrix (Fin 3) (Fin 3) R)
    (u w : Fin 3 → R) :
    (M *ᵥ u) ⨯₃ w + u ⨯₃ (M *ᵥ w) = M.trace • (u ⨯₃ w) - Mᵀ *ᵥ (u ⨯₃ w) := by
  ext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, vec3_dotProduct, Matrix.transpose_apply,
      Matrix.trace_fin_three, Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- **A trace-zero matrix acts on the cross product as a derivation**, with the transpose acting on
the target: `(M u) ⨯₃ w + u ⨯₃ (M w) = -(Mᵀ (u ⨯₃ w))`. -/
theorem _root_.Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero
    (M : Matrix (Fin 3) (Fin 3) R) (hM : M.trace = 0) (u w : Fin 3 → R) :
    (M *ᵥ u) ⨯₃ w + u ⨯₃ (M *ᵥ w) = -(Mᵀ *ᵥ (u ⨯₃ w)) := by
  rw [Matrix.mulVec_cross_add_cross_mulVec, hM, zero_smul, zero_sub]

/-! ### The hat map -/

variable (R) in
/-- The **hat map** `u ↦ û`, sending `u` to the matrix of the linear map `v ↦ u ⨯₃ v`
(`TauCeti.crossProductMatrix_mulVec`). -/
def crossProductMatrix : (Fin 3 → R) →ₗ[R] Matrix (Fin 3) (Fin 3) R :=
  LinearMap.toMatrix'.toLinearMap ∘ₗ crossProduct

/-- The matrix `û` acts on vectors by the cross product with `u`. -/
@[simp]
theorem crossProductMatrix_mulVec (u v : Fin 3 → R) :
    crossProductMatrix R u *ᵥ v = u ⨯₃ v :=
  LinearMap.toMatrix'_mulVec _ v

/-- The entries of `û`. -/
theorem crossProductMatrix_apply (u : Fin 3 → R) :
    crossProductMatrix R u = !![0, -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossProductMatrix, LinearMap.toMatrix'_apply, cross_apply]

/-- The matrix `û` is skew-symmetric. -/
@[simp]
theorem transpose_crossProductMatrix (u : Fin 3 → R) :
    (crossProductMatrix R u)ᵀ = -crossProductMatrix R u := by
  rw [crossProductMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The hat map is a Lie algebra homomorphism.** The matrix of `u ⨯₃ v` is the commutator of the
matrices of `u` and `v`; this is the Jacobi identity of the cross product. -/
theorem crossProductMatrix_cross (u v : Fin 3 → R) :
    crossProductMatrix R (u ⨯₃ v) = crossProductMatrix R u * crossProductMatrix R v -
      crossProductMatrix R v * crossProductMatrix R u := by
  refine Matrix.toLin'.injective (LinearMap.ext fun w ↦ ?_)
  simp only [toLin'_apply, sub_mulVec, ← mulVec_mulVec, crossProductMatrix_mulVec, cross_cross]

end TauCeti
