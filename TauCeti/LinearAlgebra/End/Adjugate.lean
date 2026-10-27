/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Trace
import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

/-!
# The adjugate of an endomorphism of a two-dimensional space

On a free module of rank two, the adjugate of an endomorphism `T` is `tr T • 1 - T`: in any basis
this is the matrix adjugate (`Matrix.adjugate_fin_two_eq_trace_smul_one_sub`). This file records
the two basis-free consequences of that identification: the adjugate reverses products, and
multiplying an endomorphism by its adjugate gives its determinant. Together they say that any map
which reverses products and sends each `T` to `tr T • 1 - T` on a set of generators turns
`T' T` into `det T`, which is how the determinant of a group acting on a two-dimensional space is
computed from a conjugation that reverses products.

## Main results

* `LinearMap.toMatrix_trace_smul_one_sub`: in every basis of a rank-two space, `tr T • 1 - T` is
  the matrix adjugate of `T`.
* `LinearMap.trace_mul_smul_one_sub_mul_of_finrank_eq_two`: the adjugate reverses products,
  `tr (S T) • 1 - S T = (tr T • 1 - T) (tr S • 1 - S)`.
* `LinearMap.trace_smul_one_sub_mul_self_of_finrank_eq_two`: `(tr T • 1 - T) T = det T • 1`.
-/

public section

namespace LinearMap

variable {K E : Type*}

section CommRing

variable [CommRing K] [AddCommGroup E] [Module K E]

/-- In rank two, the adjugate `T ↦ tr T • 1 - T` is the matrix adjugate in every basis. -/
theorem toMatrix_trace_smul_one_sub (b : Module.Basis (Fin 2) K E) (T : Module.End K E) :
    toMatrix b b (trace K E T • 1 - T) = (toMatrix b b T).adjugate := by
  rw [Matrix.adjugate_fin_two_eq_trace_smul_one_sub, map_sub, map_smul, toMatrix_one,
    trace_eq_matrix_trace K b]

end CommRing

section Field

variable [Field K] [AddCommGroup E] [Module K E]

/-- **The adjugate reverses products** on a two-dimensional space:
`tr (S T) • 1 - S T = (tr T • 1 - T) (tr S • 1 - S)`. -/
theorem trace_mul_smul_one_sub_mul_of_finrank_eq_two (h₂ : Module.finrank K E = 2)
    (S T : Module.End K E) :
    trace K E (S * T) • 1 - S * T = (trace K E T • 1 - T) * (trace K E S • 1 - S) := by
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ h₂
  let b := Module.finBasisOfFinrankEq K E h₂
  apply (toMatrix b b).injective
  rw [toMatrix_mul, toMatrix_trace_smul_one_sub, toMatrix_trace_smul_one_sub,
    toMatrix_trace_smul_one_sub, toMatrix_mul, Matrix.adjugate_mul_distrib]

/-- **An endomorphism times its adjugate is its determinant** on a two-dimensional space:
`(tr T • 1 - T) T = det T • 1`. -/
theorem trace_smul_one_sub_mul_self_of_finrank_eq_two (h₂ : Module.finrank K E = 2)
    (T : Module.End K E) :
    (trace K E T • 1 - T) * T = LinearMap.det T • 1 := by
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ h₂
  let b := Module.finBasisOfFinrankEq K E h₂
  apply (toMatrix b b).injective
  rw [toMatrix_mul, toMatrix_trace_smul_one_sub, Matrix.adjugate_mul, map_smul, toMatrix_one,
    det_toMatrix b]

end Field

end LinearMap
