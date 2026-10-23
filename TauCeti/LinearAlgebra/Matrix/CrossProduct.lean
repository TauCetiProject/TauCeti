/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
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

## Main results

* `Matrix.mulVec_cross_add_cross_mulVec`: the identity above.
* `Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero`: its trace-zero case.
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

end TauCeti
