/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Trace

import Mathlib.Tactic.FinCases

/-!
# Matrices acting on a cross product

A matrix `B` acting on `R³` does not commute with the cross product, but the failure is completely
described by the trace: differentiating the Cauchy--Binet formula
`(B u) ⨯₃ (B v) = (det B) • (B⁻¹)ᵀ (u ⨯₃ v)` at `B = 1` gives

`(B u) ⨯₃ v + u ⨯₃ (B v) = (tr B) • (u ⨯₃ v) - Bᵀ (u ⨯₃ v)`,

which is `TauCeti.mulVec_crossProduct_add`. Its traceless case
`TauCeti.transpose_mulVec_crossProduct` says that a traceless `B` acts on a cross product as minus
the transposed action on the factors; equivalently, `u ↦ B *ᵥ u` is a derivation of the Lie ring
`(R³, ⨯₃)` exactly when the transposed action is accounted for, which is what makes a traceless
`3 × 3` matrix act by a derivation on a Zorn vector matrix in
`TauCeti/Algebra/Octonion/Derivation.lean`.

Both identities are polynomial in the entries of `B`, `u` and `v`, and are proved by expanding the
three coordinates of each side.
-/

public section

namespace TauCeti

open Matrix

variable {R : Type*} [CommRing R]

/-- **The infinitesimal Cauchy--Binet relation**: differentiating
`(B u) ⨯₃ (B v) = (det B) • (B⁻¹)ᵀ (u ⨯₃ v)` at `B = 1` gives
`(B u) ⨯₃ v + u ⨯₃ (B v) = (tr B) • (u ⨯₃ v) - Bᵀ (u ⨯₃ v)`. Proved by expanding both sides in
coordinates. -/
theorem mulVec_crossProduct_add (B : Matrix (Fin 3) (Fin 3) R) (u v : Fin 3 → R) :
    (B *ᵥ u) ⨯₃ v + u ⨯₃ (B *ᵥ v) = B.trace • (u ⨯₃ v) - Bᵀ *ᵥ (u ⨯₃ v) := by
  ext i
  fin_cases i <;>
    (simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.trace, Matrix.diag]
     ring)

/-- The traceless case of `TauCeti.mulVec_crossProduct_add`: a traceless matrix acts on a cross
product as minus the transposed action on the factors. -/
theorem transpose_mulVec_crossProduct {B : Matrix (Fin 3) (Fin 3) R} (hB : B.trace = 0)
    (u v : Fin 3 → R) : Bᵀ *ᵥ (u ⨯₃ v) = -((B *ᵥ u) ⨯₃ v) - u ⨯₃ (B *ᵥ v) := by
  have h : -((B *ᵥ u) ⨯₃ v + u ⨯₃ (B *ᵥ v)) = Bᵀ *ᵥ (u ⨯₃ v) := by
    rw [mulVec_crossProduct_add, hB, zero_smul, zero_sub, neg_neg]
  rw [← h]
  abel

end TauCeti
