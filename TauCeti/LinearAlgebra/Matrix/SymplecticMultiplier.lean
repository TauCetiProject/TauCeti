/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant of a rank-two matrix from its symplectic multiplier

`Matrix.J l R` is the standard symplectic form on `l ⊕ l`, and `Matrix.symplecticGroup` collects
the matrices preserving it, `Aᵀ * J * A = J`. This file records what happens one step out, when
`A` merely *scales* the form: in the rank-two case — `l` a singleton — the scaling factor is
forced to be the determinant.

    Aᵀ * J l R * A = A.det • J l R,     and hence     Aᵀ * J l R * A = d • J l R ↔ A.det = d.

The second form, read left to right, is the useful one. A pairing on a rank-two module known to
scale by some quantity under a given endomorphism identifies that quantity as the determinant,
without computing it — and, since only the one endomorphism appears, without any additivity in it.

For larger `l` the corresponding conclusion is `A.det = d ^ Fintype.card l`, whose usual proof
goes through the Pfaffian; there is none in this Mathlib, and the cheap determinant argument
yields only `A.det ^ 2 = (d ^ Fintype.card l) ^ 2`, which is strictly weaker over a general
commutative ring. Only the rank-two case is proved here, that being the case in hand.

## Main results

* `Matrix.transpose_mul_J_mul_eq_det_smul`: `Aᵀ J A = det A • J`.
* `Matrix.transpose_mul_J_mul_eq_smul_iff`: the multiplier is the determinant.
* `Matrix.det_eq_of_symplectic_adjoint_of_mul_eq_smul_one`: the same, from an adjoint `B` with
  `Aᵀ J = J B` and `B A = d • 1`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/PairingDet.lean`, theorems `transpose_mul_symJ_mul`,
`det_eq_of_symplectic_adjoint` and `det_eq_of_symplectic_scaling`. The last is an implication in
the source and is stated here as an equivalence, the converse being immediate.

The source states them for a matrix of its own,
`symJ : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]`. That definition is **replaced** by Mathlib's
canonical `Matrix.J`, which the statements here are about, so nothing standing for `symJ` is
added. The two differ by a sign: `Matrix.J l R` is
`fromBlocks 0 (-1) 1 0`, which in rank two reads `!![0, -1; 1, 0]`. The identities are insensitive
to it, both sides being linear in the form.
The source's elliptic-curve reading — the scaling being the Weil pairing's
`e (A S) (A T) = e S T ^ deg A`, and the conclusion `det = deg` — is likewise not reproduced, no
curve occurring in any statement here.
-/

public section

namespace Matrix

variable {l R : Type*} [DecidableEq l] [Fintype l] [Unique l] [CommRing R]

/-- **A rank-two matrix scales the standard symplectic form by its determinant.** -/
@[simp]
theorem transpose_mul_J_mul_eq_det_smul (A : Matrix (l ⊕ l) (l ⊕ l) R) :
    Aᵀ * J l R * A = A.det • J l R := by
  ext (i | i) (j | j) <;>
    simp [det_sum_unique A, J, mul_apply, Unique.eq_default i, Unique.eq_default j] <;> ring

/-- **The symplectic multiplier of a rank-two matrix is its determinant.** `A` scales the standard
symplectic form by `d` exactly when `A.det = d`. Only `A` appears: no adjoint, and no additivity
in `A`. -/
theorem transpose_mul_J_mul_eq_smul_iff {A : Matrix (l ⊕ l) (l ⊕ l) R} {d : R} :
    Aᵀ * J l R * A = d • J l R ↔ A.det = d := by
  rw [transpose_mul_J_mul_eq_det_smul]
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  simpa [J] using congrFun₂ h (Sum.inr default) (Sum.inl default)

/-- **The determinant from a symplectic adjoint.** If `B` is adjoint to `A` for the form, meaning
`Aᵀ J = J B`, and `B A = d • 1`, then `det A = d`. -/
theorem det_eq_of_symplectic_adjoint_of_mul_eq_smul_one {A B : Matrix (l ⊕ l) (l ⊕ l) R} {d : R}
    (hadj : Aᵀ * J l R = J l R * B) (hBA : B * A = d • (1 : Matrix (l ⊕ l) (l ⊕ l) R)) :
    A.det = d :=
  transpose_mul_J_mul_eq_smul_iff.1 <| by rw [hadj, mul_assoc, hBA, Matrix.mul_smul, mul_one]

end Matrix
