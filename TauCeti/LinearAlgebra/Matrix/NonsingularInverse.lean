/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The inverse of a matrix under a ring homomorphism

Applying a ring homomorphism `f : R →+* S` entrywise commutes with taking the inverse of a square
matrix, provided `f` is a local homomorphism (`Matrix.map_nonsing_inv`). The inverse
`A⁻¹ = Ring.inverse (det A) • adjugate A` is built from the determinant and the adjugate, which
commute with every ring homomorphism (`RingHom.map_det`, `RingHom.map_adjugate`), and a local
homomorphism commutes with `Ring.inverse` (`map_ringInverse`).

Locality is needed: `ℤ →+* ℚ` is not local, and the `1 × 1` matrix `2` over `ℤ` has inverse `0`,
while its image in `ℚ` has inverse `1 / 2`. Every ring homomorphism from a field to a nontrivial
ring is local, so the statement applies, for instance, to the casts `ℚ → ℝ` and `ℝ → ℂ`: an
inverse computed over `ℚ` is the inverse over `ℝ`.
-/

public section

namespace Matrix

variable {n R S F : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
  [FunLike F R S] [RingHomClass F R S]

/-- A local ring homomorphism applied entrywise commutes with the inverse of a square matrix. -/
@[simp]
theorem map_nonsing_inv (f : F) [IsLocalHom f] (A : Matrix n n R) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  have hdet : f A.det = (A.map f).det := RingHom.map_det (f : R →+* S) A
  have hadj : A.adjugate.map f = (A.map f).adjugate := RingHom.map_adjugate (f : R →+* S) A
  rw [inv_def, inv_def, ← hdet, ← hadj, ← map_ringInverse f]
  ext i j
  simp

end Matrix
