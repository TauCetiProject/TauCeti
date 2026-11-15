/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# The characteristic polynomial of a negated endomorphism

The characteristic polynomial of `-A` is that of `A` reflected through the origin:
`χ_{-A}(X) = (-1)ⁿ χ_A(-X)` for an `n × n` matrix, or an endomorphism of a free module of rank
`n` (`Matrix.charpoly_neg`, `LinearMap.charpoly_neg`). So an endomorphism with the same
characteristic polynomial as its negative, such as a skew-adjoint endomorphism for a
nondegenerate bilinear form, has `χ(-X) = (-1)ⁿ χ(X)`.
-/

public section

open Module Polynomial

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The characteristic polynomial of `-A` is `(-1)ⁿ χ_A(-X)`. -/
theorem charpoly_neg (A : Matrix n n R) :
    (-A).charpoly = (-1) ^ Fintype.card n * A.charpoly.comp (-X) := by
  have hmap : (compRingHom (-X : R[X])).mapMatrix A.charmatrix = -(-A).charmatrix := by
    refine Matrix.ext fun i j ↦ ?_
    by_cases hij : i = j
    · subst hij
      simp only [RingHom.mapMatrix_apply, map_apply, charmatrix_apply_eq, Matrix.neg_apply,
        coe_compRingHom_apply, sub_comp, X_comp, C_comp, map_neg]
      ring
    · simp [charmatrix_apply_ne _ _ _ hij]
  have hcomp : A.charpoly.comp (-X) = (-1) ^ Fintype.card n * (-A).charpoly := by
    rw [charpoly, ← coe_compRingHom_apply, RingHom.map_det, hmap, det_neg, charpoly]
  simp [hcomp, ← mul_assoc, ← mul_pow]

end Matrix

namespace LinearMap

/-- The characteristic polynomial of `-f` is `(-1)ⁿ χ_f(-X)` for an endomorphism of a free module
of rank `n`. -/
theorem charpoly_neg {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (f : Module.End R M) :
    (-f).charpoly = (-1) ^ finrank R M * f.charpoly.comp (-X) := by
  nontriviality R
  let b := Module.Free.chooseBasis R M
  rw [← charpoly_toMatrix f b, ← charpoly_toMatrix (-f) b, map_neg, Matrix.charpoly_neg,
    finrank_eq_card_chooseBasisIndex]

end LinearMap
