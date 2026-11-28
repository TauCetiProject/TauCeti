/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Column-replacement determinant and diagonal-update identities

For a square matrix `W : Matrix n n R` over a commutative ring `R`, replacing column `i` of the
identity matrix by a vector `a` yields a matrix of determinant `a i` (`TauCeti.det_updateCol_one`).
By Cramer's rule, if `W *ᵥ a = c • v` and `a i = 1`, then `W.det = c * (W.updateCol i v).det`
(`TauCeti.det_eq_mul_det_updateCol`). Moreover, if `a` is supported on indices where a diagonal
weight `d : n → R` agrees with `d i`, then right-multiplying `W * Matrix.diagonal d` by
`(1 : Matrix n n R).updateCol i a` replaces column `i` of `W` by `v` and scales `d i` by `t`
(`TauCeti.mul_diagonal_mul_updateCol_one`).

## Main results

* `TauCeti.det_updateCol_one`: `((1 : Matrix n n R).updateCol i a).det = a i`.
* `TauCeti.det_eq_mul_det_updateCol`: if `W *ᵥ a = c • v` and `a i = 1`, then
  `W.det = c * (W.updateCol i v).det`.
* `TauCeti.mul_diagonal_mul_updateCol_one`: column-replacement action on `W * Matrix.diagonal d`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/PadicHodge/Crystalline/HodgeTateJumps.lean`
(`Matrix.det_eq_mul_det_updateCol_of_mulVec_eq_smul_of_apply_eq_one`,
`New.Period.hodgeMatrix_mul_map_updateCol`).
-/

public section

open Matrix

namespace TauCeti

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Replacing column `i` of the identity matrix by `a` produces a matrix of determinant `a i`. -/
theorem det_updateCol_one (i : n) (a : n → R) :
    ((1 : Matrix n n R).updateCol i a).det = a i := by
  have hc : Matrix.cramer (1 : Matrix n n R) a i = ((1 : Matrix n n R).updateCol i a).det :=
    Matrix.cramer_apply 1 a i
  rw [← hc, Matrix.cramer_eq_adjugate_mulVec, Matrix.adjugate_one, Matrix.one_mulVec]

/-- Cramer's rule for one column: if `W *ᵥ a = c • v` and `a i = 1`, then
`W.det = c * (W.updateCol i v).det`. -/
theorem det_eq_mul_det_updateCol {W : Matrix n n R} {a v : n → R} {c : R} {i : n}
    (hW : W *ᵥ a = c • v) (ha : a i = 1) :
    W.det = c * (W.updateCol i v).det := by
  have hcramer : Matrix.cramer W (W *ᵥ a) = W.det • a := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  calc W.det = Matrix.cramer W (W *ᵥ a) i := by
        rw [hcramer, Pi.smul_apply, ha, smul_eq_mul, mul_one]
    _ = c * (W.updateCol i v).det := by
        rw [hW, map_smul, Pi.smul_apply, Matrix.cramer_apply, smul_eq_mul]

/-- If `a` is supported where `d x = d i` and `W *ᵥ a = t • v`, then right-multiplying
`W * Matrix.diagonal d` by `(1 : Matrix n n R).updateCol i a` replaces column `i` of `W` by `v`
and multiplies the `i`-th diagonal entry `d i` by `t`. -/
theorem mul_diagonal_mul_updateCol_one {W : Matrix n n R} {d a v : n → R} {t : R} {i : n}
    (hsupp : ∀ x : n, d x = d i ∨ a x = 0) (hW : W *ᵥ a = t • v) :
    (W * Matrix.diagonal d) * (1 : Matrix n n R).updateCol i a =
      W.updateCol i v * Matrix.diagonal (Function.update d i (d i * t)) := by
  ext m l
  by_cases hl : l = i
  · subst hl
    calc ((W * Matrix.diagonal d) * (1 : Matrix n n R).updateCol l a) m l
        = ∑ x, W m x * d x * a x := by
          simp [Matrix.mul_apply, Matrix.diagonal_apply]
      _ = ∑ x, d l * (W m x * a x) := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          obtain hx | hx := hsupp x
          · rw [hx]; ring
          · simp [hx]
      _ = d l * (t * v m) := by
          rw [← Finset.mul_sum]
          simpa [Matrix.mulVec, dotProduct] using congrArg (d l * ·) (congrFun hW m)
      _ = (W.updateCol l v * Matrix.diagonal (Function.update d l (d l * t))) m l := by
          simp [Matrix.mul_apply, Matrix.diagonal_apply]; ring
  · simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.updateCol_apply, hl, Matrix.one_apply]

end TauCeti
