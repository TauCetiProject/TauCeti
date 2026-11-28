/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Tactic.Abel
import TauCeti.LinearAlgebra.Matrix.Determinant.Pencil

/-!
# The shifted determinant polynomial `det ((1 + X) • A - 1)`

For a square matrix `A : Matrix n n R` over a commutative ring `R`, `TauCeti.shiftedDet A` is the
polynomial `det ((1 + X) • A.map C - 1) : R[X]`. Its evaluation along any ring homomorphism
`e : R →+* S` at `y : S` is `((1 + y) • A.map e - 1).det` (`TauCeti.eval₂_shiftedDet`), its
constant term is `(A - 1).det` (`TauCeti.eval_shiftedDet_zero`), and its coefficient of degree
`Fintype.card n` is `A.det` (`TauCeti.coeff_shiftedDet_card`).

## Main results

* `TauCeti.shiftedDet`: the polynomial `((1 + X) • A.map C - 1).det : R[X]`.
* `TauCeti.eval₂_shiftedDet`: evaluation of `shiftedDet A` along `e : R →+* S` at `y : S`.
* `TauCeti.eval_shiftedDet_zero`: `(shiftedDet A).eval 0 = (A - 1).det`.
* `TauCeti.coeff_shiftedDet_card`: `(shiftedDet A).coeff (Fintype.card n) = A.det`.

## Provenance

Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Congruences/Selmer/Untied.lean`, declarations `New.Selmer.shiftedDet`,
`New.Selmer.eval₂_shiftedDet`, and `New.Selmer.coeff_shiftedDet_card`, lifted to arbitrary
universes and reusing `Matrix.coeff_det_X_add_C_card` from
`TauCeti.LinearAlgebra.Matrix.Determinant.Pencil`.
-/

public section

open Polynomial

namespace TauCeti

variable {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]

/-- The shifted determinant polynomial `det ((1 + X) • A - 1) : R[X]` of a square matrix `A`. -/
noncomputable def shiftedDet (A : Matrix n n R) : R[X] :=
  ((1 + X : R[X]) • A.map C - 1).det

/-- Evaluating `shiftedDet A` at `y : S` along `e : R →+* S` yields
`((1 + y) • A.map e - 1).det`. -/
theorem eval₂_shiftedDet (e : R →+* S) (y : S) (A : Matrix n n R) :
    (shiftedDet A).eval₂ e y = ((1 + y) • A.map e - 1).det := by
  rw [shiftedDet, ← coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite (eval₂ e y)]

/-- Evaluating `shiftedDet A` at `0` gives `(A - 1).det`. -/
theorem eval_shiftedDet_zero (A : Matrix n n R) : (shiftedDet A).eval 0 = (A - 1).det :=
  (eval₂_shiftedDet (RingHom.id R) 0 A).trans (by simp [Matrix.map_id])

/-- The coefficient of `X ^ (Fintype.card n)` in `shiftedDet A` is `A.det`. -/
theorem coeff_shiftedDet_card (A : Matrix n n R) :
    (shiftedDet A).coeff (Fintype.card n) = A.det := by
  have hsplit : (1 + X : R[X]) • A.map C - 1 = (X : R[X]) • A.map C + (A - 1).map C := by
    rw [add_smul, one_smul, Matrix.map_sub _ (map_sub C), Matrix.map_one _ C_0 C_1]
    abel
  rw [shiftedDet, hsplit, coeff_det_X_add_C_card]

end TauCeti
