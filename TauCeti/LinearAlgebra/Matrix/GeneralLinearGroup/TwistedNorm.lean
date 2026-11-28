/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.Group.Hom.TwistedNorm

/-!
# Twisted norms in general linear groups

For a ring endomorphism `σ : R →+* R` and `c : GL n R`, the iterates of the twisted
multiplication `v ↦ c * σ(v)` on `Matrix n n R` are given by the partial twisted norms
`N_i(c) = c * σ(c) * ⋯ * σ^(i-1)(c)` of `c` under `GeneralLinearGroup.map σ`:
`(v ↦ c * σ(v))^[i] v = N_i(c) * σ^i(v)`. This is the computation behind the classical proof of
Hilbert's Theorem 90 for `GL n`.

## Main results

* `Matrix.GeneralLinearGroup.iterate_mul_map_eq_twistedNorm_mul_map`: the iterates of
  `v ↦ c * σ(v)` are `v ↦ N_i(c) * σ^i(v)`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The `i`-th iterate of the twisted multiplication `v ↦ c * σ(v)` on `Matrix n n R` is
`v ↦ N_i(c) * σ^i(v)`, where `N_i(c) = c * σ(c) * ⋯ * σ^(i-1)(c)` is the `i`-th twisted norm of
`c` under `GeneralLinearGroup.map σ`. -/
theorem iterate_mul_map_eq_twistedNorm_mul_map (σ : R →+* R) (c : GL n R) (i : ℕ)
    (v : Matrix n n R) :
    (fun w : Matrix n n R ↦ (c : Matrix n n R) * w.map σ)^[i] v =
      ((MonoidHom.twistedNorm (map σ) i c : GL n R) : Matrix n n R) * v.map ⇑(σ ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [MonoidHom.twistedNorm_succ]
    simp [Function.iterate_succ_apply', ih, Matrix.map_mul, Matrix.map_map, mul_assoc, pow_succ']

end Matrix.GeneralLinearGroup
