/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# Coordinates in the basis of `G / nG`

For a `ℤ`-basis `b` of a free `ℤ`-module `G` and `n ≠ 0`, Mathlib's `ModN.basis b` is the basis of
`ModN G n = G / nG` over `ℤ / n` formed by the classes of the vectors of `b`. This file records
that the coordinates of the class of `v` in this basis are the coordinates of `v` in `b`, reduced
modulo `n`.

## Main statements

* `ModN.basis_repr_mkQ`, `ModN.basis_repr_mk`: `(ModN.basis b).repr [v] i = (b.repr v i : ℤ / n)`.
-/

@[expose] public section

open Module

namespace ModN

variable {G ι : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]

/-- The coordinates of the class of `v` in `ModN.basis b` are the coordinates of `v` in `b`,
reduced modulo `n`. -/
@[simp]
theorem basis_repr_mkQ (b : Basis ι ℤ G) (v : G) (i : ι) :
    (basis b).repr (mkQ n v) i = (b.repr v i : ZMod n) :=
  rfl

/-- The coordinates of the class of `v` in `ModN.basis b` are the coordinates of `v` in `b`,
reduced modulo `n`: the form of `ModN.basis_repr_mkQ` for `Submodule.Quotient.mk`. -/
@[simp]
theorem basis_repr_mk (b : Basis ι ℤ G) (v : G) (i : ι) :
    (basis b).repr (Submodule.Quotient.mk v : ModN G n) i = (b.repr v i : ZMod n) :=
  rfl

end ModN
