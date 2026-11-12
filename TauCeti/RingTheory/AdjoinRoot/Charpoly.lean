/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.PowerBasis

import TauCeti.RingTheory.AdjoinRoot.Minpoly

/-!
# The characteristic polynomial of multiplication by an adjoined root

For a monic polynomial `f` of degree `d` over a commutative ring `R`, the algebra `AdjoinRoot f` is
free over `R` with power basis `1, α, …, α ^ (d - 1)`, where `α = root f`. In this basis the matrix
of multiplication by `α` is the companion matrix of `f`, and its characteristic polynomial is `f`.
This holds for every monic `f`, including `f = 1`, where `AdjoinRoot f` is the zero module and the
characteristic polynomial is `1`.

Both this identity and its transport to a quotient of a power series ring along a Weierstrass
factorization (`PowerSeries.IsWeierstrassFactorizationAt.charpoly_lmul_mk_X`) are instances of
`PowerBasis.charpoly_lmul_gen`.

## Main results

* `AdjoinRoot.charpoly_lmul_root`: multiplication by the adjoined root of a monic `f` has
  characteristic polynomial `f`.
-/

public section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {f : R[X]}

/-- Multiplication by the adjoined root of a monic polynomial `f` has characteristic polynomial
`f`. The freeness and finiteness of `AdjoinRoot f` over `R` follow from monicity
(`Polynomial.Monic.free_adjoinRoot`, `Polynomial.Monic.finite_adjoinRoot`). -/
theorem charpoly_lmul_root [Module.Free R (AdjoinRoot f)] [Module.Finite R (AdjoinRoot f)]
    (hf : f.Monic) : (Algebra.lmul R (AdjoinRoot f) (root f)).charpoly = f := by
  rw [← powerBasis'_gen hf, PowerBasis.charpoly_lmul_gen, powerBasis'_gen,
    minpoly_root_of_monic hf]

end AdjoinRoot
