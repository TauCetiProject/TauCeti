/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.AdjoinRoot

import TauCeti.RingTheory.AdjoinRoot.Minpoly

/-!
# The characteristic polynomial of multiplication by an adjoined root

For a monic polynomial `f` of degree `d` over a commutative ring `R`, the algebra `AdjoinRoot f` is
free over `R` with power basis `1, α, …, α ^ (d - 1)`, where `α = root f`. In this basis the matrix
of multiplication by `α` is the companion matrix of `f`, and its characteristic polynomial is `f`.
This holds for every monic `f`, including `f = 1`, where `AdjoinRoot f` is the zero module and the
characteristic polynomial is `1`.

The identity is the algebraic input to reading the characteristic polynomial of multiplication by
`X` on a quotient of a power series ring off a Weierstrass factorization
(`PowerSeries.IsWeierstrassFactorizationAt.charpoly_lmul_mk_X`).

## Main results

* `PowerBasis.charpoly_lmul_gen`: for a power basis of `S` over `R`, multiplication by the
  generator has characteristic polynomial the minimal polynomial of the generator. This is the
  endomorphism form of Mathlib's `charpoly_leftMulMatrix`.
* `AdjoinRoot.charpoly_lmul_root`: multiplication by the adjoined root of a monic `f` has
  characteristic polynomial `f`.
-/

public section

open Polynomial

/-- For a power basis of `S` over `R`, the characteristic polynomial of multiplication by the
generator is the minimal polynomial of the generator. -/
theorem PowerBasis.charpoly_lmul_gen {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (pb : PowerBasis R S) :
    (Algebra.lmul R S pb.gen).charpoly = minpoly R pb.gen := by
  rw [← LinearMap.charpoly_toMatrix _ pb.basis, ← Algebra.leftMulMatrix_apply,
    charpoly_leftMulMatrix]

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
