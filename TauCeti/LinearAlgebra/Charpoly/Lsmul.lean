/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Characteristic polynomials of the action of an algebra

Let `A` be an algebra over a commutative ring `k`. Every `a : A` acts `k`-linearly on an
`A`-module `M` by `Algebra.lsmul k k M a`; for `M` finite and free over `k`, this action has a
characteristic polynomial. This file records how that polynomial behaves under `A`-linear
equivalences and products of modules.

## Main results

* `LinearEquiv.charpoly_lsmul_eq`: `A`-linearly equivalent modules have the same characteristic
  polynomials over `k`.
* `Algebra.charpoly_lsmul_prod`: the characteristic polynomial of `a` on `M × N` is the product of
  those on `M` and on `N`.
-/

public section

variable {k A M N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [Module.Free k M] [Module.Finite k M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [Module.Free k N] [Module.Finite k N]

namespace LinearEquiv

/-- `A`-linearly equivalent modules have the same characteristic polynomials over `k`. -/
theorem charpoly_lsmul_eq (e : M ≃ₗ[A] N) (a : A) :
    (Algebra.lsmul k k M a).charpoly = (Algebra.lsmul k k N a).charpoly := by
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k)]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply]

end LinearEquiv

namespace Algebra

/-- The characteristic polynomial of `a` on a product is the product of the characteristic
polynomials. -/
theorem charpoly_lsmul_prod (a : A) :
    (Algebra.lsmul k k (M × N) a).charpoly =
      (Algebra.lsmul k k M a).charpoly * (Algebra.lsmul k k N a).charpoly := by
  have : Algebra.lsmul k k (M × N) a = (Algebra.lsmul k k M a).prodMap (Algebra.lsmul k k N a) := by
    ext <;> simp
  rw [this, LinearMap.charpoly_prodMap]

end Algebra
