/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.Matrix.Charpoly.BlockDiagonal

/-!
# Characteristic polynomials on finite products

The characteristic polynomial of a coordinatewise endomorphism `LinearMap.piMap f` of a finite
product of finite free modules is the product of the characteristic polynomials of its
components (`LinearMap.charpoly_piMap`). This extends Mathlib's `LinearMap.charpoly_prodMap` from
two factors to finitely many. In a product basis `piMap f` has the block-diagonal matrix of the
`f i` (`LinearMap.toMatrix_piMap`), and the characteristic polynomial of a block-diagonal matrix
is the product of the characteristic polynomials of its blocks (`Matrix.charpoly_blockDiagonal'`,
in `TauCeti.LinearAlgebra.Matrix.Charpoly.BlockDiagonal`).

## Main result

* `LinearMap.charpoly_piMap`: the characteristic polynomial of `piMap f` is `∏ i, (f i).charpoly`.
-/

public section

open Polynomial

namespace LinearMap

variable {R ι : Type*} [CommRing R] [Fintype ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- **The characteristic polynomial is multiplicative on finite products.** The characteristic
polynomial of a coordinatewise endomorphism `piMap f` of a finite product of finite free modules
is the product of the characteristic polynomials of its components. -/
theorem charpoly_piMap (f : ∀ i, Module.End R (M i)) :
    (piMap f).charpoly = ∏ i, (f i).charpoly := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  rw [← charpoly_toMatrix _ (Pi.basis b), toMatrix_piMap b b, Matrix.charpoly_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ => charpoly_toMatrix (f i) (b i)

end LinearMap
