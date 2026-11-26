/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

import TauCeti.LinearAlgebra.Matrix.Charpoly.Block
import TauCeti.LinearAlgebra.Pi

/-!
# The characteristic polynomial of a coordinatewise endomorphism

A family of endomorphisms `fᵢ` of free modules of finite rank `Mᵢ`, indexed by a finite type,
acts coordinatewise on the product `∀ i, Mᵢ` (`LinearMap.piMap`). Its characteristic polynomial is
the product of the characteristic polynomials of the `fᵢ`. In the product basis its matrix is the
block-diagonal matrix `Matrix.blockDiagonal'` of the matrices of the `fᵢ`
(`LinearMap.toMatrix_piMap`), whose characteristic polynomial is the product of those of its blocks
(`Matrix.charpoly_blockDiagonal'`). This extends Mathlib's `LinearMap.charpoly_prodMap` from two
factors to finitely many.

## Main results

* `LinearMap.charpoly_piMap`: the characteristic polynomial of `LinearMap.piMap f` is
  `∏ i, (f i).charpoly`.
-/

public section

namespace LinearMap

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
  [∀ i, Module.Finite R (M i)]

/-- The characteristic polynomial of an endomorphism of a finite product of free modules of finite
rank acting coordinatewise is the product of the characteristic polynomials of its coordinates. -/
@[simp]
theorem charpoly_piMap (f : ∀ i, Module.End R (M i)) :
    (piMap f).charpoly = ∏ i, (f i).charpoly := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  rw [← charpoly_toMatrix _ (Pi.basis b), toMatrix_piMap b b, Matrix.charpoly_blockDiagonal']
  simp only [charpoly_toMatrix]

end LinearMap
