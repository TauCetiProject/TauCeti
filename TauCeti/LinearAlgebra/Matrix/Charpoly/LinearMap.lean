/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

/-!
# Cayley–Hamilton for an endomorphism represented by a matrix

Let `b : ι → M` span the `R`-module `M`. If a square matrix `A` represents the endomorphism `f`
on `b` (`Matrix.Represents`), then `f` is a root of the characteristic polynomial of `A`. This is
the step from the matrix Cayley–Hamilton theorem `Matrix.aeval_self_charpoly` to endomorphisms of
finitely generated modules that Mathlib performs inside the proof of
`LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero`, stated for a
given representing matrix, so that the polynomial can be read off from the matrix.

## Main results

* `Matrix.Represents.aeval_charpoly_eq_zero`: if `A` represents `f` on a spanning family, then
  `aeval f A.charpoly = 0`.
-/

public section

open Polynomial

namespace Matrix.Represents

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R M : Type*} [CommRing R] [AddCommGroup M]
  [Module R M] {b : ι → M}

/-- **Cayley–Hamilton along a representation.** If `A` represents the endomorphism `f` on a family
`b` spanning `M`, then `f` is a root of the characteristic polynomial of `A`. -/
theorem aeval_charpoly_eq_zero (hb : Submodule.span R (Set.range b) = ⊤) {A : Matrix ι ι R}
    {f : Module.End R M} (h : A.Represents b f) : aeval f A.charpoly = 0 := by
  rw [← Matrix.isRepresentation.eq_toEnd_of_represents R b hb ⟨A, f, h⟩ h,
    Polynomial.aeval_algHom_apply, ← map_zero (Matrix.isRepresentation.toEnd R b hb)]
  congr 1
  ext1
  rw [Polynomial.aeval_subalgebra_coe, Matrix.aeval_self_charpoly, Subalgebra.coe_zero]

end Matrix.Represents
