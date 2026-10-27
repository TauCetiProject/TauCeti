/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.PowerBasis

/-!
# The constant coordinate of a power basis, and multiplication by the generator

An `R`-algebra `S` with a power basis `1, x, …, x ^ (d - 1)` retracts onto `R`: the coordinate
along `x ^ 0 = 1` is an `R`-linear map `S → R` sending `1` to `1`. So `R · 1` is a direct summand of
`S`, which is what it takes to descend a span over `S` back to a span over `R`
(`TauCeti.mem_of_mem_span_of_mem_closure`).

## Main statements

* `PowerBasis.exists_linearMap_apply_one`: an algebra with a power basis retracts onto its scalars.
* `PowerBasis.charpoly_lmul_gen`: multiplication by the generator of a power basis has
  characteristic polynomial the minimal polynomial of the generator. This is the endomorphism form
  of Mathlib's `charpoly_leftMulMatrix`.
-/

public section

/-- **An algebra with a power basis retracts onto its scalars**: the coordinate along
`pb.gen ^ 0 = 1` is an `R`-linear map `S → R` sending `1` to `1`. -/
theorem PowerBasis.exists_linearMap_apply_one {R S : Type*} [CommRing R] [Ring S] [Nontrivial S]
    [Algebra R S] (pb : PowerBasis R S) : ∃ t : S →ₗ[R] R, t 1 = 1 := by
  refine ⟨pb.basis.coord ⟨0, pb.dim_pos⟩, ?_⟩
  have h : pb.basis ⟨0, pb.dim_pos⟩ = 1 := by rw [pb.basis_eq_pow, pow_zero]
  rw [← h, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- For a power basis of `S` over `R`, the characteristic polynomial of multiplication by the
generator is the minimal polynomial of the generator. -/
theorem PowerBasis.charpoly_lmul_gen {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (pb : PowerBasis R S) :
    (Algebra.lmul R S pb.gen).charpoly = minpoly R pb.gen := by
  rw [← LinearMap.charpoly_toMatrix _ pb.basis, ← Algebra.leftMulMatrix_apply,
    charpoly_leftMulMatrix]
