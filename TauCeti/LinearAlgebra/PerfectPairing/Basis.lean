/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Perfect pairings with a permutation Gram matrix

Let `b` be a finite basis of a module `M` over a commutative ring and `σ` a permutation of its
index set. A bilinear form `B` with `B (b i) (b j) = 1` when `j = σ i` and `0` otherwise sends each
`b i` to the dual basis vector at `σ i`, so it is the linear equivalence of `M` onto its dual
obtained by reindexing the dual basis along `σ`. No scalar is inverted, so `B` is a perfect pairing
over every commutative ring.

## Main results

* `Module.Basis.isPerfPair_of_apply_eq_ite`: a bilinear form whose Gram matrix in a finite basis
  is a permutation matrix is a perfect pairing.
-/

public section

namespace Module.Basis

variable {ι R M : Type*} [Finite ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]

/-- **A bilinear form whose Gram matrix in a finite basis is a permutation matrix is a perfect
pairing.** It is the linear equivalence of `M` onto its dual sending `b i` to the dual basis vector
at `σ i`. -/
theorem isPerfPair_of_apply_eq_ite (b : Basis ι R M) (B : M →ₗ[R] M →ₗ[R] R)
    (σ : Equiv.Perm ι) (h : ∀ i j, B (b i) (b j) = if j = σ i then 1 else 0) :
    B.IsPerfPair := by
  have : Module.Finite R M := .of_basis b
  have : Module.Free R M := .of_basis b
  have key : B = (b.equiv b.dualBasis σ).toLinearMap :=
    b.ext fun i => b.ext fun j => by
      rw [LinearEquiv.coe_coe, equiv_apply, dualBasis_apply_self, h]
  rw [key]
  infer_instance

end Module.Basis
