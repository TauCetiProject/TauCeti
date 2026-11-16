/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Perfect pairings from Gram matrices

Let `B : M →ₗ[R] N →ₗ[R] R` be a bilinear pairing, `b` a basis of `M` and `c` a finite basis of
`N`. If `e` is a bijection between the index sets and `B (b i) (c j)` is `1` when `j = e i` and `0`
otherwise, then `B` sends each `b i` to the dual basis vector of `c` at `e i`, so it is the linear
equivalence of `M` onto the dual of `N` obtained by matching `b` with that dual basis along `e`. No
scalar is inverted, so `B` is a perfect pairing over every commutative semiring.

More generally, over a commutative ring, a pairing whose Gram matrix `G` in finite bases `b` and `c`
indexed by the same type has unit determinant is a perfect pairing: in the bases `b` and the dual
basis of `c`, the map `M → Dual R N` given by `B` has matrix `Gᵀ`, which is invertible. Conversely,
the Gram matrix of a perfect pairing in any such pair of bases has unit determinant.

## Main results

* `Module.Basis.isPerfPair_of_apply_eq_ite`: a pairing whose Gram matrix in finite bases is the
  matrix of a bijection of the index sets is a perfect pairing.
* `Module.Basis.toMatrix_dualBasis_eq_transpose_toMatrix₂`: for finite bases `b` of `M` and `c` of
  `N`, the matrix of the map `M → Dual R N` given by a pairing, in `b` and the dual basis of `c`,
  is the transpose of its Gram matrix in `b` and `c`.
* `Module.Basis.isPerfPair_of_isUnit_det`: a pairing whose Gram matrix in finite bases has unit
  determinant is a perfect pairing.
* `Module.Basis.isUnit_det_of_isPerfPair`: the Gram matrix of a perfect pairing in finite bases has
  unit determinant.
-/

public section

namespace Module.Basis

section CommSemiring

variable {ι κ R M N : Type*} [Finite κ] [DecidableEq κ] [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- **A pairing whose Gram matrix in finite bases is the matrix of a bijection of the index sets is
a perfect pairing.** It is the linear equivalence of `M` onto the dual of `N` sending `b i` to the
vector of the dual basis of `c` at `e i`. -/
theorem isPerfPair_of_apply_eq_ite (b : Basis ι R M) (c : Basis κ R N) (B : M →ₗ[R] N →ₗ[R] R)
    (e : ι ≃ κ) (h : ∀ i j, B (b i) (c j) = if j = e i then 1 else 0) :
    B.IsPerfPair := by
  have : Module.Finite R N := .of_basis c
  have : Module.Free R N := .of_basis c
  have key : B = (b.equiv c.dualBasis e).toLinearMap :=
    b.ext fun i => c.ext fun j => by
      rw [LinearEquiv.coe_coe, equiv_apply, dualBasis_apply_self, h]
  rw [key]
  infer_instance

end CommSemiring

open Matrix

section GramMatrix

variable {ι κ R M N : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- **The map of a pairing into the dual has the transposed Gram matrix.** In the basis `b` of `M`
and the dual basis of `c`, the matrix of `B`, read as a linear map from `M` to the dual of `N`, is
the transpose of the Gram matrix of `B` in `b` and `c`. -/
theorem toMatrix_dualBasis_eq_transpose_toMatrix₂ (b : Basis ι R M) (c : Basis κ R N)
    (B : M →ₗ[R] N →ₗ[R] R) :
    LinearMap.toMatrix b c.dualBasis B = (LinearMap.toMatrix₂ b c B)ᵀ := by
  ext i j
  simp [LinearMap.toMatrix_apply, LinearMap.toMatrix₂_apply]

end GramMatrix

section CommRing

variable {ι R M N : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **A pairing whose Gram matrix in finite bases has unit determinant is a perfect pairing.** -/
theorem isPerfPair_of_isUnit_det (b : Basis ι R M) (c : Basis ι R N) (B : M →ₗ[R] N →ₗ[R] R)
    (h : IsUnit (LinearMap.toMatrix₂ b c B).det) : B.IsPerfPair := by
  have : Module.Finite R N := .of_basis c
  have : Module.Free R N := .of_basis c
  refine .of_bijective B ?_
  rw [← LinearEquiv.coe_ofIsUnitDet (v := b) (v' := c.dualBasis) (f := B)
    (by rwa [toMatrix_dualBasis_eq_transpose_toMatrix₂, det_transpose]), LinearEquiv.coe_coe]
  exact LinearEquiv.bijective _

/-- **The Gram matrix of a perfect pairing in finite bases has unit determinant.** -/
theorem isUnit_det_of_isPerfPair (b : Basis ι R M) (c : Basis ι R N) (B : M →ₗ[R] N →ₗ[R] R)
    (h : B.IsPerfPair) : IsUnit (LinearMap.toMatrix₂ b c B).det := by
  -- `B`, read as a linear map into the dual of `N`, is the linear equivalence it induces.
  have he : (LinearEquiv.ofBijective B h.bijective_left : M →ₗ[R] Module.Dual R N) = B :=
    LinearMap.ext (LinearEquiv.ofBijective_apply B)
  rw [← det_transpose, ← toMatrix_dualBasis_eq_transpose_toMatrix₂, ← he]
  exact (LinearEquiv.ofBijective B h.bijective_left).isUnit_det b c.dualBasis

end CommRing

end Module.Basis
