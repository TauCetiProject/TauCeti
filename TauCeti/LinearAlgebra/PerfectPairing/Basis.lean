/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Perfect pairings and bases

Let `B : M →ₗ[R] N →ₗ[R] R` be a bilinear pairing, `b` a basis of `M` and `c` a finite basis of
`N`. If `e` is a bijection between the index sets and `B (b i) (c j)` is `1` when `j = e i` and `0`
otherwise, then `B` sends each `b i` to the dual basis vector of `c` at `e i`, so it is the linear
equivalence of `M` onto the dual of `N` obtained by matching `b` with that dual basis along `e`. No
scalar is inverted, so `B` is a perfect pairing over every commutative semiring.

More generally, over a commutative ring, a pairing whose Gram matrix `G` in finite bases `b` and `c`
indexed by the same type has unit determinant is a perfect pairing: in the bases `b` and the dual
basis of `c`, the map `M → Dual R N` given by `B` has matrix `Gᵀ`, which is invertible. Conversely,
the Gram matrix of a perfect pairing in any such pair of bases has unit determinant.

Conversely, a perfect pairing `p : M × N → R` turns a finite basis `e` of `N` into its *left dual
basis* `e^i` of `M`, characterised by `p (e^i) (e_j) = δ_ij`, and every `x ∈ M` is
`∑_j p(x, e_j) e^j`. The dual basis sits in the left slot of `p`: when `p` is not symmetric the
right dual basis, with `p (e_j) (e^i) = δ_ij`, is a different basis. Mathlib's
`LinearMap.BilinForm.dualBasis` is the case of a nondegenerate bilinear form on a
finite-dimensional vector space; here the scalars form any commutative semiring.

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
* `LinearMap.leftDualBasis`: the left dual basis of a finite basis for a perfect pairing, with
  `LinearMap.apply_leftDualBasis`, `LinearMap.eq_leftDualBasis_iff`, the left dual of a pairing
  given by a bijection of the index sets `LinearMap.coe_leftDualBasis_eq_comp_symm`, and the
  reconstruction `LinearMap.sum_apply_smul_leftDualBasis`.
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
  refine .of_bijective B ((LinearMap.isUnit_det_toMatrix_iff_bijective b c.dualBasis B).1 ?_)
  rwa [toMatrix_dualBasis_eq_transpose_toMatrix₂, det_transpose]

/-- **The Gram matrix of a perfect pairing in finite bases has unit determinant.** -/
theorem isUnit_det_of_isPerfPair (b : Basis ι R M) (c : Basis ι R N) (B : M →ₗ[R] N →ₗ[R] R)
    (h : B.IsPerfPair) : IsUnit (LinearMap.toMatrix₂ b c B).det := by
  rw [← det_transpose, ← toMatrix_dualBasis_eq_transpose_toMatrix₂]
  exact (LinearMap.isUnit_det_toMatrix_iff_bijective b c.dualBasis B).2 h.bijective_left

end CommRing

end Module.Basis

namespace LinearMap

open Module

variable {ι R M N : Type*} [DecidableEq ι] [Finite ι] [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]

/-- The **left dual basis** of a finite basis `e` of `N` for a perfect pairing `p : M × N → R`:
the basis `e^i` of `M` with `p (e^i) (e_j) = δ_ij` (`LinearMap.apply_leftDualBasis`). It is the
image of the dual basis of `e` under the identification of `Dual R N` with `M` given by `p`. -/
noncomputable def leftDualBasis (e : Basis ι R N) : Basis ι R M :=
  e.dualBasis.map p.toPerfPair.symm

/-- The defining property of the left dual basis: `p (e^i) (e_j) = δ_ij`. -/
@[simp]
theorem apply_leftDualBasis (e : Basis ι R N) (i j : ι) :
    p (p.leftDualBasis e i) (e j) = if j = i then 1 else 0 := by
  simp [leftDualBasis, Finsupp.single_apply]

/-- The left dual basis is the only family `f` of `M` with `p (f i) (e j) = δ_ij`. -/
theorem eq_leftDualBasis_iff (e : Basis ι R N) {f : ι → M} :
    f = p.leftDualBasis e ↔ ∀ i j, p (f i) (e j) = if j = i then 1 else 0 := by
  refine ⟨fun h ↦ h ▸ p.apply_leftDualBasis e, fun h ↦ funext fun i ↦ ?_⟩
  exact (IsPerfPair.bijective_left p).injective (e.ext fun j ↦ by rw [h, apply_leftDualBasis])

/-- If `p (f k) (e j)` is `1` when `j = σ k` and `0` otherwise, for a bijection `σ` of the index
sets, then the left dual basis of `e` is the family `f` reindexed along `σ`: `e^i = f (σ⁻¹ i)`. -/
theorem coe_leftDualBasis_eq_comp_symm {κ : Type*} (e : Basis ι R N) {f : κ → M} (σ : κ ≃ ι)
    (h : ∀ k j, p (f k) (e j) = if j = σ k then 1 else 0) :
    ⇑(p.leftDualBasis e) = f ∘ σ.symm :=
  ((p.eq_leftDualBasis_iff e).2 fun i j ↦ by
    rw [Function.comp_apply, h, Equiv.apply_symm_apply]).symm

/-- The coordinates of `x ∈ M` in the left dual basis of `e` are the pairings `p x (e_i)`. -/
@[simp]
theorem leftDualBasis_repr_apply (e : Basis ι R N) (x : M) (i : ι) :
    (p.leftDualBasis e).repr x i = p x (e i) := by
  simp [leftDualBasis]

/-- **The left-dual reconstruction.** Every `x ∈ M` is `∑_j p(x, e_j) e^j`, for the left dual
basis `e^j` of a finite basis `e` of `N`. -/
theorem sum_apply_smul_leftDualBasis [Fintype ι] (e : Basis ι R N) (x : M) :
    ∑ j, p x (e j) • p.leftDualBasis e j = x := by
  simpa using (p.leftDualBasis e).sum_repr x

end LinearMap
