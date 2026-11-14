/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor-product basis coordinates

This file records how contractions against one factor of a tensor product detect equality when
that factor is projective, how contracting against a basis of one factor extracts coefficients,
and how coordinates in a basis of one factor commute with maps of the other.
It also proves that the coordinates in bases obtained by scalar extension commute with a map of
the scalar-extension algebras, and that over a basis with at most one index a scalar extension
consists of pure tensors.

## Main declarations

* `TensorProduct.tensor_eq_of_forall_tensorComponent_eq`: contractions against a projective right
  factor detect equality.
* `Submodule.tensor_mem_range_iff_forall_tensorComponent_mem`: contractions against a projective
  right factor detect membership in the tensor product with a submodule of the left factor.
* `Module.Basis.tensorComponent_coord_sum_tmul`: contracting against a coordinate functional of a
  basis of the right factor recovers the corresponding coefficient.
* `Module.Basis.equivFinsuppOfBasisLeft_lTensor_apply` and
  `Module.Basis.lTensor_eq_zero_iff_forall_equivFinsuppOfBasisLeft`: coordinates in a basis of
  the left factor commute with maps of the right factor, so such a map kills an element exactly
  when it kills every coordinate.
* `Module.Basis.baseChange_reindex`: scalar extension of a basis commutes with reindexing it.
* `Module.Basis.map_baseChange_repr`: applying a scalar map to a coordinate in a base-changed
  basis agrees with first mapping the tensor and then taking its coordinate.
* `Module.Basis.eq_baseChange_repr_tmul_of_subsingleton`: over a basis with at most one index,
  every element of a scalar extension is the pure tensor of its unique coordinate with the
  corresponding basis vector.
* `Module.Basis.baseChange_toMatrix_baseChange`: change-of-basis matrices between base-changed
  bases are obtained by mapping entries.
* `Module.Basis.map_toMatrixAlgEquiv_baseChange`: matrices in base-changed bases commute with
  scalar maps when the represented endomorphisms are intertwined by tensor-product base change.
* `Module.Basis.toMatrix_baseChange_baseChange`: matrices of scalar-extended linear maps
  are obtained by mapping entries.
* `TauCeti.piTensorEquiv`: coordinates of `(Fin m → R) ⊗[R] (Fin n → R)` in the reindexed tensor
  product of standard bases, storing the `(i, j)` coefficient at `finProdFinEquiv (i, j)`.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace TensorProduct

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Equality of all contractions against the right factor detects equality in a tensor product
over a commutative semiring when the right factor is projective. -/
theorem tensor_eq_of_forall_tensorComponent_eq [Module.Projective R N] {x y : M ⊗[R] N}
    (h : ∀ φ : Module.Dual R N,
      _root_.LinearMap.tensorComponent (R := R) (M := M) φ x =
        _root_.LinearMap.tensorComponent (R := R) (M := M) φ y) :
    x = y := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R N)
  let b := Finsupp.basisSingleOne (R := R) (ι := N)
  have hmap : map LinearMap.id s x = map LinearMap.id s y := by
    apply (equivFinsuppOfBasisRight b (M := M)).injective
    ext i
    have hcoord :
        _root_.LinearMap.tensorComponent (b.coord i) (map LinearMap.id s x) =
        _root_.LinearMap.tensorComponent (b.coord i) (map LinearMap.id s y) := by
      simpa only [_root_.LinearMap.tensorComponent_map, LinearMap.id_apply] using
        h ((b.coord i).comp s)
    simpa only [equivFinsuppOfBasisRight_apply,
      _root_.LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe] using hcoord
  have := congrArg (map LinearMap.id (Finsupp.linearCombination R id)) hmap
  simpa only [map_map, LinearMap.id_comp, hs, map_id,
    LinearMap.id_apply] using this

end TensorProduct

namespace Submodule

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Projective R N]

/-- A tensor lies in the tensor product with a submodule exactly when all its contractions
against linear functionals on the projective right factor lie in that submodule. -/
theorem tensor_mem_range_iff_forall_tensorComponent_mem (S : Submodule R M) (z : M ⊗[R] N) :
    z ∈ LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : N →ₗ[R] N)) ↔
      ∀ f : N →ₗ[R] R, LinearMap.tensorComponent f z ∈ S := by
  constructor
  · rintro ⟨w, hw⟩ f
    rw [← hw]
    have h := LinearMap.tensorComponent_map f S.subtype (LinearMap.id : N →ₗ[R] N) w
    rw [LinearMap.comp_id] at h
    rw [h]
    exact (LinearMap.tensorComponent f w).property
  · intro h
    rw [← LinearMap.rTensor_def, ← rTensor_mkQ, LinearMap.mem_ker]
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro f
    rw [map_zero, LinearMap.tensorComponent_rTensor]
    simpa only [mkQ_apply, Quotient.mk_eq_zero] using h f

end Submodule

namespace Module.Basis

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Contracting `∑ⱼ xⱼ ⊗ bⱼ` against the `i`-th coordinate functional of a basis `b` of the right
factor recovers the coefficient `xᵢ`. -/
theorem tensorComponent_coord_sum_tmul {ι : Type*} [Fintype ι] (b : Module.Basis ι R N)
    (x : ι → M) (i : ι) :
    LinearMap.tensorComponent (b.coord i) (∑ j, x j ⊗ₜ[R] b j) = x i := by
  classical
  simp [Finsupp.single_apply]

section EquivFinsuppOfBasisLeft

variable {ι : Type*} [DecidableEq ι] {P : Type*} [AddCommMonoid P] [Module R P]
variable (ℬ : Module.Basis ι R M)

/-- Coordinates in a basis of the left factor commute with maps of the right factor. -/
@[simp]
theorem equivFinsuppOfBasisLeft_lTensor_apply (g : N →ₗ[R] P) (x : M ⊗[R] N) (i : ι) :
    equivFinsuppOfBasisLeft ℬ (g.lTensor M x) i = g (equivFinsuppOfBasisLeft ℬ x i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul m n => simp

/-- Over a basis of the left factor, a map of the right factor kills an element of the tensor
product exactly when it kills each of its coordinates. -/
theorem lTensor_eq_zero_iff_forall_equivFinsuppOfBasisLeft (g : N →ₗ[R] P) (x : M ⊗[R] N) :
    g.lTensor M x = 0 ↔ ∀ i, g (equivFinsuppOfBasisLeft ℬ x i) = 0 := by
  rw [← (equivFinsuppOfBasisLeft ℬ).map_eq_zero_iff, Finsupp.ext_iff]
  simp

end EquivFinsuppOfBasisLeft

end Module.Basis

namespace Module.Basis

universe u v w x

variable {R : Type u} [CommSemiring R]
variable {M : Type x} [AddCommMonoid M] [Module R M]
variable {ι : Type*}

section Repr

variable {S : Type v} [Semiring S] [Algebra R S]
variable {T : Type w} [Semiring T] [Algebra R T]

/-- Scalar extension of a basis commutes with reindexing it. -/
theorem baseChange_reindex {ι' : Type*} (b : Basis ι R M) (e : ι ≃ ι') :
    (b.reindex e).baseChange S = (b.baseChange S).reindex e :=
  eq_of_apply_eq fun i => by simp

/-- Coordinates in a base-changed basis are natural in the scalar-extension algebra. -/
@[simp] theorem map_baseChange_repr (b : Basis ι R M) (φ : S →ₗ[R] T)
    (z : S ⊗[R] M) (i : ι) :
    φ ((b.baseChange S).repr z i) =
      (b.baseChange T).repr
        (TensorProduct.map φ LinearMap.id z) i := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul s m => simp

/-- Over a basis with at most one index, every element of a scalar extension is the pure tensor
of its unique coordinate with the corresponding basis vector.  This isolates the tensor
bookkeeping needed to reduce statements about rank-at-most-one scalar extensions to scalar
multiples of a single vector. -/
theorem eq_baseChange_repr_tmul_of_subsingleton [Subsingleton ι] (b : Basis ι R M)
    (z : S ⊗[R] M) (i : ι) :
    z = (b.baseChange S).repr z i ⊗ₜ b i := by
  let _ : Fintype ι := Fintype.ofFinite ι
  conv_lhs => rw [← (b.baseChange S).sum_repr z]
  rw [Fintype.sum_subsingleton _ i, baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

end Repr

section Matrix

variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {T : Type w} [CommSemiring T] [Algebra R T]

/-- The change-of-basis matrix between two base-changed bases is the entrywise scalar extension
of the change-of-basis matrix between the original bases. -/
@[simp] theorem baseChange_toMatrix_baseChange {ι' : Type*} (b : Basis ι R M)
    (b' : Basis ι' R M) :
    (b.baseChange S).toMatrix (b'.baseChange S) = (b.toMatrix b').map (algebraMap R S) := by
  ext i j
  simp [toMatrix_apply, baseChange_apply, Algebra.smul_def]

variable [Fintype ι] [DecidableEq ι]

/-- The matrix of a scalar-extended linear map is the entrywise scalar extension of its
matrix in the original source and target bases. -/
@[simp] theorem toMatrix_baseChange_baseChange {κ N : Type*} [Finite κ]
    [AddCommMonoid N] [Module R N] (b : Basis ι R M) (c : Basis κ R N) (f : M →ₗ[R] N) :
    LinearMap.toMatrix (b.baseChange S) (c.baseChange S) (f.baseChange S) =
      (LinearMap.toMatrix b c f).map (algebraMap R S) := by
  ext i j
  simp [LinearMap.toMatrix_apply, baseChange_apply, Algebra.smul_def]

/-- Matrices in base-changed bases commute with a scalar map when the corresponding
endomorphisms are intertwined by tensor-product base change. -/
theorem map_toMatrixAlgEquiv_baseChange (b : Basis ι R M) (φ : S →ₐ[R] T)
    (f : S ⊗[R] M →ₗ[S] S ⊗[R] M) (g : T ⊗[R] M →ₗ[T] T ⊗[R] M)
    (h : ∀ z, TensorProduct.map φ.toLinearMap LinearMap.id (f z) =
      g (TensorProduct.map φ.toLinearMap LinearMap.id z)) :
    (LinearMap.toMatrixAlgEquiv (b.baseChange S) f).map φ =
      LinearMap.toMatrixAlgEquiv (b.baseChange T) g := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.toMatrixAlgEquiv_apply, ← AlgHom.toLinearMap_apply,
    map_baseChange_repr b φ.toLinearMap]
  apply congrArg (fun z => (b.baseChange T).repr z i)
  rw [h]
  simp only [baseChange_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    LinearMap.id_apply, map_one]

end Matrix

end Module.Basis

namespace TauCeti

section PiTensorEquiv

variable {R : Type*} [CommSemiring R]

variable (R) in
/-- Coordinates of `(Fin m → R) ⊗[R] (Fin n → R)` in the tensor product of the standard bases,
reindexed by `finProdFinEquiv` so that the `(i, j)` coefficient sits at `finProdFinEquiv (i, j)`. -/
noncomputable def piTensorEquiv (m n : ℕ) :
    (Fin m → R) ⊗[R] (Fin n → R) ≃ₗ[R] (Fin (m * n) → R) :=
  (((Pi.basisFun R (Fin m)).tensorProduct (Pi.basisFun R (Fin n))).reindex
    finProdFinEquiv).equivFun

/-- On a pure tensor `u ⊗ₜ v`, the coordinate at `finProdFinEquiv (i, j)` is `u i * v j`. -/
@[simp] theorem piTensorEquiv_tmul_apply {m n : ℕ} (u : Fin m → R) (v : Fin n → R)
    (i : Fin m) (j : Fin n) :
    piTensorEquiv R m n (u ⊗ₜ v) (finProdFinEquiv (i, j)) = u i * v j := by
  rw [piTensorEquiv, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply,
    Equiv.symm_apply_apply, Module.Basis.tensorProduct_repr_tmul_apply, Pi.basisFun_repr,
    Pi.basisFun_repr, smul_eq_mul, mul_comm]

/-- A single coordinate at `finProdFinEquiv (i, j)` corresponds to the pure tensor of single
coordinates `Pi.single i r ⊗ₜ Pi.single j 1`. -/
@[simp] theorem piTensorEquiv_symm_single {m n : ℕ} (i : Fin m) (j : Fin n) (r : R) :
    (piTensorEquiv R m n).symm (Pi.single (finProdFinEquiv (i, j)) r) =
      Pi.single i r ⊗ₜ Pi.single j 1 := by
  apply (piTensorEquiv R m n).injective
  rw [LinearEquiv.apply_symm_apply]
  ext k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [piTensorEquiv_tmul_apply]
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]

/-- In `piTensorEquiv` coordinates, `TensorProduct.map f g` acts on rows by `g` and then on
columns by `f`, matching the Kronecker-product formula on `Fin (m * n) → R`. -/
theorem piTensorEquiv_map_apply {m n m' n' : ℕ} (f : (Fin m → R) →ₗ[R] (Fin m' → R))
    (g : (Fin n → R) →ₗ[R] (Fin n' → R)) (z : (Fin m → R) ⊗[R] (Fin n → R))
    (i : Fin m') (j : Fin n') :
    piTensorEquiv R m' n' (TensorProduct.map f g z) (finProdFinEquiv (i, j)) =
      f (fun i' ↦ g (fun j' ↦ piTensorEquiv R m n z (finProdFinEquiv (i', j'))) j) i := by
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [TensorProduct.map_tmul, piTensorEquiv_tmul_apply]
    have hrow : ∀ i', (fun j' ↦ u i' * v j') = u i' • v := fun _ ↦ rfl
    simp_rw [hrow, map_smul, Pi.smul_apply, smul_eq_mul]
    have hcol : (fun i' ↦ u i' * g v j) = g v j • u := funext fun _ ↦ mul_comm _ _
    rw [hcol, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
    have hrow : ∀ i', (fun j' ↦ piTensorEquiv R m n x (finProdFinEquiv (i', j')) +
        piTensorEquiv R m n y (finProdFinEquiv (i', j'))) =
      (fun j' ↦ piTensorEquiv R m n x (finProdFinEquiv (i', j'))) +
        (fun j' ↦ piTensorEquiv R m n y (finProdFinEquiv (i', j'))) := fun _ ↦ rfl
    simp_rw [hrow, map_add, Pi.add_apply]
    rw [← Pi.add_def, map_add, Pi.add_apply]

end PiTensorEquiv

end TauCeti
