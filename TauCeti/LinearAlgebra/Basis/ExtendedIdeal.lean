/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Quotient
public import TauCeti.RingTheory.Ideal.Extended
import TauCeti.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Submodule.Quotient
import TauCeti.RingTheory.Ideal.Operations

/-!
# Coefficient matrices modulo an extended ideal

Let `A` be an `R`-algebra with a finite basis `b`, and let `φ : V →ₗ[R] A` be a linear map from a
module with a finite basis `v`. The coefficient matrix of `φ` is Mathlib's
`LinearMap.toMatrix v b φ`, with rows indexed by the basis of `A`: its entry at `(i, j)` is the
coordinate `b.repr (φ (v j)) i`. The coordinate `i` of `φ (∑ j, x j • v j)` is the `i`-th row of
this matrix applied to `x` (`LinearMap.toMatrix_mulVec_eq_repr`), and since membership in an
extended ideal `J A` is read off the coordinates (`Ideal.mem_map_algebraMap_iff` with
`Module.Basis.mem_smul_top_iff`), the value `φ (∑ j, x j • v j)` lies in `J A` exactly when every
row applied to `x` lies in `J`.

For a commutative `A` and an arbitrary ideal `J` of `R`, the quotient `A ⧸ J A` is free over
`R ⧸ J` on the classes of the basis vectors (`Module.Basis.quotient`): this is the base change of
`b` to `R ⧸ J`, transported along `(R ⧸ J) ⊗[R] A ≃ A ⧸ J A`. The coordinates of the class of `x`
are the classes of the coordinates of `x`, so the coefficient matrix of a reduction of `φ` is the
entrywise reduction of the coefficient matrix of `φ`. At the maximal ideal of a local ring this
basis is Mathlib's `IsLocalRing.basisQuotient`.

The coordinate map `A → ι → R` is not a ring homomorphism, so none of this computes the
determinant of an `A`-valued matrix coordinatewise.

## Main definitions

* `Module.Basis.quotientEquiv`: coordinates modulo an extended ideal in an algebra that may
  be noncommutative, as a linear equivalence over the original scalar ring.
* `Module.Basis.quotient`: the basis of `A ⧸ J A` over `R ⧸ J` given by the classes of a basis of
  `A` over `R`.

## Main results

* `LinearMap.apply_sum_smul_mem_map_algebraMap_iff`: `φ (∑ j, x j • v j) ∈ J A` exactly when every
  row of the coefficient matrix applied to `x` lies in `J`.
* `Module.Basis.quotient_repr_mk`: the coordinates of a class are the classes of the coordinates.
* `LinearMap.toMatrix_quotient`: the coefficient matrix of a reduction of `φ` is the entrywise
  reduction of the coefficient matrix of `φ`.

## References

* H. Matsumura, *Commutative Ring Theory*, Chapter 1, §2 (the module `M ⧸ J M ≅ (R ⧸ J) ⊗ M` and
  base change of free modules).
-/

public section

open Module Matrix

variable {R A V ι κ : Type*}

namespace LinearMap

section Coordinates

variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid V] [Module R V]
  [Fintype κ] [DecidableEq κ] [Finite ι]

/-- **Extended-ideal membership through the coefficient matrix.** For an ideal `J` of `R`, the
value `φ (∑ j, x j • v j)` lies in the extended ideal `J A` exactly when every row of the
coefficient matrix `LinearMap.toMatrix v b φ` applied to `x` lies in `J`. -/
theorem apply_sum_smul_mem_map_algebraMap_iff (v : Basis κ R V) (b : Basis ι R A)
    (φ : V →ₗ[R] A) (J : Ideal R) (x : κ → R) :
    φ (∑ j, x j • v j) ∈ J.map (algebraMap R A) ↔ ∀ i, (toMatrix v b φ *ᵥ x) i ∈ J := by
  rw [Ideal.mem_map_algebraMap_iff, b.mem_smul_top_iff, toMatrix_mulVec_eq_repr]

end Coordinates

end LinearMap

namespace Module.Basis

section QuotientEquiv

variable [CommRing R] [Ring A] [Algebra R A]

/-- Coordinates modulo an extended scalar ideal are finitely supported families of scalar
residue classes. The algebra need not be commutative, and the equivalence is linear over `R`. -/
noncomputable def quotientEquiv (b : Basis ι R A) (J : Ideal R) :
    (A ⧸ J.map (algebraMap R A)) ≃ₗ[R] (ι →₀ R ⧸ J) :=
  (Submodule.quotEquivOfEqRestrictScalars (J • (⊤ : Submodule R A))
      (J.map (algebraMap R A)) (Ideal.smul_top_eq_restrictScalars_map J)).symm ≪≫ₗ
    (TensorProduct.quotTensorEquivQuotSMul A J).symm ≪≫ₗ
      (b.baseChange (R ⧸ J)).repr.restrictScalars R

/-- The quotient coordinates of a representative are its original coordinates reduced
modulo the scalar ideal. -/
@[simp]
theorem quotientEquiv_mk (b : Basis ι R A) (J : Ideal R) (x : A) (i : ι) :
    b.quotientEquiv J (Ideal.Quotient.mk _ x) i =
      Ideal.Quotient.mk J (b.repr x i) := by
  simp only [quotientEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [← Ideal.Quotient.mk_eq_mk, Submodule.quotEquivOfEqRestrictScalars_symm_mk
      (J • (⊤ : Submodule R A))
      (J.map (algebraMap R A)) (Ideal.smul_top_eq_restrictScalars_map J) x,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk, baseChange_repr_tmul]
  simp [Algebra.smul_def]

/-- Reduction along an inclusion of scalar ideals reduces each coordinate by the scalar
quotient map. -/
theorem quotientEquiv_factor (b : Basis ι R A) {J K : Ideal R} (h : J ≤ K)
    (x : A ⧸ J.map (algebraMap R A)) (i : ι) :
    b.quotientEquiv K (Ideal.Quotient.factor (Ideal.map_mono h) x) i =
      Ideal.Quotient.factor h (b.quotientEquiv J x i) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk, quotientEquiv_mk]

end QuotientEquiv

section Quotient

variable [CommRing R] [CommRing A] [Algebra R A]

/-- **Reduction of a basis modulo an extended ideal.** For an arbitrary ideal `J` of `R`, the
classes of a basis of `A` over `R` form a basis of `A ⧸ J A` over `R ⧸ J`: the base change of `b`
to `R ⧸ J`, transported along `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. -/
noncomputable def quotient (b : Basis ι R A) (J : Ideal R) :
    Basis ι (R ⧸ J) (A ⧸ J.map (algebraMap R A)) :=
  (b.baseChange (R ⧸ J)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A J).symm.toLinearEquiv

@[simp]
theorem quotient_apply (b : Basis ι R A) (J : Ideal R) (i : ι) :
    b.quotient J i = Ideal.Quotient.mk _ (b i) := by
  simp [quotient, AlgEquiv.symm_apply_eq]

/-- The coordinates of the class of `x` in `b.quotient J` are the classes of the coordinates of
`x` in `b`. -/
@[simp]
theorem quotient_repr_mk (b : Basis ι R A) (J : Ideal R) (x : A) (i : ι) :
    (b.quotient J).repr (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk J (b.repr x i) := by
  simp [quotient, Algebra.smul_def]

end Quotient

end Module.Basis

namespace LinearMap

variable [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid V] [Module R V]
  [Fintype κ] [DecidableEq κ] [Finite ι]

/-- **Reduction of the coefficient matrix.** If `φ' : V' →ₗ[R ⧸ J] A ⧸ J A` reduces
`φ : V →ₗ[R] A`, in the sense that `φ' (v' j)` is the class of `φ (v j)` for bases `v` and `v'`
indexed by the same type, then its coefficient matrix in the basis `b.quotient J` is the entrywise
reduction modulo `J` of the coefficient matrix of `φ`. -/
theorem toMatrix_quotient {J : Ideal R} {V' : Type*} [AddCommMonoid V'] [Module (R ⧸ J) V']
    (v : Basis κ R V) (v' : Basis κ (R ⧸ J) V')
    (b : Basis ι R A) (φ : V →ₗ[R] A) (φ' : V' →ₗ[R ⧸ J] A ⧸ J.map (algebraMap R A))
    (h : ∀ j, φ' (v' j) = Ideal.Quotient.mk _ (φ (v j))) :
    toMatrix v' (b.quotient J) φ' = (toMatrix v b φ).map (Ideal.Quotient.mk J) := by
  ext i j
  rw [toMatrix_apply, h, Basis.quotient_repr_mk, map_apply, toMatrix_apply]

end LinearMap
