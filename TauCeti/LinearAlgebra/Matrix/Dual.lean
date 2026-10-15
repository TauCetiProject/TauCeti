/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `dotProductBilin` and `dotProductEquiv` occur in the statement and the body below.
public import Mathlib.LinearAlgebra.Matrix.Dual
-- `BilinForm.IsSymm` occurs in the statement below.
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
-- `LinearMap.IsPerfPair` occurs in the statement below.
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The dot product on `ι → R` is a perfect pairing

Mathlib's `dotProductEquiv` identifies `ι → R`, for `ι` finite, with its own dual under the dot
product. This file records the symmetry and perfectness of this pairing, so that the dot product
may be used directly as the pairing of a `RootPairing` or a `RootDatum` on `ι → R`.

Through the same identification, a linear equivalence `f : (ι → R) ≃ₗ[R] (κ → R)` has a
contragredient `f.dotProductContragredient`, the equivalence `g` with `g y ⬝ᵥ f x = y ⬝ᵥ x`. In
matrix terms it is the inverse transpose of `f`. It describes how a linear change of coordinates
acts on orthogonal complements for the dot product, for instance on the dual of a linear code.

## Main results

* `TauCeti.dotProductBilin_isPerfPair`: the dot product `dotProductBilin R R` on `ι → R` is a
  perfect pairing of that module with itself.
* `TauCeti.isSymm_dotProductBilin`: the standard dot-product bilinear form is symmetric.
* `TauCeti.linearIndependent_of_dotProduct_diagonal`: a family whose dot products against a second
  family vanish off the diagonal and are right-regular on it is linearly independent.
* `LinearEquiv.dotProductContragredient`: the contragredient of a linear equivalence for the dot
  product, characterized by `LinearEquiv.eq_dotProductContragredient_iff`, with matrix computed by
  `LinearEquiv.toMatrix'_dotProductContragredient`. Taking contragredients is involutive and
  compatible with composition and inversion. On invertible square matrices over a commutative
  ring it is `Matrix.GeneralLinearGroup.inverseTranspose`; here it acts on linear equivalences
  between possibly different coordinate spaces over a commutative semiring.
-/

public section

namespace TauCeti

open _root_.Matrix

/-- Over a commutative semiring, the dot product on `ι → R` is a perfect pairing of that module
with itself: it is Mathlib's `dotProductEquiv` read as a bilinear map. -/
instance dotProductBilin_isPerfPair (R ι : Type*) [CommSemiring R] [Fintype ι] :
    (dotProductBilin R R : (ι → R) →ₗ[R] (ι → R) →ₗ[R] R).IsPerfPair := by
  classical
  have h : (dotProductBilin R R : (ι → R) →ₗ[R] (ι → R) →ₗ[R] R) =
      (dotProductEquiv R ι).toLinearMap := by
    ext x y
    simp
  rw [h]
  infer_instance

/-- The standard dot-product bilinear form is symmetric. -/
theorem isSymm_dotProductBilin {R ι : Type*} [CommSemiring R] [Fintype ι] :
    LinearMap.BilinForm.IsSymm
      (dotProductBilin R R : LinearMap.BilinForm R (ι → R)) := by
  constructor
  intro x y
  simpa only [RingHom.id_apply, dotProductBilin_apply_apply] using dotProduct_comm x y

/-- **A family paired diagonally by a second family is linearly independent.** If `v i ⬝ᵥ w j`
vanishes whenever `i ≠ j` and right multiplication by `v i ⬝ᵥ w i` is injective, the `v i` are
linearly independent. Over a ring without zero divisors, nonzero diagonal entries suffice; in
particular, this applies over `ℤ` with diagonal `2`. The ring may have zero divisors away from
the chosen diagonal entries.
The family index `κ` is arbitrary — neither finite nor decidable — and unrelated to the coordinate
index `ι`; the scalars need not commute. -/
theorem linearIndependent_of_dotProduct_diagonal {κ ι R : Type*}
    [Fintype ι] [Ring R] {v w : κ → ι → R} {c : κ → R}
    (hc : ∀ i, IsRightRegular (c i)) (hdiag : ∀ i, v i ⬝ᵥ w i = c i)
    (hoff : ∀ i j, i ≠ j → v i ⬝ᵥ w j = 0) :
    LinearIndependent R v := by
  rw [linearIndependent_iff']
  intro s g hg j hj
  -- pairing the relation with `w j` kills every term but the `j`-th, leaving `g j * c j = 0`
  have hpair := congrArg (· ⬝ᵥ w j) hg
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at hpair
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hoff i j hij, mul_zero])
      (fun hns => absurd hj hns), hdiag] at hpair
  exact (hc j) (hpair.trans (zero_mul _).symm)

end TauCeti

/-! ### The contragredient of a linear equivalence for the dot product -/

namespace LinearEquiv

open Matrix

variable {R ι κ μ : Type*} [CommSemiring R] [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

/-- The contragredient of a linear equivalence `f : (ι → R) ≃ₗ[R] (κ → R)` for the dot product:
the linear equivalence `g` with `g y ⬝ᵥ f x = y ⬝ᵥ x` for all `x` and `y`
(`LinearEquiv.eq_dotProductContragredient_iff`). It is the dual map of `f.symm`, read through the
identifications `dotProductEquiv` of `ι → R` and `κ → R` with their duals, and its matrix is the
transpose of the matrix of `f.symm` (`LinearEquiv.toMatrix'_dotProductContragredient`). -/
def dotProductContragredient (f : (ι → R) ≃ₗ[R] (κ → R)) : (ι → R) ≃ₗ[R] (κ → R) :=
  (dotProductEquiv R ι).trans (f.symm.dualMap.trans (dotProductEquiv R κ).symm)

/-- The contragredient of `f` is adjoint, for the dot product, to the inverse of `f`. -/
@[simp]
theorem dotProductContragredient_apply_dotProduct (f : (ι → R) ≃ₗ[R] (κ → R)) (y : ι → R)
    (x : κ → R) : f.dotProductContragredient y ⬝ᵥ x = y ⬝ᵥ f.symm x := by
  have h := congr($((dotProductEquiv R κ).apply_symm_apply
    (f.symm.dualMap (dotProductEquiv R ι y))) x)
  simpa only [dotProductContragredient, trans_apply, dotProductEquiv_apply_apply,
    dualMap_apply] using h

/-- A linear equivalence and its contragredient preserve the dot product jointly. -/
theorem dotProductContragredient_apply_dotProduct_apply (f : (ι → R) ≃ₗ[R] (κ → R))
    (y x : ι → R) : f.dotProductContragredient y ⬝ᵥ f x = y ⬝ᵥ x := by
  rw [dotProductContragredient_apply_dotProduct, symm_apply_apply]

/-- A linear equivalence and its contragredient preserve the dot product jointly, with the
contragredient applied on the right. -/
@[simp]
theorem apply_dotProduct_dotProductContragredient_apply (f : (ι → R) ≃ₗ[R] (κ → R))
    (x y : ι → R) : f x ⬝ᵥ f.dotProductContragredient y = x ⬝ᵥ y := by
  rw [dotProduct_comm, dotProductContragredient_apply_dotProduct_apply, dotProduct_comm]

/-- The contragredient of `f` is the unique linear equivalence `g` with `g y ⬝ᵥ f x = y ⬝ᵥ x`. -/
theorem eq_dotProductContragredient_iff {f g : (ι → R) ≃ₗ[R] (κ → R)} :
    g = f.dotProductContragredient ↔ ∀ y x, g y ⬝ᵥ f x = y ⬝ᵥ x := by
  refine ⟨by rintro rfl; simp, fun h ↦ ext fun y ↦ dotProduct_eq _ _ fun x ↦ ?_⟩
  rw [← f.apply_symm_apply x, h, dotProductContragredient_apply_dotProduct_apply]

/-- The matrix of the contragredient of `f` is the transpose of the matrix of `f.symm`. -/
@[simp]
theorem toMatrix'_dotProductContragredient (f : (ι → R) ≃ₗ[R] (κ → R)) :
    LinearMap.toMatrix' (f.dotProductContragredient : (ι → R) →ₗ[R] (κ → R)) =
      (LinearMap.toMatrix' (f.symm : (κ → R) →ₗ[R] (ι → R)))ᵀ := by
  ext j i
  rw [LinearMap.toMatrix'_apply, transpose_apply, LinearMap.toMatrix'_apply, coe_coe, coe_coe,
    ← dotProduct_single_one (f.dotProductContragredient (Pi.single i 1)) j,
    dotProductContragredient_apply_dotProduct, single_one_dotProduct]

/-- The contragredient of the identity is the identity. -/
@[simp]
theorem dotProductContragredient_refl :
    (refl R (ι → R)).dotProductContragredient = refl R (ι → R) :=
  (eq_dotProductContragredient_iff.2 fun _ _ ↦ rfl).symm

/-- Taking the contragredient is compatible with composition: the contragredient of `f.trans g`
is the composite of the contragredients of `f` and `g`. -/
@[simp]
theorem dotProductContragredient_trans (f : (ι → R) ≃ₗ[R] (κ → R)) (g : (κ → R) ≃ₗ[R] (μ → R)) :
    (f.trans g).dotProductContragredient =
      f.dotProductContragredient.trans g.dotProductContragredient :=
  (eq_dotProductContragredient_iff.2 fun _ _ ↦ by simp).symm

/-- Taking the contragredient is compatible with inversion: the contragredient of `f.symm` is
the inverse of the contragredient of `f`. -/
@[simp]
theorem dotProductContragredient_symm (f : (ι → R) ≃ₗ[R] (κ → R)) :
    f.symm.dotProductContragredient = f.dotProductContragredient.symm := by
  refine (eq_dotProductContragredient_iff.2 fun y x ↦ ?_).symm
  obtain ⟨z, rfl⟩ := f.dotProductContragredient.surjective y
  rw [symm_apply_apply, dotProductContragredient_apply_dotProduct]

/-- Taking the contragredient is an involution. -/
@[simp]
theorem dotProductContragredient_dotProductContragredient (f : (ι → R) ≃ₗ[R] (κ → R)) :
    f.dotProductContragredient.dotProductContragredient = f :=
  (eq_dotProductContragredient_iff.2 fun _ _ ↦
    apply_dotProduct_dotProductContragredient_apply ..).symm

end LinearEquiv
