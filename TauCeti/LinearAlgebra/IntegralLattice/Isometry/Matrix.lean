/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.Basic
import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# The matrix form of the isometry group of an integral lattice

Let `L` be an integral lattice with a finite carrier basis `b` and Gram matrix
`G = L.gramMatrix b`. The matrix in `b` of a self-isometry of `L` is an integral matrix `A` with
`Aᵀ * G * A = G`, that is, an element of the submonoid `Matrix.isometryMatrices G`. This file
shows that taking matrices identifies the isometry group `O(L)` with the group of units of that
submonoid, and uses it to compute the order of `O(L)` as a number of integral matrices.

* Taking matrices in `b` is a group isomorphism from `O(L)` onto the units of
  `Matrix.isometryMatrices G`. No hypothesis on `L` is needed for this: a unit of the submonoid
  is an integral matrix with an integral inverse, so it represents an automorphism of the carrier
  preserving the integral form.
* The determinant of the matrix of an isometry is its determinant `±1`, so the proper isometries
  `SO(L)` correspond to the solutions of `Aᵀ * G * A = G` of determinant `1`, and the
  correspondence restricts on `SO(L)` to `TauCeti.IntegralLattice.specialOrthogonalGroup.toMatrix`.
* When `L` is nondegenerate, `det G ≠ 0` need not be a unit, but `(det A) ^ 2 * det G = det G`
  forces `det A = ±1`, so every solution of `Aᵀ * G * A = G` is invertible in the submonoid.
  Hence `|O(L)|` is the number of integral solutions of `Aᵀ * G * A = G`, in every basis.
  Nondegeneracy cannot be dropped here: for `G = [0]` every integer solves `a * 0 * a = 0`,
  while the lattice presented by `[0]` has only the two isometries `±1`.
* A second basis `b'` conjugates the matrices by the change-of-basis matrices of `b` and `b'`.

## Main definitions

* `TauCeti.IntegralLattice.Isometry.toIsometryMatrices`: the matrix of a self-isometry in a
  finite carrier basis, as a monoid homomorphism into `Matrix.isometryMatrices (L.gramMatrix b)`.
* `TauCeti.IntegralLattice.Isometry.toUnitsIsometryMatrices`: the group isomorphism from `O(L)`
  onto the units of `Matrix.isometryMatrices (L.gramMatrix b)`.

## Main results

* `TauCeti.IntegralLattice.Isometry.det_coe_toIsometryMatrices`: the determinant of the matrix of
  an isometry is its determinant.
* `TauCeti.IntegralLattice.Isometry.coe_toIsometryMatrices_coe`: on `SO(L)` the matrix is the one
  given by `TauCeti.IntegralLattice.specialOrthogonalGroup.toMatrix`.
* `TauCeti.IntegralLattice.Isometry.coe_toIsometryMatrices_basis_change`: the matrices in two
  bases are conjugate by the change-of-basis matrices.
* `TauCeti.IntegralLattice.natCard_isometry_eq_natCard_isometryMatrices`: for a
  nondegenerate lattice, `|O(L)|` is the number of integral `A` with `Aᵀ * G * A = G`.
* `TauCeti.IntegralLattice.natCard_specialOrthogonalGroup_eq_natCard_isometryMatrices_det_eq_one`:
  `|SO(L)|` is the number of those solutions of determinant `1`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1
-/

public section

open Module Matrix

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Isometry

/-- The matrix of a self-isometry in a carrier basis `b` preserves the Gram matrix of `b`. -/
theorem toMatrix_carrierEquiv_mem_isometryMatrices (b : Basis ι ℤ L) (e : Isometry L L) :
    LinearMap.toMatrix b b (e.carrierEquiv : L →ₗ[ℤ] L) ∈ isometryMatrices (L.gramMatrix b) :=
  mem_isometryMatrices.mpr (L.gramMatrix_eq_transpose_mul_gramMatrix_mul _
    (fun x y ↦ (e.carrierEquiv_map_integralForm x y).symm) b b).symm

/-- The matrix of a self-isometry in a finite carrier basis `b`, as a monoid homomorphism from
`O(L)` into the submonoid of integral matrices preserving the Gram matrix of `b`. -/
noncomputable def toIsometryMatrices (b : Basis ι ℤ L) :
    Isometry L L →* isometryMatrices (L.gramMatrix b) where
  toFun e := ⟨LinearMap.toMatrix b b e.carrierEquiv, toMatrix_carrierEquiv_mem_isometryMatrices b e⟩
  map_one' := Subtype.ext <| by
    dsimp only
    rw [Submonoid.coe_one, ← carrierEquivHom_apply, map_one, LinearEquiv.one_eq_refl,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id]
  map_mul' e f := Subtype.ext <| by
    dsimp only
    rw [Submonoid.coe_mul, ← LinearMap.toMatrix_mul, ← carrierEquivHom_apply, map_mul,
      LinearEquiv.coe_toLinearMap_mul, carrierEquivHom_apply, carrierEquivHom_apply]

@[simp]
theorem coe_toIsometryMatrices_apply (b : Basis ι ℤ L) (e : Isometry L L) :
    (toIsometryMatrices b e : Matrix ι ι ℤ) = LinearMap.toMatrix b b e.carrierEquiv := (rfl)

/-- A self-isometry is determined by its matrix in a finite carrier basis. -/
theorem toIsometryMatrices_injective (b : Basis ι ℤ L) :
    Function.Injective (toIsometryMatrices b) := fun _ _ h ↦
  carrierEquiv_injective <| LinearEquiv.toLinearMap_injective <|
    (LinearMap.toMatrix b b).injective (congrArg Subtype.val h)

/-- The determinant of the matrix of a self-isometry is the determinant of the isometry. -/
theorem det_coe_toIsometryMatrices (b : Basis ι ℤ L) (e : Isometry L L) :
    (toIsometryMatrices b e : Matrix ι ι ℤ).det = (det L e : ℤ) := by
  rw [coe_toIsometryMatrices_apply, LinearMap.det_toMatrix, coe_det]

/-- A self-isometry is proper exactly when its matrix in a finite carrier basis has
determinant `1`. -/
theorem mem_specialOrthogonalGroup_iff_det_toIsometryMatrices (b : Basis ι ℤ L)
    {e : Isometry L L} :
    e ∈ specialOrthogonalGroup L ↔ (toIsometryMatrices b e : Matrix ι ι ℤ).det = 1 := by
  rw [mem_specialOrthogonalGroup_iff, det_coe_toIsometryMatrices, Units.val_eq_one]

/-- On a proper isometry, the matrix of `toIsometryMatrices` is the matrix given by
`TauCeti.IntegralLattice.specialOrthogonalGroup.toMatrix`. -/
theorem coe_toIsometryMatrices_coe (b : Basis ι ℤ L) (g : specialOrthogonalGroup L) :
    (toIsometryMatrices b (g : Isometry L L) : Matrix ι ι ℤ) =
      (specialOrthogonalGroup.toMatrix b g : Matrix ι ι ℤ) := by
  rw [coe_toIsometryMatrices_apply, specialOrthogonalGroup.coe_toMatrix_apply]

/-- **Change of basis.** The matrices of a self-isometry in two finite carrier bases `b` and `b'`
are conjugate by the change-of-basis matrices between them. -/
theorem coe_toIsometryMatrices_basis_change {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℤ L) (b' : Basis κ ℤ L) (e : Isometry L L) :
    (toIsometryMatrices b' e : Matrix κ κ ℤ) =
      b'.toMatrix b * (toIsometryMatrices b e : Matrix ι ι ℤ) * b.toMatrix b' := by
  rw [coe_toIsometryMatrices_apply, coe_toIsometryMatrices_apply,
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]

/-- The determinant of a unit of the submonoid of matrices preserving a Gram matrix is a unit. -/
private theorem isUnit_det_coe_units (b : Basis ι ℤ L)
    (u : (isometryMatrices (L.gramMatrix b))ˣ) :
    IsUnit ((u : isometryMatrices (L.gramMatrix b)) : Matrix ι ι ℤ).det :=
  isUnit_isometryMatrices_iff.mp u.isUnit

/-- The automorphism of the carrier represented in a basis `b` by a matrix of unit determinant
preserving the Gram matrix of `b` preserves the integral form. -/
private theorem integralForm_toLinearEquiv (b : Basis ι ℤ L) {X : Matrix ι ι ℤ}
    (hX : X ∈ isometryMatrices (L.gramMatrix b)) (hdet : IsUnit X.det) (x y : L) :
    L.integralForm (Matrix.toLinearEquiv b X hdet x) (Matrix.toLinearEquiv b X hdet y) =
      L.integralForm x y := by
  rw [gramMatrix_eq_toMatrix] at hX
  rw [Matrix.toLinearEquiv_apply, Matrix.toLinearEquiv_apply]
  exact BilinForm.isIsometry_iff.mp
    ((BilinForm.isIsometry_toLin_iff_mem_isometryMatrices b).mpr hX) x y

/-- **The matrix form of the isometry group.** Taking matrices in a finite carrier basis `b` is
a group isomorphism from `O(L)` onto the group of units of the submonoid of integral matrices
`A` with `Aᵀ * G * A = G`, for `G` the Gram matrix of `b`. The inverse sends a unit to the
isometry acting on the carrier by the matrix in `b`. -/
noncomputable def toUnitsIsometryMatrices (b : Basis ι ℤ L) :
    Isometry L L ≃* (isometryMatrices (L.gramMatrix b))ˣ where
  toFun := (toIsometryMatrices b).toHomUnits
  invFun u := ofCarrierEquiv (Matrix.toLinearEquiv b _ (isUnit_det_coe_units b u))
    (integralForm_toLinearEquiv b (u : isometryMatrices (L.gramMatrix b)).property _)
  left_inv e := carrierEquiv_injective <| LinearEquiv.ext fun x ↦ by
    rw [carrierEquiv_ofCarrierEquiv, Matrix.toLinearEquiv_apply, MonoidHom.coe_toHomUnits,
      coe_toIsometryMatrices_apply, Matrix.toLin_toMatrix, LinearEquiv.coe_coe]
  right_inv u := Units.ext <| Subtype.ext <| by
    rw [MonoidHom.coe_toHomUnits, coe_toIsometryMatrices_apply, carrierEquiv_ofCarrierEquiv]
    exact (congrArg (LinearMap.toMatrix b b)
      (LinearMap.ext (Matrix.toLinearEquiv_apply b _ _))).trans (LinearMap.toMatrix_toLin b b _)
  map_mul' := map_mul _

@[simp]
theorem coe_toUnitsIsometryMatrices_apply (b : Basis ι ℤ L) (e : Isometry L L) :
    (toUnitsIsometryMatrices b e : isometryMatrices (L.gramMatrix b)) = toIsometryMatrices b e :=
  (rfl)

/-- The isometry attached to a unit `u` by the inverse of `toUnitsIsometryMatrices` acts on the
carrier by the matrix of `u` in `b`. -/
@[simp]
theorem coe_carrierEquiv_toUnitsIsometryMatrices_symm_apply (b : Basis ι ℤ L)
    (u : (isometryMatrices (L.gramMatrix b))ˣ) :
    (((toUnitsIsometryMatrices b).symm u).carrierEquiv : L →ₗ[ℤ] L) =
      Matrix.toLin b b (u : Matrix ι ι ℤ) :=
  LinearMap.ext fun x ↦ by
    rw [LinearEquiv.coe_coe, toUnitsIsometryMatrices, MulEquiv.symm_mk, MulEquiv.coe_mk,
      Equiv.coe_fn_symm_mk, carrierEquiv_ofCarrierEquiv, Matrix.toLinearEquiv_apply]

/-- Every matrix of unit determinant preserving the Gram matrix of `b` is the matrix of a
self-isometry. -/
theorem exists_toIsometryMatrices_eq (b : Basis ι ℤ L) {X : isometryMatrices (L.gramMatrix b)}
    (hX : IsUnit (X : Matrix ι ι ℤ).det) : ∃ e, toIsometryMatrices b e = X :=
  ⟨(toUnitsIsometryMatrices b).symm (isUnit_isometryMatrices_iff.mpr hX).unit,
    congrArg Units.val ((toUnitsIsometryMatrices b).apply_symm_apply _)⟩

end Isometry

/-- **The order of the isometry group of a nondegenerate lattice is a number of integral
matrices.** For a finite carrier basis `b` with Gram matrix `G`, `|O(L)|` is the number of
integral matrices `A` with `Aᵀ * G * A = G`: although `det G` need not be `±1`, every such `A`
has determinant `±1`. -/
theorem natCard_isometry_eq_natCard_isometryMatrices [L.IsNondegenerate] (b : Basis ι ℤ L) :
    Nat.card (Isometry L L) = Nat.card (isometryMatrices (L.gramMatrix b)) := by
  have hdet : (L.gramMatrix b).det ≠ 0 := by
    rw [← gramDet_def, gramDet_ne_zero_iff]
    exact IsNondegenerate.nondegenerate
  rw [Nat.card_congr (Isometry.toUnitsIsometryMatrices b).toEquiv,
    natCard_units_isometryMatrices (IsRegular.of_ne_zero hdet)]

/-- **The order of the special isometry group is a number of integral matrices.** For a finite
carrier basis `b` with Gram matrix `G`, `|SO(L)|` is the number of integral matrices `A` of
determinant `1` with `Aᵀ * G * A = G`. No nondegeneracy is needed, since such an `A` is
invertible. -/
theorem natCard_specialOrthogonalGroup_eq_natCard_isometryMatrices_det_eq_one (b : Basis ι ℤ L) :
    Nat.card (specialOrthogonalGroup L) =
      Nat.card {X : Matrix ι ι ℤ // X ∈ isometryMatrices (L.gramMatrix b) ∧ X.det = 1} := by
  refine Nat.card_congr <| Equiv.ofBijective
    (fun g ↦ ⟨Isometry.toIsometryMatrices b g, (Isometry.toIsometryMatrices b g).property,
      (Isometry.mem_specialOrthogonalGroup_iff_det_toIsometryMatrices b).mp g.property⟩) ⟨?_, ?_⟩
  · intro g h hgh
    have hgh' := congrArg Subtype.val hgh
    dsimp only at hgh'
    exact Subtype.ext (Isometry.toIsometryMatrices_injective b (Subtype.ext hgh'))
  · rintro ⟨X, hX, hdet⟩
    obtain ⟨e, he⟩ := Isometry.exists_toIsometryMatrices_eq b (X := ⟨X, hX⟩)
      (by rw [hdet]; exact isUnit_one)
    have he' : (Isometry.toIsometryMatrices b e : Matrix ι ι ℤ) = X := Subtype.ext_iff.mp he
    refine ⟨⟨e, (Isometry.mem_specialOrthogonalGroup_iff_det_toIsometryMatrices b).mpr ?_⟩,
      Subtype.ext he'⟩
    rw [he', hdet]

end TauCeti.IntegralLattice
