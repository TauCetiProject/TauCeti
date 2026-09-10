/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootBivectors

import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Root operators on the four-dimensional spinor model

For an isotropic summand with basis indexed by `Fin 2`, the spinor module has exterior basis
indexed by the four subsets of `Fin 2`. Its even half has coordinates `empty` and `{0, 1}`, while
its odd half has coordinates `{0}` and `{1}`. The two simple-root pairs of type `D2` act on these
two halves independently.

The exterior basis records its top wedge only up to the shuffle unit used by its construction.
`TauCeti.spinFourExteriorBasis` absorbs that unit once, so its top coordinate is literally the
ordered product of the two exterior generators. In this basis the positive and negative root
bivectors are literal matrix units: the chain root moves `{1}` to `{0}`, and the fork root moves
the vacuum to `{0, 1}`; the negative roots reverse those moves. Thus one root pair occupies the
odd block and the other occupies the even block.

These formulas isolate the two elementary `sl2` actions inside the spinor model. In particular,
adding scalar multiples of the root operators to the identity produces the elementary matrix
directions needed to identify the two half-spin factors.

## Main definitions and results

* `TauCeti.spinFourExteriorBasis`: the oriented exterior basis in isotropic rank two.
* `TauCeti.toMatrix_spinAction_typeDSimpleRootBivector_fin_two`: the two positive root matrices.
* `TauCeti.toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two`: the two negative root
  matrices.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

open CliffordAlgebra Module QuadraticMap

namespace TauCeti

universe u v

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The scalar unit that orients the top exterior-basis vector as the ordered product of the two
generators. All other exterior-basis vectors retain their original normalization. -/
private noncomputable def spinFourBasisUnit (s : Finset (Fin 2)) : Kˣ :=
  if s = {0, 1} then
    Units.map (Int.castRingHom K).toMonoidHom
      (TauCeti.ExteriorAlgebra.basisEraseSign (0 : Fin 2) {0, 1})
  else 1

/-- The exterior basis in isotropic rank two, oriented so that its top vector is
`ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)`.

The even half-spin coordinates are `empty` and `{0, 1}`; the odd half-spin coordinates are `{0}`
and `{1}`. -/
noncomputable def spinFourExteriorBasis (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) :
    Basis (Finset (Fin 2)) K (ExteriorAlgebra K P.W) :=
  b.ExteriorAlgebra.unitsSMul spinFourBasisUnit

/-- The vacuum vector in the oriented rank-two exterior basis. -/
@[simp]
theorem spinFourExteriorBasis_empty
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    spinFourExteriorBasis P b ∅ = 1 := by
  rw [spinFourExteriorBasis, Basis.unitsSMul_apply, spinFourBasisUnit,
    ite_eq_right (by decide), one_smul, ExteriorAlgebra.basis_apply]
  simp

/-- The first singleton vector in the oriented rank-two exterior basis. -/
@[simp]
theorem spinFourExteriorBasis_zero
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    spinFourExteriorBasis P b {0} = ExteriorAlgebra.ι K (b 0) := by
  rw [spinFourExteriorBasis, Basis.unitsSMul_apply, spinFourBasisUnit,
    ite_eq_right (by decide), one_smul, TauCeti.ExteriorAlgebra.basis_singleton]

/-- The second singleton vector in the oriented rank-two exterior basis. -/
@[simp]
theorem spinFourExteriorBasis_one
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    spinFourExteriorBasis P b {1} = ExteriorAlgebra.ι K (b 1) := by
  rw [spinFourExteriorBasis, Basis.unitsSMul_apply, spinFourBasisUnit,
    ite_eq_right (by decide), one_smul, TauCeti.ExteriorAlgebra.basis_singleton]

/-- The top vector in the oriented rank-two exterior basis is the ordered product of its two
generators. -/
@[simp]
theorem spinFourExteriorBasis_pair
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    spinFourExteriorBasis P b {0, 1} =
      ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1) := by
  rw [spinFourExteriorBasis, Basis.unitsSMul_apply, spinFourBasisUnit,
    ite_eq_left rfl]
  have h := TauCeti.ExteriorAlgebra.basis_singleton_mul_basis_erase b 0 {0, 1} (by simp)
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul K] at h
  rw [Units.smul_def, Units.coe_map]
  change ((TauCeti.ExteriorAlgebra.basisEraseSign (0 : Fin 2) {0, 1} : ℤ) : K) •
      b.ExteriorAlgebra {0, 1} = _
  rw [← h]
  have herase : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
  rw [herase, TauCeti.ExteriorAlgebra.basis_singleton,
    TauCeti.ExteriorAlgebra.basis_singleton]

private theorem finsetFinTwo_cases (s : Finset (Fin 2)) :
    s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {0, 1} := by
  fin_cases s <;> decide

private theorem toMatrix_spinAction_typeDSimpleRootBivector_fin_two_zero
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleRootBivector b (by omega) 0)) =
      Matrix.single {0} {1} 1 := by
  rw [P.typeDSimpleRootBivector_def, dite_eq_left (by decide)]
  apply (Matrix.toLinAlgEquiv (spinFourExteriorBasis P b)).injective
  rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  apply (spinFourExteriorBasis P b).ext
  intro s
  rw [toLinAlgEquiv_single_apply_basis]
  rcases finsetFinTwo_cases s with rfl | rfl | rfl | rfl <;>
    simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector,
      CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι, Finset.ext_iff]

private theorem toMatrix_spinAction_typeDSimpleRootBivector_fin_two_one
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleRootBivector b (by omega) 1)) =
      Matrix.single {0, 1} ∅ 1 := by
  rw [P.typeDSimpleRootBivector_def, dite_eq_right (by decide)]
  apply (Matrix.toLinAlgEquiv (spinFourExteriorBasis P b)).injective
  rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  apply (spinFourExteriorBasis P b).ext
  intro s
  rw [toLinAlgEquiv_single_apply_basis]
  have hswap : ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 0) =
      -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) :=
    eq_neg_of_add_eq_zero_left
      (ExteriorAlgebra.ι_add_mul_swap (R := K) (b 1) (b 0))
  have hleft : ExteriorAlgebra.ι K (b 0) *
      (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) = 0 := by
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  have hpair : ExteriorAlgebra.ι K (b 0) *
      (ExteriorAlgebra.ι K (b 1) *
        (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1))) = 0 := by
    rw [← mul_assoc (ExteriorAlgebra.ι K (b 1)), hswap]
    simp only [neg_mul, mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, neg_zero]
  rcases finsetFinTwo_cases s with rfl | rfl | rfl | rfl <;>
    simp [map_mul, Module.End.mul_apply, Finset.ext_iff, hswap, hleft, hpair]

private theorem toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two_zero
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleNegativeRootBivector b (by omega) 0)) =
      Matrix.single {1} {0} 1 := by
  rw [P.typeDSimpleNegativeRootBivector_def, dite_eq_left (by decide)]
  apply (Matrix.toLinAlgEquiv (spinFourExteriorBasis P b)).injective
  rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  apply (spinFourExteriorBasis P b).ext
  intro s
  rw [toLinAlgEquiv_single_apply_basis]
  rcases finsetFinTwo_cases s with rfl | rfl | rfl | rfl <;>
    simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector,
      CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι, Finset.ext_iff]

private theorem toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two_one
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleNegativeRootBivector b (by omega) 1)) =
      Matrix.single ∅ {0, 1} 1 := by
  rw [P.typeDSimpleNegativeRootBivector_def, dite_eq_right (by decide)]
  apply (Matrix.toLinAlgEquiv (spinFourExteriorBasis P b)).injective
  rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  apply (spinFourExteriorBasis P b).ext
  intro s
  rw [toLinAlgEquiv_single_apply_basis]
  rcases finsetFinTwo_cases s with rfl | rfl | rfl | rfl <;>
    simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector,
      CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι, Finset.ext_iff]

/-- In the oriented rank-two exterior basis, the two positive type-`D` root bivectors are the
elementary matrices on the odd and even half-spin blocks, respectively. -/
theorem toMatrix_spinAction_typeDSimpleRootBivector_fin_two
    (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) (i : Fin 2) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleRootBivector b (by omega) i)) =
      if i = 0 then Matrix.single {0} {1} 1 else Matrix.single {0, 1} ∅ 1 := by
  fin_cases i
  · simpa using toMatrix_spinAction_typeDSimpleRootBivector_fin_two_zero P b
  · simpa using toMatrix_spinAction_typeDSimpleRootBivector_fin_two_one P b

/-- In the oriented rank-two exterior basis, the two negative type-`D` root bivectors are the
reverse elementary matrices on the odd and even half-spin blocks, respectively. -/
theorem toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two
    (P : SpinPolarizationData Q)
    (b : Basis (Fin 2) K P.W) (i : Fin 2) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleNegativeRootBivector b (by omega) i)) =
      if i = 0 then Matrix.single {1} {0} 1 else Matrix.single ∅ {0, 1} 1 := by
  fin_cases i
  · simpa using toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two_zero P b
  · simpa using toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two_one P b

end TauCeti
