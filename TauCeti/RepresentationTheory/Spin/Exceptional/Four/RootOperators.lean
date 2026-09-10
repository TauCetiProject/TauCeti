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
  calc
    _ = b.ExteriorAlgebra {0} * b.ExteriorAlgebra (({0, 1} : Finset (Fin 2)).erase 0) :=
      h.symm
    _ = _ := by
      have herase : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
      rw [herase, TauCeti.ExteriorAlgebra.basis_singleton,
        TauCeti.ExteriorAlgebra.basis_singleton]

private theorem finsetFinTwo_cases (s : Finset (Fin 2)) :
    s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {0, 1} := by
  fin_cases s <;> decide

private theorem orderedPair_eq_smul_exteriorBasis
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1) =
      ((TauCeti.ExteriorAlgebra.basisEraseSign (0 : Fin 2) {0, 1} : ℤ) : K) •
        b.ExteriorAlgebra {0, 1} := by
  have h := TauCeti.ExteriorAlgebra.basis_singleton_mul_basis_erase b 0 {0, 1} (by simp)
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul K] at h
  have herase : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
  simpa [herase] using h

private theorem toMatrix_spinAction_typeDSimpleRootBivector_fin_two_zero
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleRootBivector b (by omega) 0)) =
      Matrix.single {0} {1} 1 := by
  rw [P.typeDSimpleRootBivector_def, dite_eq_left (by decide)]
  apply toMatrixAlgEquiv_eq_single_of_apply_basis
  intro s
  rcases finsetFinTwo_cases s with rfl | rfl | rfl | rfl
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector, Finset.ext_iff]
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector, Finset.ext_iff]
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector]
  · rw [spinFourExteriorBasis_pair, orderedPair_eq_smul_exteriorBasis P b]
    simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector,
      TauCeti.ExteriorAlgebra.ι_mul_basis,
      TauCeti.ExteriorAlgebra.contractLeft_coord_basis, Finset.ext_iff]

private theorem toMatrix_spinAction_typeDSimpleRootBivector_fin_two_one
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleRootBivector b (by omega) 1)) =
      Matrix.single {0, 1} ∅ 1 := by
  rw [P.typeDSimpleRootBivector_def, dite_eq_right (by decide)]
  apply toMatrixAlgEquiv_eq_single_of_apply_basis
  intro s
  rcases finsetFinTwo_cases s with rfl | rfl | rfl | rfl
  · simp [map_mul, Module.End.mul_apply]
  · rw [spinFourExteriorBasis_zero, ← TauCeti.ExteriorAlgebra.basis_singleton]
    rw [map_mul, Module.End.mul_apply, spinAction_ι_wedge, spinAction_ι_wedge,
      TauCeti.ExteriorAlgebra.ι_mul_basis, ite_eq_right (by simp), mul_smul_comm,
      TauCeti.ExteriorAlgebra.ι_mul_basis, ite_eq_left (by simp), smul_zero]
    simp
  · rw [spinFourExteriorBasis_one, ← TauCeti.ExteriorAlgebra.basis_singleton]
    rw [map_mul, Module.End.mul_apply, spinAction_ι_wedge, spinAction_ι_wedge,
      TauCeti.ExteriorAlgebra.ι_mul_basis, ite_eq_left (by simp), mul_zero]
    simp
  · rw [spinFourExteriorBasis_pair, orderedPair_eq_smul_exteriorBasis P b]
    simp [map_mul, Module.End.mul_apply,
      TauCeti.ExteriorAlgebra.ι_mul_basis, Finset.ext_iff]

private theorem toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two_zero
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleNegativeRootBivector b (by omega) 0)) =
      Matrix.single {1} {0} 1 := by
  rw [P.typeDSimpleNegativeRootBivector_def, dite_eq_left (by decide)]
  apply toMatrixAlgEquiv_eq_single_of_apply_basis
  intro s
  rcases finsetFinTwo_cases s with rfl | rfl | rfl | rfl
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector, Finset.ext_iff]
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector]
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector]
  · rw [spinFourExteriorBasis_pair, orderedPair_eq_smul_exteriorBasis P b]
    simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector,
      TauCeti.ExteriorAlgebra.contractLeft_coord_basis, Finset.ext_iff]

private theorem toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two_one
    (P : SpinPolarizationData Q) (b : Basis (Fin 2) K P.W) :
    LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b)
        (spinAction Q P (P.typeDSimpleNegativeRootBivector b (by omega) 1)) =
      Matrix.single ∅ {0, 1} 1 := by
  rw [P.typeDSimpleNegativeRootBivector_def, dite_eq_right (by decide)]
  apply toMatrixAlgEquiv_eq_single_of_apply_basis
  intro s
  rcases finsetFinTwo_cases s with rfl | rfl | rfl | rfl
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector, Finset.ext_iff]
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector, Finset.ext_iff]
  · simp [map_mul, Module.End.mul_apply, P.pairingEquiv_dualVector, Finset.ext_iff]
  · rw [spinFourExteriorBasis_pair, orderedPair_eq_smul_exteriorBasis P b]
    simp only [Nat.add_one_sub_one, Fin.mk_one, Fin.isValue, tsub_self, Fin.zero_eta,
      map_mul, spinAction_ι, SpinPolarizationData.cliffordOperator_coe_W', map_smul,
      Module.End.mul_apply, SpinPolarizationData.contract_apply,
      SpinPolarizationData.pairingEquiv_dualVector,
      TauCeti.ExteriorAlgebra.contractLeft_coord_basis, Finset.mem_insert,
      Finset.mem_singleton, zero_ne_one, or_false, ↓reduceIte, Finset.erase_insert_eq_erase,
      not_false_eq_true, Finset.erase_eq_of_notMem, TauCeti.ExteriorAlgebra.basis_singleton,
      map_zsmul_unit, CliffordAlgebra.contractLeft_ι, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same, map_one, spinFourExteriorBasis_empty, one_smul]
    obtain h | h := Int.units_eq_one_or
      (TauCeti.ExteriorAlgebra.basisEraseSign (0 : Fin 2) {0, 1})
    · simp [h]
    · simp [h]

/-- In the oriented rank-two exterior basis, the two positive type-`D` root bivectors are the
elementary matrices on the odd and even half-spin blocks, respectively. -/
@[simp]
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
@[simp]
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
